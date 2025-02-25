#include "vm.h"
#include "scmmath.h"

using namespace Scheme;

void RefObject::finz(VM* vm)
{
  if (marked & (1 << WEAKTAG))
    vm->rmWeak(this);

  int size = this->getsize();
  this->~RefObject();

  vm->free(this, size);
}

void RefObject::curmark(VM* vm)
{
  this->gcmark(ObjGroup(vm)->curbit());
}

bool RefObject::iscurmark(VM* vm)
{
  return isgcmark(ObjGroup(vm)->curbit());
}

void PairObj::finz(VM* vm)
{
  CachePair(vm)->addref(this);
}

GCVar::GCVar(VM* v)
  :vm(v)
{
  object = Stk(vm)->alloc(&hori, &vert);
}

GCVar::~GCVar()
{
  Stk(vm)->freez(hori, vert);
}

#define SweepListNext(gclist, objgroup, gc, delpost)  \
{ RefPtr* lst = &(gclist);                            \
  while (*lst != NULL) {                              \
    if ((*lst)->isgcmark(objgroup->curbit()))         \
      lst = &(*lst)->gcnxt;                           \
    else {                                            \
      RefPtr item = *lst; *lst = (*lst)->gcnxt;       \
      (gc)->toDel(item);  delpost ;                   \
    }}                                                \
}                                                     \

void RefObjGroup::fullsweep()
{
  // firstly iterate current gclst
  // then other gclst
  SweepListNext(gclst[curIdx], ObjGroup(vm), GC(vm), );

  // move marked refs to cur gclst
  RefPtr* lst = &gclst[othIdx];
  while (*lst != NULL)
  {
    RefPtr item = *lst;
    lst = &(*lst)->gcnxt;

    GC(vm)->toDelOrMark(item);
  }
}

bool RefObjGroup::stepsweep()
{
  for(int i = 0; i < 10 && gclst[othIdx] != NULL; i++)
  {
    RefPtr item = gclst[othIdx];
    gclst[othIdx] = gclst[othIdx]->gcnxt;

    GC(vm)->toDelOrMark(item);
  }

  return gclst[othIdx] != NULL;
}

void StackFrame::mark(VM* vm)
{
  for (int j = 0; j < etyidx; j++)
    Check(&vars[j]);
}

void StackMatrix::freez(int h, int v)
{
  stkvars[h]->freez(v);

  int last = stkvars.size() - 1;
  if (stkvars[last]->empty() &&
      last - 1 >= 0 && stkvars[last-1]->empty())
  {
    vm->free(stkvars[last], sizeof(StackFrame));
    stkvars[last] = NULL;

    stkvars.erase(--(stkvars.end()));
  }
}

ValueT* StackMatrix::alloc(int* h, int* v)
{
  if (stkvars.size() == 0)
    stkvars.push_back(new (vm->alloc(sizeof(StackFrame))) StackFrame());

  StackFrame* pG = stkvars[stkvars.size() - 1];

  ValueT* val = pG->alloc(v);
  if (val != NULL)
  {
    *h = stkvars.size() - 1;
    return val;
  }

  else
    stkvars.push_back(new (vm->alloc(sizeof(StackFrame))) StackFrame());

  pG = stkvars[stkvars.size() - 1];
  val = pG->alloc(v);

  *h = stkvars.size() - 1;
  return val;
}

bool StackMatrix::stepmark()
{
  int i = stkidx;
  if (i < stkvars.size())
  {
    stkidx++;

    StackFrame* frm = stkvars[i];
    if (NULL != frm && !frm->empty())
    {
      frm->mark(vm);
      return true;
    }
  }

  return false;
}

void StackMatrix::fullmark()
{
  for (int i = 0; i < stkvars.size(); i++)
  {
    StackFrame* frm = stkvars[i];
    if (NULL == frm || frm->empty())
      continue;

    frm->mark(vm);
  }
}

void CachePairObj::addref(PairPtr ref)
{
  ref->car(Snullref);
  ref->cdr(Snullref);

  // TODO: check capacity to release some caches
  ref->link(cache);
  cache = ref;
}

PairPtr CachePairObj::getone()
{
  PairPtr item = cache;
  if (cache != NULL)
    cache = (PairPtr)cache->gcnxt;
  return item;
}

void CachePairObj::fullsweep()
{
  while (cache != NULL)
  {
    PairPtr p = cache;
    cache = (PairPtr)cache->gcnxt;
    p->RefObject::finz(vm);
  }
}

void SGC::toDel(RefPtr ref)
{
  ref->finz(vm);
}

void SGC::startstep()
{
  Assert(state == GCSNone, "internal error %d", state);

  Assert(graylstLast == NULL, "internal error graylstlast not null");
  Assert(graylst == NULL, "internal error graylst not null");

  state = GCSNone + 1;

  Stk(vm)->startstep();
  Intern(vm)->startstep();

  ftouchptr = &SGC::addgraylst;
}

bool SGC::markgray()
{
  for (int i = 0; i < 10; i++)
  {
    if (graylst == NULL) return false;

    PairPtr pair = graylst;
    graylst = (PairPtr)graylst->gcnxt;
    if (graylst == NULL) graylstLast = NULL;

    // must be refval
    Assert(pair->car()->isref(), "internal error gray lst car not ref");
//    Assert(pair->cdr()->isref(), "internal error gray lst cdr not ref");

    pair->car()->ref()->visit(vm);
    if (!pair->cdr()->isnull())
      pair->cdr()->ref()->visit(vm);

    CachePair(vm)->addref(pair);
  }

  return true;
}

void SGC::addgraylst(RefPtr ref)
{
  ValueT vt;
  setref(&vt, ref);

  if (graylst == NULL)
  {
    PairPtr pair = vm->getonepairnor();

    graylst = graylstLast = pair;

    graylstLast->car(&vt);
  }
  else
  {
    if (graylstLast->cdr()->isnull())
      graylstLast->cdr(&vt);

    else
    {
      PairPtr pair = vm->getonepairnor();

      graylstLast->gcnxt = pair;
      graylstLast = pair;

      pair->car(&vt);
    }
  }
}

void SGC::singlestep()
{
  switch(state) {
  case GCSMarkStk:
    if (!Stk(vm)->stepmark())
      state = state + 1;
    break;
  case GCSMarkReg:
    vm->stepmarkregs();
    state = state + 1;
    break;
  case GCSMarkFrame:
    vm->stepmarkframes();
    state = state + 1;
    break;
  case GCSMarkGray:
    if (!markgray())
      state = state + 1;
    break;
  case GCSSweepObjGroup:
    if (!ObjGroup(vm)->stepsweep())
      state = state + 1;
    break;
  case GCSSweepInterns:
    if (!Intern(vm)->stepsweep())
      state = state + 1;
    break;
  case GCSSweepEnd:
    Intern(vm)->checkResize();
    state = state + 1;
    break;
  case GCSEnd:
    state = GCSNone;
    break;
  default:
    Error("unknown state %d", state);
    break;
  }
}

void SGC::sweepgray()
{
  while (graylst != NULL)
  {
    PairPtr pair = graylst;
    graylst = (PairPtr)graylst->gcnxt;

    toDelOrMark(pair->car()->ref());

    if (!pair->cdr()->isnull())
      toDelOrMark(pair->cdr()->ref());

    this->toDel(pair);
  }

  graylst = graylstLast = NULL;
}

void SGC::fullgc()
{
  ftouchptr = &SGC::touchchild;

  // set fullgc mark
  ObjGroup(vm)->setfullgcmask();

  // stage mark start
  Stk(vm)->fullmark();

  // mark the regs and regframes
  vm->regfullmark();
  // stage mark end

  // stage sweep start
  // free cached pair mem
  CachePair(vm)->fullsweep();

  // remove gc from curgclst
  // move visited refs to curgclst
  ObjGroup(vm)->fullsweep();

  // collect pair refs from graylst
  sweepgray();

  // collect symbols
  Intern(vm)->fullsweep();

  clearDel();

  // stage sweep end

  // unset the fullgc mark
  ObjGroup(vm)->unsetfullgcmask();

  // reset to incremental gc
  ftouchptr = &SGC::addgraylst;

  // ignore previous state
  state = GCSNone;
}

void SGC::clearDel()
{
  while (toDelLst != NULL)
  {
    RefPtr item = toDelLst;
    toDelLst = toDelLst->gcnxt;

    // default behaviour
    // delete this
    item->finz(vm);
  }
}

void SGC::stepfullgc()
{
  startstep();

  while (state != GCSNone)
    singlestep();
}

void SGC::checkTrace(RefPtr ptr)
{
  if (ptr && !ptr->iscurmark(vm))
  {
    ptr->curmark(vm);

    (this->*ftouchptr)(ptr);
  }
}

void SGC::toDelOrMark(RefPtr ref)
{
  if (ref->isgcmark(ObjGroup(vm)->curbit()))
    ObjGroup(vm)->addrefcur(ref);

  else
    this->toDel(ref);
}

void SGC::checkBarrier(RefPtr ptr)
{
  if (state != GCSNone && ptr->iscurmark(vm))
    checkTrace(ptr);
}

bool Interns::stepsweep()
{
  int i = bidx;
  if (i < blistlen)
  {
    bidx++;
    if (bucketlist[i] != NULL)
    {
      RefPtr bklst = bucketlist[i];
      SweepListNext(bklst, ObjGroup(vm), GC(vm), bcount--);
    }

    return true;
  }

  return false;
}

void Interns::fullsweep()
{
  for (int i = 0; i < blistlen; i++)
  {
    RefPtr bklst = bucketlist[i];
    SweepListNext(bklst, ObjGroup(vm), GC(vm), bcount--);
  }
}

void Interns::rehash(int oldl, int newl)
{
  for (int i = 0; i < oldl; i++)
  {
    RefPtr b = bucketlist[i], bnext = NULL;
    bucketlist[i] = NULL;

    for (; b != NULL; b = bnext)
    {
      bnext = b->gcnxt;

      int idx = objstrh((SymPtr)b) % newl;
      b->gcnxt = bucketlist[idx];
      bucketlist[idx] = (SymPtr)b;
    }
  }
}

void Interns::checkResize()
{
  if (bcount >= blistlen)
  {
    // grow
    int newl = blistlen * 2;
    while (bcount >= blistlen) newl *= 2;

    bucketlist = (SymPtr*)vm->realloc(bucketlist, blistlen, sizeof(SymPtr) * newl);

    rehash(blistlen, newl);

    blistlen = newl;
  }
  else if (bcount < blistlen / 4 && blistlen > INIT_LEN)
  {
    // shrink
    int newl = blistlen / 2;
    while (bcount < newl / 4) newl /= 2;
    newl = std::max(newl, INIT_LEN);

    rehash(blistlen, newl);

    bucketlist = (SymPtr*)vm->realloc(bucketlist, blistlen, sizeof(SymPtr) * newl);

    blistlen = newl;
  }
}

SymPtr Interns::intern(const char* str, int n)
{
  SymPtr b = (SymPtr)Const(vm)->getconst(str);
  if (b != NULL) return b;

  uint h = Util::hash(str, n, vm->seed);
  int idx = h % blistlen;
  b = bucketlist[idx];
  while (b != NULL)
  {
    if (objstrl(b) == n && memcmp(objstr(b), str, n * sizeof(char)) == 0)
    {
      b->gcmark(ObjGroup(vm)->curbit());

      return b;
    }

    b = (SymPtr)b->gcnxt;
  }

  SymPtr sym = vm->newstr(str, n, h);

  sym->gcnxt = bucketlist[idx];
  b = bucketlist[idx] = sym;

  b->gcmark(ObjGroup(vm)->curbit());

  bcount++;

  return sym;
}

void Interns::init()
{
  bucketlist = (SymPtr*)vm->alloc(sizeof(SymPtr) * INIT_LEN);
  blistlen = INIT_LEN;
  bcount = 0;
}

Interns::~Interns()
{
  if (bucketlist)
    vm->free(bucketlist, sizeof(SymPtr) * blistlen);

  bucketlist = NULL;
  blistlen = 0;
}

Interns::Interns(VM* v):
  vm(v), bidx(0), bucketlist(0), blistlen(0), bcount(0)
{
}

ValueT ConstVal::linknext(VT_LINK_NEXT);
ValueT ConstVal::linkreturn(VT_LINK_RETURN);

ValueT ConstVal::snull;
ValueT ConstVal::sundefined(VT_UNDEFINED);
ValueT ConstVal::strue(VT_TRUE);
ValueT ConstVal::sfalse(VT_FALSE);

#define InitConstSym(A, B) setsym(&A, initConstSym(ConstTKs[B]))

static const char*const ConstTKs[] = {
  "quote",
  "quasiquote",
  "unquote",
  "unquote-splicing",
  "define",
  "set!",
  "begin",
  "lambda",
  "if",
  "cond",
  "else",
  "let",
  "syntax-rules",
  "..."
};

void ConstVal::init()
{
  InitConstSym(quote, CTK_QUOTE);
  InitConstSym(qquote, CTK_QQUOTE);
  InitConstSym(uquote, CTK_UQUOTE);
  InitConstSym(uquotes, CTK_UQUOTES);
  InitConstSym(define, CTK_DEFINE);
  InitConstSym(sset, CTK_SET);
  InitConstSym(begin, CTK_BEGIN);
  InitConstSym(lambda, CTK_LAMBDA);
  InitConstSym(sif, CTK_IF);
  InitConstSym(cond, CTK_COND);
  InitConstSym(selse, CTK_ELSE);
  InitConstSym(let, CTK_LET);
  InitConstSym(synrules, CTK_SYNRULES);
  InitConstSym(ellip, CTK_ELLIP);
}

RefPtr ConstVal::initConstSym(const char* str)
{
  int n = strlen(str);

  SymPtr ptr = vm->newstr(str, n, Util::hash(str, n, vm->seed));

  int idx = objstrh(ptr) % CTK_MAX;
  constlst[idx] = (SymPtr)ptr->link(constlst[idx]);

  return ptr;
}

RefPtr ConstVal::getconst(const char* str, int n)
{
  SymPtr ptr = (SymPtr)constlst[Util::hash(str, n, vm->seed) % CTK_MAX];
  while (ptr != NULL)
  {
    if (objstrl(ptr) == n && memcmp(objstr(ptr), str, n) == 0)
      return ptr;

    ptr = (SymPtr)ptr->gcnxt;
  }
  return NULL;
}

InstPtr Instruction::preserving(int regs, InstPtr i2)
{
  if (regs == rvEmpty)
  {
    append(i2);
    return this;
  }

  else
  {

    int sr = rvEmpty;
    for (int i = 0; i < rMax; i++)
    {
      int r = regv(i);
      if ((regs&r) && (i2->rneed&r) && (rmod&r))
        sr |= r;
    }

    rneed |= sr;
    rmod ^= sr;

    if (sr > 0)
      saverestore(sr);

    append(i2);
    return this;
  }
}

void Instruction::label(ValueT* label)
{
  ValueT exprv;
  setpair(&exprv, expr);

  PairPtr pair = Sconsref(label, &exprv);
  setexpr(pair);
}

InstPtr Instruction::labelend(ValueT* label)
{
  PairPtr end = vm->list(label);
  Sgcreserve(end);

  endwithpair(end);

  return this;
}

InstPtr Instruction::append(InstPtr ptr)
{
  rneed |= (ptr->rneed & (ptr->rneed ^ rmod));
  rmod |= ptr->rmod;

  endwithpair(ptr->expr);
  return this;
}

InstPtr Instruction::parallel(InstPtr ptr)
{
  rneed |= ptr->rneed;
  rmod |= ptr->rmod;

  endwithpair(ptr->expr);

  return this;
}

InstPtr Instruction::tack(InstPtr ptr)
{
  endwithpair(ptr->expr);
  return this;
}

void Instruction::saverestore(int sr)
{
  Sreservevt(vrestore);

  *vrestore = Sr1(RestoreReg, sr);
  *vrestore = vm->list(vrestore);

  endwithpair(pairref(vrestore));

  Sreservevt(vsave);
  *vsave = Sr1(SaveReg, sr);

  ValueT exprv;
  setpair(&exprv, this->expr);

  setexpr(Sconsref(vsave, &exprv));
}

void Instruction::endwithpair(PairPtr p2)
{
  if (!expr)
    setexpr(p2);

  else
  {
    PairPtr p1 = expr;

    while (!p1->cdr()->isnull())
      p1 = Spairref(p1->cdr());

    ValueT p2p;
    setpair(&p2p, p2);

    p1->cdr(&p2p);
    GC(vm)->checkBarrier(p1);
  }
}

JumpToFix::~JumpToFix()
{
  if (arrToFix)
    vm->free(arrToFix, size * sizeof(PairPtr));

  arrToFix = NULL;
}

void JumpToFix::fix(int label, PairPtr jmp)
{
  int rng = label - startlabel;
  if (rng < size)
  {
    PairPtr pair = arrToFix[rng];
    while (pair)
    {
      FixJumpObj* ref = jumpobjref(pair->car());
      ref->fixJmp(label, jmp);
      GC(vm)->checkBarrier(pair->car()->ref());

      pair = pairref(pair->cdr());
    }
  }
}

void JumpToFix::toFix(int label, RefPtr p)
{
  if (size == 0)
  {
    size = 2;
    arrToFix = (PairPtr*)vm->alloc(size * sizeof(PairPtr));
    arrToFix[0] = NULL;
    arrToFix[1] = NULL;
  }

  int rng = label - startlabel;
  if (rng >= size)
  {
    int oldsize = size;
    do {
      size *= 2;
    } while (rng >= size);

    arrToFix = (PairPtr*)vm->realloc(arrToFix, oldsize * sizeof(PairPtr), size * sizeof(PairPtr));
    for (int i = oldsize; i < size; i++)
      arrToFix[i] = NULL;
  }

  ValueT fix;
  setpair(&fix, arrToFix[rng]);

  ValueT pv;
  setref(&pv, p);

  arrToFix[rng] = Sconsref(&pv, &fix);
}

void SCompiler::endwithlink(JumpToFix* jf, InstPtr inst, ValueT* link)
{
  Sinstvar(linki);

  compilelink(&linki, jf, link);

  inst->preserving(regv(rContinue), &linki);
}

void SCompiler::compilelink(InstPtr inst, JumpToFix* jf, ValueT* link)
{
  static JumpContinue jmpcontinue;

  if (isreturn(link))
  {
    ValueT vjump;
    setref(&vjump, &jmpcontinue);
    inst->set(regv(rContinue), rvEmpty, vm->list(&vjump));
  }

  else if (isnext(link))
    inst->set(rvEmpty, rvEmpty, NULL);

  // jump to a label
  else
  {
    Sreservevt(vjump);

    *vjump = Sr1(JumpLabel, link);
    jf->toFix(Slabeli(link), vjump->ref());

    setinst1v(inst, rvEmpty, rvEmpty, vjump);
  }
}

void SCompiler::compilesym(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, SymPtr sym, ValueT* link)
{
  Sreservevt(ref);

  int needr = regv(rEnv);

  if (vars)
  {
    int idx = vars->looklocal(sym);
    if (idx < 0)
    {
      idx = vars->lookovar(sym);
      if (idx < 0)
      {
        int depth = 0;
        idx = vars->lookouter(sym, &depth);

        if (idx < 0)
        {
          *ref = Sr2(RefGlobalVar, targetr, sym);
          needr = rvEmpty;
        }

        else
        {
          idx = vars->addovar(vm, depth, idx);
          *ref = Sr2(RefUpVar, targetr, idx);
        }
      }
      else
        *ref = Sr2(RefUpVar, targetr, idx);
    }

    else
      *ref = Sr2(RefLocalVar, targetr, idx);
  }
  else
  {
    *ref = Sr2(RefGlobalVar, targetr, sym);
    needr = rvEmpty;
  }

  setinst1v(inst, needr, regv(targetr), ref);

  endwithlink(jf, inst, link);
}

void SCompiler::makedef(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* val)
{
  Sreservevt(symval);

  PairPtr pair = Spairref(val);
  ValueT* symv = pair->car();

  SymPtr sym = NULL;

  // (define (a b c) ...)
  if (!issym(symv))
  {
    PairPtr symvpair = Spairref(symv);
    sym = Ssymref(symvpair->car());

    // (lambda (b c) ...)
    *symval = Sconsref(symvpair->cdr(), pair->cdr());
    *symval = Sconsref(Sklambda(), symval);
  }

  // (define a 2)
  else
  {
    sym = symref(symv);

    pair = Spairref(pair->cdr());
    *symval = pair->car();

    Assert(pair->cdr()->isnull(), "define bad form");
  }

  Sreservevt(vdef);

  int offset = -1;
  if (vars != NULL)
  {
    offset = vars->looklocal(sym);
    if (offset < 0)
      offset = vars->addlocal(vm, sym);

    *vdef = Sr1(DefLocalVar, offset);
  }
  else
    *vdef = Sr1(DefGlobalVar, sym);

  compile(inst, rVal, vars, jf, symval, Snext);

  //  vdef = Sr1(DefVar, offset);
  *vdef = vm->list(vdef);
  Sinstvar(definst);
  definst.set(regv(rEnv)|regv(rVal), regv(targetr), pairref(vdef));

  inst->preserving(regv(rEnv), &definst);
}

void SCompiler::makeset(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* val)
{
  Sreservevt(vset);

  PairPtr pair = Spairref(val);
  ValueT* symp = pair->car();

  SymPtr sym = Ssymref(symp);
  int offset = vars->looklocal(sym);
  if (offset < 0)
  {
    offset = vars->lookovar(sym);
    if (offset < 0)
    {
      int depth = -1;
      offset = vars->lookouter(sym, &depth);
      if (offset < 0)
        *vset = Sr2(SetVarGlobal, sym, targetr);

      else
      {
        offset = vars->addovar(vm, depth, offset);
        *vset = Sr2(SetVarUp, offset, targetr);
      }
    }
    else
      *vset = Sr2(SetVarUp, offset, targetr);
  }
  else
    *vset = Sr2(SetVarLocal, offset, targetr);

  *vset = vm->list(vset);

  pair = Spairref(pair->cdr());
  Assert(pair->cdr()->isnull(), "bad set! form");

  compile(inst, rVal, vars, jf, pair->car(), Snext);

  Sinstvar(setinst);
  setinst.set(regv(rEnv)|regv(rVal), regv(targetr), pairref(vset));

  inst->preserving(regv(rEnv), &setinst);
}

void SCompiler::compileseq(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, PairPtr pair, ValueT* link)
{
  if (pair->cdr()->isnull())
    compile(inst, targetr, vars, jf, pair->car(), link);

  else
  {
    Sinstvar(rest);

    compileseq(&rest, targetr, vars, jf, Spairref(pair->cdr()), link);

    compile(inst, targetr, vars, jf, pair->car(), Snext);

    inst->preserving(regv(rEnv)|regv(rContinue), &rest);
  }
}

void SCompiler::makeiftest(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, PairPtr pair, ValueT* link)
{
  ValueT branchtrue; setlabel(&branchtrue);
  ValueT branchfalse; setlabel(&branchfalse);
  ValueT afterif; setlabel(&afterif);

  compile(inst, rVal, vars, jf, pair->car(), Snext);

  Sreservevt(ifjmp);
  *ifjmp = Sr1(IfFalseJump, &branchfalse);
  jf->toFix(labeli(&branchfalse), ifjmp->ref());
  *ifjmp = vm->list(ifjmp);

  Sinstvar(ifjmpinst);
  ifjmpinst.set(regv(rVal), rvEmpty, pairref(ifjmp));

  ValueT* conseqlink = isnext(link) ? &afterif : link;

  pair = Spairref(pair->cdr());

  Sinstvar(ccodeinst);
  compile(&ccodeinst, targetr, vars, jf, pair->car(), conseqlink);
  ccodeinst.label(&branchtrue);

  pair = Spairref(pair->cdr());
  Assert(pair->cdr()->isnull(), "if syntax error");

  Sinstvar(acodeinst);
  compile(&acodeinst, targetr, vars, jf, pair->car(), link);

  acodeinst.label(&branchfalse);
  acodeinst.labelend(&afterif);

  ccodeinst.parallel(&acodeinst);

  ifjmpinst.append(&ccodeinst);

  inst->preserving(regv(rEnv)|regv(rContinue), &ifjmpinst);
}

class VarsProtectShrink {
public:
  VarsProtectShrink(VM* v, VarsPtr vp): vm(v), vars(vp) {}

  ~VarsProtectShrink() { vars->shrink(vm); }

  VM* vm;
  VarsPtr vars;
};

void SCompiler::makelambda(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, PairPtr pair, ValueT* link)
{
  Sreservevt(lambda);

  VarsPtr newvars = Sr1(VarsObj, vars);
  Sgcreserve(newvars);
  VarsProtectShrink(vm, newvars);

  newvars->initparam(vm, pair->car());

  ValueT lambdaentry; setlabel(&lambdaentry);
  ValueT lambdaend; setlabel(&lambdaend);

  *lambda = Sr3(LambdaObj, targetr, newvars, &lambdaentry);
  jf->toFix(labeli(&lambdaentry), lambda->ref());
  *lambda = vm->list(lambda);

  inst->set(regv(rEnv), regv(targetr), pairref(lambda));

  ValueT* llink = isnext(link) ? &lambdaend : link;

  endwithlink(jf, inst, llink);

  Sinstvar(bodyinst);
  compileseq(&bodyinst, rVal, newvars, jf, Spairref(pair->cdr()), Sreturn);
  bodyinst.label(&lambdaentry);
  bodyinst.labelend(&lambdaend);

  inst->tack(&bodyinst);
}

void SCompiler::constructarg0(InstPtr inst, InstArr* iarr, int index)
{
  static ConsArg consArg;
  ValueT carg;
  setref(&carg, &consArg);

  Sreservevt(varg);
  *varg = vm->list(&carg);

  Sinstvar(arginst);
  arginst.set(regv(rVal)|regv(rArgl), regv(rArgl), pairref(varg));

  *inst = iarr->geti(index)->preserving(regv(rArgl), &arginst);

  if (index > 0)
  {
    Sinstvar(restinst);
    constructarg0(&restinst, iarr, --index);

    inst->preserving(regv(rEnv), &restinst);
  }
}

void SCompiler::constructarg(InstPtr inst, VarsPtr vars, JumpToFix* jf, ValueT* cdrval)
{
  static Assign assignargnull(rArgl, Snullref);
  ValueT vassignargnull;
  setref(&vassignargnull, &assignargnull);

  int count = 0;
  for (ValueT* arg = cdrval; !arg->isnull(); arg = Spairref(arg)->cdr())
    count++;

  if (count <= 0)
    inst->set(rvEmpty, regv(rArgl), vm->list(&vassignargnull));

  else
  {
    int i = 0;
    InstArr iarr(vm, count);
    ValueT* arg = cdrval;
    while (!arg->isnull())
    {
      PairPtr pair = Spairref(arg);
      arg = pair->cdr();

      compile(iarr.geti(i++), rVal, vars, jf, pair->car(), Snext);
    }

    static InitArg initArg;
    ValueT carg;
    setref(&carg, &initArg);

    Sinstvar(initinst);
    initinst.set(regv(rVal), regv(rArgl), vm->list(&carg));

    int last = count - 1;
    *inst = iarr.geti(last)->append(&initinst);

    if (last > 0)
    {
      Sinstvar(restinst);
      constructarg0(&restinst, &iarr, last - 1);

      inst->preserving(regv(rEnv), &restinst);
    }
  }
}

void SCompiler::compilelambdaappl(InstPtr inst, JumpToFix* jf, int targetr, ValueT* link)
{
  static JumpProc jmpproc;

  ValueT vjumpproc;
  setref(&vjumpproc, &jmpproc);

  if (targetr == rVal && !isreturn(link))
  {
    // link must be a label
    Sreservevt(assign);
    *assign = Sr2(AssignLabel, rContinue, link);
    jf->toFix(Slabeli(link), assign->ref());

    inst->set(regv(rProc), allreg, vm->list(assign, &vjumpproc));
  }

  else if (targetr != rVal && !isreturn(link))
  {
    Sreservevt(assign);
    Sreservevt(assignreg);
    Sreservevt(jmp);

    ValueT branchreturn; setlabel(&branchreturn);

    *assign = Sr2(AssignLabel, rContinue, &branchreturn);
    jf->toFix(labeli(&branchreturn), assign->ref());

    *jmp = Sr1(JumpLabel, link);
    jf->toFix(Slabeli(link), jmp->ref());

    *assignreg = Sr2(AssignReg, targetr, rVal);

    PairPtr expr = vm->list(assign,
                            &vjumpproc,
                            &branchreturn,
                            assignreg,
                            jmp);
    Sgcreserve(expr);

    inst->set(regv(rProc), allreg, expr);
  }

  else if (targetr == rVal && isreturn(link))
    inst->set(regv(rProc)|regv(rContinue), allreg, vm->list(&vjumpproc));

  else
  {
    Error("return link, target not val %d %d", targetr, link->gettype());
  }
}

void SCompiler::compileappcall(InstPtr inst, JumpToFix* jf, int targetr, ValueT* link)
{
  ValueT branchprim; setlabel(&branchprim);
  ValueT branchcompile; setlabel(&branchcompile);
  ValueT aftercall; setlabel(&aftercall);

  Sreservevt(callapp);
  *callapp = Sr2(CallApp, &branchcompile, &branchprim);
  jf->toFix(labeli(&branchcompile), callapp->ref());
  jf->toFix(labeli(&branchprim), callapp->ref());

  setinst1v(inst, regv(rProc), rvEmpty, callapp);

  ValueT* compilelink = isnext(link) ? &aftercall : link;

  Sinstvar(lambdainst);
  compilelambdaappl(&lambdainst, jf, targetr, compilelink);
  lambdainst.label(&branchcompile);

  Sreservevt(applyprim);
  *applyprim = Sr1(ApplyPrim, targetr);

  Sinstvar(priminst);
  setinst1v(&priminst, regv(rProc)|regv(rArgl), regv(targetr), applyprim);
  priminst.label(&branchprim);

  endwithlink(jf, &priminst, link);

  inst->append(lambdainst.parallel(&priminst)->labelend(&aftercall));
}

void SCompiler::makeapp(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* type, ValueT* cdrval, ValueT* link)
{
  compile(inst, rProc, vars, jf, type, Snext);

  Sinstvar(argsinst);
  constructarg(&argsinst, vars, jf, cdrval);

  Sinstvar(appcallinst);
  compileappcall(&appcallinst, jf, targetr, link);

  inst->preserving(regv(rEnv)|regv(rContinue),
                   argsinst.preserving(regv(rProc)|regv(rContinue), &appcallinst));
}

void SCompiler::compilepair(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, PairPtr pair, ValueT* link)
{
  ValueT* type = pair->car();

  if (iskquote(type))
  {
    Sreservevt(assign);

    *assign = Sr2(Assign, targetr, pair->cdr());
    inst->set(rvEmpty, regv(targetr), vm->list(assign));

    endwithlink(jf, inst, link);
  }

  else if (iskdefine(type))
  {
    makedef(inst, targetr, vars, jf, pair->cdr());
    endwithlink(jf, inst, link);
  }

  else if (iskset(type))
  {
    makeset(inst, targetr, vars, jf, pair->cdr());
    endwithlink(jf, inst, link);
  }

  else if (iskbegin(type))
    compileseq(inst, targetr, vars, jf, Spairref(pair->cdr()), link);

  else if (iskif(type))
    makeiftest(inst, targetr, vars, jf, Spairref(pair->cdr()), link);

  else if (isklambda(type))
    makelambda(inst, targetr, vars, jf, Spairref(pair->cdr()), link);

  else
    makeapp(inst, targetr, vars, jf, type, pair->cdr(), link);
}

void SCompiler::compile(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* val, ValueT* link)
{
  if (ispair(val))
    compilepair(inst, targetr, vars, jf, pairref(val), link);

  else if (issym(val))
    compilesym(inst, targetr, vars, jf, symref(val), link);

  else /* (val->isnull()) or other types */
  {
    Sreservevt(assign);

    *assign = Sr2(Assign, targetr, val);
    setinst1v(inst, rvEmpty, targetr, assign);

    endwithlink(jf, inst, link);
  }
}

void SCompiler::printcompilecode(ValueT* val)
{
  JumpToFix jf(vm, labelmax);
  Sinstvar(inst);
  compile(&inst, rVal, NULL, &jf, val, Snext);

  printf("\n==Compiled Code==\n\n");
  printir(inst.expr);
  printf("\n\n==Compiled Code End==\n\n");
}

PairPtr SCompiler::compile(ValueT* val)
{
  JumpToFix jf(vm, labelmax);
  Sinstvar(inst);
  compile(&inst, rVal, NULL, &jf, val, Snext);

  return extractlabel(&jf, inst.expr);
}

PairPtr SCompiler::extractlabel(JumpToFix* jf, PairPtr expr)
{
  if (expr == NULL)
    return NULL;

  ValueT* first = expr->car();
  if (islabel(first))
  {
    int label = labeli(first);

    PairPtr pair  = extractlabel(jf, pairref(expr->cdr()));
    if (pair)
      jf->fix(label, pair);

    return pair;
  }

  else
  {
    PairPtr inst = extractlabel(jf, pairref(expr->cdr()));

    ValueT val;
    setpair(&val, inst);
    expr->cdr(&val);

    GC(vm)->checkBarrier(expr);

    return expr;
  }
}

static const char* getregname(byte reg)
{
  switch(reg) {
  case rEnv: return "rEnv";
  case rProc: return "rProc";
  case rVal: return "rVal";
  case rArgl: return "rArgl";
  case rContinue: return "rContinue";
  default: Error("unknown reg %x", reg);
  }
}

void SCompiler::printvt(const char* pre, ValueT* v)
{
  printf("%s", pre);
  switch(v->t) {
  case VT_REF_STR:
    printf("\"%s\"", strref(v)->str);
    break;
  case VT_REF_SYM:
    printf("%s", symref(v)->str);
    break;
  case VT_NUM_INTEGER:
    printf("%d", numi(v));
    break;
  case VT_LABEL:
    printf("%d", labeli(v));
    break;
  default:
    Error("unknown type %x", v->t);
    break;
  }
}

void SCompiler::printregs(const char* pre, byte regs)
{
  printf("%s", pre);
  for (int i = 0; i < rMax; i++)
  {
    if (regs & regv(i))
      printf("%s(%x) ", getregname(i), i);
  }
}

void SCompiler::printreg(const char* pre, byte reg)
{
  printf("%s[%s(%x)]", pre, getregname(reg), reg);
}

void SCompiler::printir0(ExeCmd* cmd)
{
  switch(cmd->getcmd()) {
  case CMD_ASSIGN: {
    Assign* ass = assignptr(cmd);
    printf("ASSIGN");
    printreg(" ", ass->reg);
    printvt(" ", ass->getval());
    break;
  }
  case CMD_LAMBDA: {
    LambdaPtr lambda = lambdaptr(cmd);
    printf("LAMBDA %s(%x)", getregname(lambda->targetr), lambda->targetr);
    printf("entry[%d]", labeli(lambda->getentry()));
  }
  case CMD_ASSIGN_REG: {
    AssignReg* ar = assignregptr(cmd);
    printf("ASSIGNREG");
    printreg(" ", ar->dst);
    printreg(" ", ar->src);
    break;
  }
  case CMD_JUMP_PROC: {
    printf("JUMPPROC");
    break;
  }
  case CMD_JUMP_CONTINUE: {
    printf("JUMPCONTINUE");
    break;
  }
  case CMD_JUMP_LABEL: {
    printf("JUMPLABEL");
    printf(" %d", labeli(jumplabelptr(cmd)->getentry()));
    break;
  }
  case CMD_SAVE_REG: {
    printf("SAVEREG");
    printregs(" ", saveregptr(cmd)->reg);
    break;
  }
  case CMD_RESTORE_REG: {
    printf("RESTOREREG");
    printregs(" ", restoreregptr(cmd)->reg);
    break;
  }
  case CMD_REF_LOCAL: {
    printf("REFLOCAL");
    RefLocalVar* ref = reflocalptr(cmd);
    printreg(" ", ref->reg);
    printf("offset[%d]", ref->offset);
    break;
  }
  case CMD_REF_UP: {
    printf("REFUP");
    RefUpVar* ref = refupptr(cmd);
    printreg(" ", ref->reg);
    printf("outer offset[%d]", ref->oidx);
    break;
  }
  case CMD_REF_GLOBAL: {
    printf("REFGLOBAL");
    RefGlobalVar* ref = refglobalptr(cmd);
    printreg(" ", ref->reg);
    printf(" Var[%s]", objstr(ref->var));
    break;
  }
  case CMD_DEF_GLOBAL: {
    printf("DEFGLOBAL");
    DefGlobalVar* def = defglobalptr(cmd);
    printf(" %s", objstr(def->var));
    printreg(" ", rVal);
    break;
  }
  case CMD_DEF_LOCAL: {
    printf("DEFLOCAL");
    DefLocalVar* def = deflocalptr(cmd);
    printf(" offset[%d]", def->offset);
    printreg(" ", rVal);
    break;
  }
  case CMD_SET_LOCAL: {
    printf("SETLOCAL");
    SetVarLocal* set = setvarlocalptr(cmd);
    printf(" offset[%d]", set->offset);
    printreg(" ", rVal);
    break;
  }
  case CMD_SET_UP: {
    printf("SETUP");
    SetVarUp* set = setvarupptr(cmd);
    printf(" upoffset[%d]", set->offset);
    printreg(" ", rVal);
    break;
  }
  case CMD_SET_GLOBAL: {
    printf("SETGLOBAL");
    SetVarGlobal* set = setvarglobalptr(cmd);
    printf(" Var[%s]", objstr(set->var));
    printreg(" ", rVal);
    break;
  }
  case CMD_IF_FALSE_JUMP: {
    printf("IFFALSEJUMP");
    IfFalseJump* jmp = iffalsejumpptr(cmd);
    printf("%d", labeli(&(jmp->entry)));
    break;
  }
  case CMD_INIT_ARG: {
    printf("INITARG");
    break;
  }
  case CMD_APPLY_PRIM: {
    printf("APPLYPRIM");
    printreg(" ", applyprimptr(cmd)->targetr);
    break;
  }
  case CMD_CALL_APP: {
    printf("CALLAPP");
    CallApp* ca = callappptr(cmd);
    printf(" Proc(%d) Prim(%d)", labeli(&(ca->lproc)), labeli(&(ca->lprim)));
    break;
  }
  case CMD_CONS_ARG: {
    printf("CONSARG");
    break;
  }
  default:
    Error("unknown cmd %d", cmd->getcmd());
  }
}

void SCompiler::printir(PairPtr expr)
{
  int maxlabel = 0;
  PairPtr oldexpr = expr;
  while (expr)
  {
    ValueT* vcmd = expr->car();
    if (islabel(vcmd))
    {
      int label = labeli(vcmd);
      if (label > maxlabel)
        maxlabel = label;
    }

    expr = pairref(expr->cdr());
  }

  int nspace = 0;
  while (maxlabel > 0)
  {
    nspace++;
    maxlabel /= 10;
  }

  ValueT* lastv = NULL;
  expr = oldexpr;
  while (expr)
  {
    ValueT* vcmd = expr->car();
    if (islabel(vcmd))
    {
      printf("\n");
      printf("%*d", nspace, labeli(vcmd));
      printf(": ");
    }
    else
    {
      if (!lastv || !islabel(lastv))
        printf("\n%*s  ", nspace, " ");

      printir0(execmdref(vcmd));
    }

    lastv = vcmd;
    expr = pairref(expr->cdr());
  }
}

void GSymTable::init()
{
  lsizenode = MINLTSIZE;
  int size = twoto(lsizenode);
  slots = new (vm->alloc(size * sizeof(TSlot))) TSlot[size];

  lastfree = &slots[size - 1];
}

void GSymTable::newkey(SymPtr sym, ValueT* v)
{
  ValueT symp;
  setsym(&symp, sym);

  PairPtr tv = Sconsref(&symp, v);
  Sgcreserve(tv);

  insert(sym, tv);
}

void GSymTable::newkeyorupdate(SymPtr sym, ValueT* val)
{
  PairPtr pair = getslot(sym);
  if (pair == NULL)
    newkey(sym, val);

  else
  {
    pair->cdr(val);
    GC(vm)->checkBarrier(pair);
  }
}

void GSymTable::insert(SymPtr sym, PairPtr tv)
{
  TSlot* node = getpos(sym);
  // not empty
  // collide
  if (node->tv != NULL)
  {
    TSlot* freenode = getfreepos();
    if (!freenode)
    {
      rehash();
      insert(sym, tv);
      return;
    }

    TSlot* othernode = getpos(symref(node->tv->car()));
    // 1 move newsym to empty
    if (node == othernode)
    {
      // find previous node
      while (othernode->next) othernode = othernode->next;
      othernode->next = freenode;

      freenode->settv(tv);
    }
    // 2 move othersym to empty
    else
    {
      freenode->tv = othernode->tv;

      othernode->settv(tv);
      othernode->next = freenode;
    }
  }

  else
    node->settv(tv);
}

void GSymTable::rehash()
{
  int oldsize = twoto(lsizenode);

  lsizenode += 1;
  int size = twoto(lsizenode);

  TSlot* oldslots = slots;

  slots = new (vm->alloc(size * sizeof(TSlot))) TSlot[size];
  lastfree = &slots[size - 1];

  for (int i = 0; i < oldsize; i++)
  {
    TSlot* slot = &oldslots[i];
    insert(symref(slot->tv->car()), slot->tv);
  }

  vm->free(oldslots, oldsize * sizeof(TSlot));
}

TSlot* GSymTable::getfreepos()
{
  if (lastfree)
  {
    if (lastfree->tv == NULL) return lastfree;

    while (lastfree > slots)
    {
      lastfree--;
      if (lastfree->tv == NULL) return lastfree;
    }
  }

  return NULL;
}

TSlot* GSymTable::getpos(SymPtr sym)
{
  return &slots[objstrh(sym) & (twoto(lsizenode) - 1)];
}

void GSymTable::getval(SymPtr sym, ValueT* v)
{
  PairPtr pair = getslot(sym);
  if (pair == NULL)
    setundefined(v);

  else
    *v = pair->cdr();
}

PairPtr GSymTable::getslot(SymPtr sym)
{
  Assert(sym, "key null");

  TSlot* node = getpos(sym);
  for (;;)
  {
    if (node->tv == NULL) return NULL;

    if (sym == Ssymref(node->tv->car())) return node->tv;

    if (node->next == NULL) return NULL;

    node = node->next;
  }
  // won't reach here
}

RegFrame::RegFrame(int r, ValueT rs[rMax])
{
  regs = r;
  for (int i = 0; i < rMax; i++)
    if (r & regv(i))
      regval[i] = rs[i];
}

void RegFrame::restore(ValueT vmreg[rMax])
{
  for (int i = 0; i < rMax; i++)
    if (regs & regv(i))
      vmreg[i] = regval[i];
}

void VM::stepmarkregs()
{
  for (int i = 0; i < rMax; i++)
    getgc()->checkTrace(regs[i]);
}

void VM::stepmarkframes()
{
  getgc()->checkTrace(frames);
}

void VM::regfullmark()
{
  for (int i = 0; i < rMax; i++)
    getgc()->checkTrace(regs[i]);

  getgc()->checkTrace(frames);
}

/**
 * called from the eval loop
 */
void VM::checkgc()
{
  if (getgc()->state == GCSNone)
  {
    getobjgroup()->swapobjset();
    getgc()->startstep();
    getgc()->singlestep();
  }

  else
    getgc()->singlestep();
}

void VM::eval(ValueT* out, PairPtr expr)
{
  VM* vm = this;

  Sreservevt(tmp);

  PairPtr pc = expr;
 loop:
  if (!pc) return;
  checkgc();

  ExeCmd* cmd = execmdref(pc->car());
  switch(cmd->getcmd()) {
  case CMD_ASSIGN: {
    assignptr(cmd)->assignreg(regs);
    break;
  }
  case CMD_LAMBDA: {
    LambdaPtr lambda = lambdaptr(cmd);
    EnvPtr env = NULL;
    ValueT venv = regs[rEnv];
    if (!Sisnull(&venv))
      env = envref(&venv);
    setref(&regs[lambda->targetr], Sr2(ClosureObj, env, lambda));
    break;
  }
  case CMD_ASSIGN_REG: {
    assignregptr(cmd)->assignreg(regs);
    break;
  }
  case CMD_JUMP_PROC: {
    ClosurePtr clo = closureptr(cmd);
    EnvPtr oenv = envref(&regs[rEnv]);

    EnvPtr nenv = Sr2(EnvObj, oenv, clo->lambda->vars);
    nenv->extend(this, regs, &regs[rArgl]);

    setref(&regs[rEnv], nenv);
    pc = Spairref(clo->lambda->getentry());
    goto loop;
  }
  case CMD_JUMP_CONTINUE: {
    pc = Spairref(&regs[rContinue]);
    goto loop;
  }
  case CMD_JUMP_LABEL: {
    pc = Spairref(&(jumplabelptr(cmd)->entry));
    goto loop;
  }
  case CMD_SAVE_REG: {
    *tmp = Sr2(RegFrame, saveregptr(cmd)->reg, regs);
    ValueT frm;
    if (frames != NULL)
      setpair(&frm, frames);

    frames = Sconsref(tmp, &frm);
    break;
  }
  case CMD_RESTORE_REG: {
    RegFrame* frm = frameref(frames->car());
    Assert(restoreregptr(cmd)->reg == frm->regs, "save restore reg error");

    frames = pairref(frames->cdr());
    frm->restore(regs);

    break;
  }
  case CMD_REF_LOCAL: {
    reflocalptr(cmd)->ref(regs, envref(&regs[rEnv]));
    break;
  }
  case CMD_REF_UP: {
    refupptr(cmd)->ref(regs, envref(&regs[rEnv]));
    break;
  }
  case CMD_REF_GLOBAL: {
    refglobalptr(cmd)->ref(regs, getgenv());
    break;
  }
  case CMD_DEF_GLOBAL: {
    defglobalptr(cmd)->def(regs, getgenv());
    break;
  }
  case CMD_DEF_LOCAL: {
    deflocalptr(cmd)->def(regs, envref(&regs[rEnv]));
    break;
  }
  case CMD_SET_LOCAL: {
    setvarlocalptr(cmd)->set(regs, envref(&regs[rEnv]));
    break;
  }
  case CMD_SET_UP: {
    setvarupptr(cmd)->set(regs, envref(&regs[rEnv]));
    break;
  }
  case CMD_SET_GLOBAL: {
    setvarglobalptr(cmd)->set(vm, regs, getgenv());
    break;
  }
  case CMD_IF_FALSE_JUMP: {
    if (Sisfalse(&regs[rVal]))
    {
      pc = Spairref(&(iffalsejumpptr(cmd)->entry));
      goto loop;
    }
    break;
  }
  case CMD_INIT_ARG: {
    setpair(&regs[rArgl], vm->list(&regs[rVal]));
    break;
  }
  case CMD_APPLY_PRIM: {
    CFunction f = regs[rProc].cfunc();
    ValueT* out = &regs[applyprimptr(cmd)->targetr];
    (*f)(this, out, &regs[rArgl]);
    break;
  }
  case CMD_CALL_APP: {
    CallApp* ca = callappptr(cmd);
    if (iscfunction(&regs[rProc]))
      pc = Spairref(&(ca->lprim));

    else
      pc = Spairref(&(ca->lproc));

    goto loop;
  }
  case CMD_CONS_ARG: {
    setpair(&regs[rArgl], Sconsref(&regs[rVal], &regs[rArgl]));
    break;
  }
  default:
    Error("unknown cmd %d", cmd->getcmd());
  }
// advpc:
  if (!Sisnull(pc->cdr()))
  {
    pc = pairref(pc->cdr());
    goto loop;
  }
}

#define addbuff(b,p,e)                            \
{ size_t t = (size_t)(e);                         \
  memcpy(b + p, &t, sizeof(t)); p += sizeof(t); } \

void VM::makeseed()
{
  char buff[3 * sizeof(size_t)];
  int h = time(NULL);
  int p = 0;

  addbuff(buff, p, this);
  addbuff(buff, p, &h);
  addbuff(buff, p, &intern);

  Assert(p == sizeof(buff), "internal makeseed error");
  seed = Util::hash(buff, p, h);
}

void VM::regCFunction(const char* name, CFunction f)
{
  int n = strlen(name);
  SymPtr sym = getintern()->intern(name, n);

  PairPtr pair = getgenv()->getslot(sym);
  Assert(!pair, "key already exists %s", name);

  ValueT cf;
  setcfunction(&cf, f);

  getgenv()->newkey(sym, &cf);
}

void VM::init()
{
  getconst()->init();
  getintern()->init();
  getgenv()->init();

  ScmMath::init(this);
}

VM::VM(ScmAlloc a):
  frealloc(a), gc(this), stk(this), objGroup(this),
  intern(this), consts(this), cachePair(this), compiler(this),
  genv(this)
{
  weakIdx = 0;

  makeseed();

  frames = NULL;

  init();
}

void* VM::realloc(void* ptr, size_t osize, size_t nsize)
{
  long debt = getgc()->debt();

  void* block = frealloc(ptr, nsize);
  if (block == NULL)
  {
    gc.fullgc();
    block = frealloc(ptr, nsize);
  }
  if (osize < nsize) memset((byte*)block + osize, 0, nsize - osize);

  getgc()->debt(debt + nsize - osize);
  debt = getgc()->debt();

  Debug(Print("realloc mem(%u) -> %p old(%u) -> %p \n", nsize, block, osize, ptr));

  return block;
}

void* VM::alloc(size_t size)
{
  long debt = getgc()->debt();

  void* block = frealloc(NULL, size);
  if (block == NULL)
  {
    gc.fullgc();
    block = frealloc(NULL, size);
  }
  memset(block, 0, size);

  getgc()->debt(debt + size);
  debt = getgc()->debt();

  Debug(Print("alloc mem(%u) -> %p\n", size, block));

  return block;
}

StrObj* VM::newstr(const char* str, int len, int h)
{
  int size = StrObj::totalsize(len);
  return new (alloc(size)) StrObj(str, len, h);
}

PairPtr VM::consref(ValueT* h, ValueT* t)
{
  PairPtr pair = cachePair.getone();
  if (pair == NULL)
    pair = new (alloc(sizeof(PairObj))) PairObj(h, t);

  else
  {
    pair->car(h);
    pair->cdr(t);
  }
  return (PairPtr)getobjgroup()->recobj(pair);
}

PairPtr VM::getonepairnor()
{
  PairPtr pair = cachePair.getone();
  if (pair == NULL)
    pair = new (alloc(sizeof(PairObj))) PairObj();

  pair->gcnxt = NULL;
  return pair;
}

StrObj* VM::stringref(const char* str, int len)
{
  if (len <= MAXSHORTLEN)
  {
    return getintern()->intern(str, len);
  }
  else
  {
    return (StrObj*)getobjgroup()->recobj(newstr(str, len, -1));
  }
}

#define reservelist(pbv, b)                     \
  PairPtr pb = (b); gcreserve(this, pb);        \
  ValueT pbv; setpair(&pbv, pb)

PairPtr VM::list(ValueT* a, ValueT* b)
{
  reservelist(pbv, list(b));
  return consref(a, &pbv);
}

PairPtr VM::list(ValueT* a, ValueT* b, ValueT* c)
{
  reservelist(pbv, list(b, c));
  return consref(a, &pbv);
}

PairPtr VM::list(ValueT* a, ValueT* b, ValueT* c, ValueT* d)
{
  reservelist(pbv, list(b, c, d));
  return consref(a, &pbv);
}

PairPtr VM::list(ValueT* a, ValueT* b, ValueT* c, ValueT* d, ValueT* e)
{
  reservelist(pbv, list(b, c, d, e));
  return consref(a, &pbv);
}

void VarsObj::visit(VM* vm)
{
  Check(outer);
  if (local)
    for (int i = 0; i < sizelocal; i++)
      Check(local[i]);

  if (ovar)
    for (int i = 0; i < sizeovar; i++)
      Check(ovar[i].name);
}

void VarsObj::finz(VM* vm)
{
  if (local) vm->free(local, sizelocal * sizeof(SymPtr));
  local = NULL;
  if (ovar) vm->free(ovar, sizeovar * sizeof(OuterVar));
  ovar = NULL;

  this->RefObject::finz(vm);
}


#define CheckSize(ptr, nele, size, ELE)                                 \
if (nele >= size) {                                                     \
  size = size * 2;                                                      \
  ptr = (ELE *)vm->realloc(ptr, nele * sizeof(ELE), size * sizeof(ELE)); \
 }

#define CheckInitSize(ptr, size, initsize, ELE) \
if (size <= 0) {                                \
  size = initsize;                              \
  ptr = (ELE *)vm->alloc(size * sizeof(ELE));   \
 }

#define ShrinkSize(ptr, size, nsize, ELE)                               \
if (size > 0 && size > nsize) {                                         \
  ptr = (ELE *)vm->realloc(ptr, size * sizeof(ELE), nsize * sizeof(ELE)); \
  size = nsize;                                                         \
 }

int VarsObj::addlocal(VM* vm, SymPtr sym)
{
  CheckInitSize(local, sizelocal, 2, SymPtr);
  CheckSize(local, nlocal, sizelocal, SymPtr);

  int k = nlocal++;
  local[k] = sym;

  return k;
}

int VarsObj::addovar(VM* vm, int depth, int idx)
{
  CheckInitSize(ovar, sizeovar, 2, OuterVar);
  CheckSize(ovar, novar, sizeovar, OuterVar);

  OuterVar ov(depth, idx);

  int k = novar++;
  ovar[k] = ov;
  return k;
}

void VarsObj::shrink(VM* vm)
{
  ShrinkSize(local, sizelocal, nlocal, SymPtr);
  ShrinkSize(ovar, sizeovar, novar, OuterVar);
}

int VarsObj::lookouter(SymPtr sym, int* depth)
{
  *depth = 0;
  int idx = -1;
  for (VarsPtr p = outer; p != NULL; p = p->outer, *depth = (*depth)+1)
    if ((idx = p->looklocal(sym)) > 0)
      break;

  return idx;
}

int VarsObj::lookovar(SymPtr sym)
{
  for (int i = novar-1; i >= 0; i--)
    if (ovar[i].name == sym) return i;

  return -1;
}

int VarsObj::looklocal(SymPtr sym)
{
  for (int i = nlocal-1; i >= 0; i--)
    if (local[i] == sym) return i;

  return -1;
}

void VarsObj::initparam(VM* vm, ValueT* param)
{
  while (!Sisnull(param) && ispair(param))
  {
    PairPtr ppair = pairref(param);
    param = ppair->cdr();
    addlocal(vm, Ssymref(ppair->car()));
  }

  if (issym(param))
    addlocal(vm, symref(param));
  else
  {
    Assert(param->isnull(), "bad lambda form");
  }
}

void EnvObj::visit(VM* vm)
{
  Check(outer);
  Check(vars);
  for (int i = 0; i < nlocal; i++)
    Check(&locals[i]);

  //  for (int i = 0; i < nout; i++)
  //    Check(outers[i]);
}

void EnvObj::finz(VM* vm)
{
  if (locals)
    vm->free(locals, nlocal * sizeof(ValueT));
  locals = NULL;
  nlocal = 0;

  if (outers)
    vm->free(outers, nout * sizeof(ValueT*));
  outers = NULL;
  nout = 0;

  this->RefObject::finz(vm);
}

void EnvObj::initlocalout(VM* vm, VarsPtr vars)
{
  if (vars->nlocal > 0)
  {
    nlocal = vars->nlocal;
    locals = (ValueT*) vm->alloc(sizeof(ValueT) * nlocal);
    for (int i = 0; i < nlocal; i++)
      setundefined(&locals[i]);
  }

  if (vars->novar > 0)
  {
    nout = vars->novar;
    outers = (ValueT**) vm->alloc(sizeof(ValueT*) * nout);
    for (int i = 0; i < nout; i++)
    {
      OuterVar* ov = &vars->ovar[i];
      int depth = ov->depth, idx = ov->idx;

      EnvPtr oe = outer;
      while (depth-- > 0) oe = oe->outer;
      outers[i] = &oe->locals[idx];
    }
  }
}

void EnvObj::extend(VM* vm, ValueT regs[rMax], ValueT* argl)
{
  initlocalout(vm, vars);

  int index = 0;
  for (; index < nlocal && !Sisnull(argl); index++)
  {
    if (ispair(argl))
    {
      PairPtr pair = pairref(argl);
      argl = pair->cdr();

      locals[index] = pair->car();
    }

    else
    {
      locals[index] = argl;
      break;
    }
  }
}

enum TokenType {
	TOKEN_UNKNOWN,
	TOKEN_END,
	TOKEN_NUM,
	TOKEN_STRING,
	TOKEN_DOT,
	TOKEN_LEFT_PAREN,
	TOKEN_RIGHT_PAREN,
  TOKEN_LEFT_SQUARE_PAREN,
  TOKEN_RIGHT_SQUARE_PAREN,
	TOKEN_SYMBOL,
	TOKEN_QUOTE,
	TOKEN_UNQUOTE,
	TOKEN_UNQUOTE_SPLICING,
	TOKEN_QUASIQUOTE,
  TOKEN_MAX,
};


static const char* TokenType[] = {
  "UNKNOWN",
  "END",
  "NUM",
  "STRING",
  "DOT",
  "LEFT_PAREN",
  "RIGHT_PAREN",
  "LEFT_SQUARE_PAREN",
  "RIGHT_SQUARE_PAREN",
  "SYMBOL",
  "QUOTE",
  "UNQUOTE",
  "UNQUOTE_SPLICING",
  "QUASIQUOTE",
  "MAX"
};

#define CASE_DIGIT case '0':case '1':case '2':case '3':case '4':case '5':case '6':case '7':case '8':case '9'
#define CASE_BLANK case '\n':case ' ':case '\t':case '\r':case '\0'

void Lexer::match(int type)
{
  Assert(type == aheadToken,
         "unrecognized token type %s with current %s",
         TokenType[type],
         TokenType[aheadToken]);

  aheadToken = dLex();
}

int Lexer::dLex()
{
  skipBlankComment();

	if (reader->isEnd())
		return TOKEN_END;

  int token = TOKEN_UNKNOWN;

  switch(reader->curChar()) {
  case '\'':
		token = TOKEN_QUOTE;
    reader->advance();
    break;
  case '`':
		token = TOKEN_QUASIQUOTE;
    reader->advance();
		break;
  case ',':
    token = TOKEN_UNQUOTE;
    reader->advance();
    if (!reader->isEnd() && '@' == reader->curChar())
    {
      token = TOKEN_UNQUOTE_SPLICING;
      reader->advance();
    }
    break;
  case '"':
    token = readString();
    break;
  case '(':
		token = TOKEN_LEFT_PAREN;
    reader->advance();
    break;
	case ')':
		token = TOKEN_RIGHT_PAREN;
    reader->advance();
    break;
  case '[':
		token = TOKEN_LEFT_SQUARE_PAREN;
    reader->advance();
    break;
	case ']':
		token = TOKEN_RIGHT_SQUARE_PAREN;
    reader->advance();
    break;
  case '.':
    token = TOKEN_DOT;
    reader->advance();
    if (!reader->isEnd())
    {
      switch(reader->curChar()){
      CASE_BLANK:break;
      CASE_DIGIT:
        // TODO: readfloat
        break;
      default:
        token = readSymbol('.');
        break;
      }
    }
    break;
  CASE_DIGIT:
    token = readNum();
    break;
  default:
    token = readSymbol();
    break;
  }

  return token;
}

void Lexer::skipBlankComment()
{
 loop:
  if(reader->isEnd())
    return;

  switch(reader->curChar()) {
  CASE_BLANK: reader->advance(); goto loop;
  case ';':
    while(!reader->isEnd() && reader->curChar() != '\n')
      reader->advance();

    reader->advance();
    goto loop;
  default:
    break;
  }
}

int Lexer::readSymbol(char init)
{
  buff.reset();

  if (init) buff.put(init);

 loop:
  if(!reader->isEnd())
  {
		char c = reader->curChar();
    switch(c){
    CASE_BLANK:
    case ')':
      break;
		default:
      buff.put(c);
      reader->advance();
      goto loop;
		}
	}

	return TOKEN_SYMBOL;
}

int Lexer::readSymbol()
{
  return readSymbol(0);
}

int Lexer::readString()
{
  buff.reset();

  reader->advance();

  char c;
  while(!reader->isEnd())
  {
    c = reader->curCharAdv();
    if (c == '\"')
      break;
    buff.put(c);
  }

  if (c != '\"')
    return TOKEN_UNKNOWN;

	return TOKEN_STRING;
}

int Lexer::readNum()
{
	// TODO: read float
	char num[20] = {0};
	int temp = 0;

 loop:
  if(!reader->isEnd())
  {
    char c = reader->curChar();
    switch(c){
    case ' ':
    case '\t':
    case '\n':
    case '\r':
    case '\0':
    case ')':
      break;
    default:
      // TODO: illegal char
      num[temp++] = c;
      reader->advance();
      goto loop;
    }
  }

  int n = 0;
	sscanf(num, "%d", &n);
  readI = n;

	return TOKEN_NUM;
}

void Lexer::readOne(ValueT* v)
{
  if (aheadToken != TOKEN_END)
    readValueT(v);
}

void Lexer::readListT(ValueT* v)
{
  PairObj* last = NULL;
  bool dot = false;

  Sreservevt(sval);

  while (aheadToken != TOKEN_RIGHT_PAREN &&
         aheadToken != TOKEN_RIGHT_SQUARE_PAREN)
  {
    sval->reset();

    readValueT(sval);

    if (Sisnull(sval))
    {
      if (aheadToken == TOKEN_DOT)
      {
        dot = true;

        Assert(!v->isnull(), "dot cannot be the first item");

        match(TOKEN_DOT);

        readValueT(sval);

        Assert(aheadToken == TOKEN_RIGHT_SQUARE_PAREN ||
               aheadToken == TOKEN_RIGHT_PAREN,
               "must have only one item after dot");
        break;
      }
    }

    PairPtr tmp = vm->list(sval);

    if (NULL == last)
    {
      last = tmp;
      setpair(v, tmp);
    }
    else
    {
      ValueT tmpp;
      setpair(&tmpp, tmp);

      last->cdr(&tmpp);
      GC(vm)->checkBarrier(last);

      last = tmp;
    }
  }

  if (dot)
  {
    last->cdr(sval);
    GC(vm)->checkBarrier(last);
  }
}

void Lexer::readValueT(ValueT* v)
{
  switch(aheadToken) {
	case TOKEN_NUM:
    setnumi(v, readI);
		match(TOKEN_NUM);
    break;
	case TOKEN_STRING:
    setstr(v, vm->stringref(buff.buf, buff.count));
		match(TOKEN_STRING);
    break;
	case TOKEN_SYMBOL:
    setsym(v, Intern(vm)->intern(buff.buf, buff.count));
		match(TOKEN_SYMBOL);
    break;
	case TOKEN_QUOTE: {
    match(TOKEN_QUOTE);
    Sreservevt(v2);
    readValueT(v2);
    setpair(v, Squote_ref(v2));
    break;
  }
	case TOKEN_UNQUOTE: {
    match(TOKEN_UNQUOTE);
    Sreservevt(v2);
    readValueT(v2);
    setpair(v, Su_quote_ref(v2));
    break;
  }
	case TOKEN_QUASIQUOTE: {
    match(TOKEN_QUASIQUOTE);
    Sreservevt(v2);
    readValueT(v2);
    setpair(v, Sq_quote_ref(v2));
    break;
  }
	case TOKEN_UNQUOTE_SPLICING: {
    match(TOKEN_UNQUOTE_SPLICING);
    Sreservevt(v2);
    readValueT(v2);
    setpair(v, Su_quote_s_ref(v2));
    break;
  }
	case TOKEN_LEFT_PAREN:
		match(TOKEN_LEFT_PAREN);
		readListT(v);
		match(TOKEN_RIGHT_PAREN);
    break;
  case TOKEN_LEFT_SQUARE_PAREN:
		match(TOKEN_LEFT_SQUARE_PAREN);
		readListT(v);
		match(TOKEN_RIGHT_SQUARE_PAREN);
    break;
  case TOKEN_DOT:
    *v = Snullref;
    break;
	default:
		Error("somethign error happened");
    break;
	}
}
