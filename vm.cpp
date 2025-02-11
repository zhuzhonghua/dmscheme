#include "vm.h"
#include "scmmath.h"

using namespace Scheme;

void RefObject::finz(VM* vm)
{
  if (marked & (1 << WEAKTAG))
    vm->rmWeak(this);

  this->~RefObject();

  vm->free(this, this->getsize());
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

#define ToDelOrMark(item, objgroup, gc)         \
{if ((item)->isgcmark((objgroup)->curbit()))    \
    (objgroup)->addrefcur(item);                \
  else                                          \
    gc->toDel(item);}

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

    ToDelOrMark(item, this, GC(vm));
  }
}

bool RefObjGroup::stepsweep()
{
  RefPtr* lst = &gclst[othIdx];

  for(int i = 0; i < 10 && (*lst) != NULL; i++)
  {
    RefPtr item = *lst;
    lst = &(*lst)->gcnxt;

    ToDelOrMark(item, this, GC(vm));
  }

  return (*lst) != NULL;
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
  cache = (PairPtr)ref->link(cache);
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
    p->finz(vm);
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

  touchf = &SGC::addchildgraylst;
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
    Assert(pair->cdr()->isref(), "internal error gray lst cdr not ref");

    Check(pair->car());
    Check(pair->cdr());

    pair->car(Snullref);
    pair->cdr(Snullref);

    CachePair(vm)->addref(pair);
  }

  return true;
}

void SGC::addchildgraylst(ValueT* ref)
{
  if (graylst == NULL)
  {
    PairPtr pair = vm->getonepairnor();

    graylst = graylstLast = pair;

    graylstLast->car(ref);
  }
  else
  {
    ValueT* last = graylstLast->cdr();
    if (last->isnull())
      *last = ref;

    else
    {
      PairPtr pair = vm->getonepairnor();

      graylstLast->gcnxt = pair;
      graylstLast = pair;

      pair->car(ref);
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

    RefPtr item = pair->car()->ref();

    ToDelOrMark(item, ObjGroup(vm), this);

    if (!pair->cdr()->isnull())
    {
      item = pair->cdr()->ref();
      ToDelOrMark(item, ObjGroup(vm), this);
    }

    this->toDel(pair);
  }

  graylst = graylstLast = NULL;
}

void SGC::fullgc()
{
  touchf = &SGC::visitchild;

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
  touchf = &SGC::addchildgraylst;

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

void SGC::checkTrace(ValueT* v)
{
  if (v->isref())
  {
    byte curbit = ObjGroup(vm)->curbit();
    RefPtr ptr = v->ref();
    if (!ptr->isgcmark(curbit))
    {
      ptr->gcmark(curbit);

      (this->*touchf)(v);
    }
  }
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
    if (objstrl(ptr) == n && memcpy(objstr(ptr), str, n) == 0)
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
  Sgcvar2(vrestore, vsave);

  vrestore = Sr1(RestoreReg, sr);
  vrestore = vm->list(vrestore.obj());

  ValueT* vr = vrestore.obj();
  endwithpair(pairref(vrestore.obj()));

  vsave = Sr1(SaveReg, sr);

  ValueT exprv;
  setpair(&exprv, expr);

  setexpr(Sconsref(vsave.obj(), &exprv));
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
    while (pair != NULL)
    {
      FixJumpObj* ref = jumpobjref(pair->car());
      ref->fixJmp(label, jmp);

      pair = pairref(pair->cdr());
    }
  }
}

void JumpToFix::toFix(int label, RefPtr p)
{
  if (size == 0)
  {
    size = 2;
    int totalsize = size * sizeof(PairPtr);
    arrToFix = (PairPtr*)vm->alloc(totalsize);
    memset((byte*)arrToFix, 0, totalsize);
  }

  int rng = label - startlabel;
  if (rng >= size - 1)
  {
    int oldsize = size;
    do {
      size *= 2;
    } while (rng >= size - 1);

    arrToFix = (PairPtr*)vm->realloc(arrToFix, size * sizeof(PairPtr), size * sizeof(PairPtr));
    memset((byte*)(arrToFix + oldsize), 0, (size - oldsize) * sizeof(PairPtr));
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
    Sgcvar1(vjump);

    JumpLabel* jtf;
    vjump = jtf = Sr1(JumpLabel, link);
    jf->toFix(Slabeli(link), jtf);

    setinst1v(inst, rvEmpty, rvEmpty, vjump);
  }
}

void SCompiler::compilesym(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, SymPtr sym, ValueT* link)
{
  Sgcvar1(ref);

  int needr = regv(rEnv);

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
        ref = Sr2(RefGlobalVar, targetr, sym);
        needr = rvEmpty;
      }

      else
      {
        idx = vars->addovar(vm, depth, idx);
        ref = Sr2(RefUpVar, targetr, idx);
      }
    }
    else
      ref = Sr2(RefUpVar, targetr, idx);
  }

  else
    ref = Sr2(RefLocalVar, targetr, idx);

  setinst1v(inst, needr, regv(targetr), ref);

  endwithlink(jf, inst, link);
}

void SCompiler::makedef(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* val)
{
  Sgcvar2(vsymval, vdef);

  PairPtr pair = Spairref(val);
  ValueT* symv = pair->car();

  SymPtr sym = NULL;
  ValueT* symval = NULL;

  // (define (a b c) ...)
  if (!issym(symv))
  {
    PairPtr symvpair = Spairref(symv);
    sym = Ssymref(symvpair->car());

    // (lambda (b c) ...)
    vsymval = Sconsref(symvpair->cdr(), pair->cdr());
    vsymval = Sconsref(Sklambda(), vsymval.obj());

    symval = vsymval.obj();
  }

  // (define a 2)
  else
  {
    sym = symref(symv);

    pair = Spairref(pair->cdr());
    symval = pair->car();

    Assert(pair->cdr()->isnull(), "define bad form");
  }

  int offset = -1;
  if (vars != NULL)
  {
    offset = vars->looklocal(sym);
    if (offset < 0)
      offset = vars->addlocal(vm, sym);

    vdef = Sr1(DefLocalVar, offset);
  }
  else
    vdef = Sr1(DefGlobalVar, sym);

  compile(inst, rVal, vars, jf, symval, Snext);

  //  vdef = Sr1(DefVar, offset);
  vdef = vm->list(vdef.obj());
  Sinstvar(definst);
  definst.set(regv(rEnv)|regv(rVal), regv(targetr), pairref(vdef.obj()));

  inst->preserving(regv(rEnv), &definst);
}

void SCompiler::makeset(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* val)
{
  Sgcvar1(vset);

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
        vset = Sr2(SetVarGlobal, sym, targetr);

      else
      {
        offset = vars->addovar(vm, depth, offset);
        vset = Sr2(SetVarUp, offset, targetr);
      }
    }
    else
      vset = Sr2(SetVarUp, offset, targetr);
  }
  else
    vset = Sr2(SetVarLocal, offset, targetr);

  vset = vm->list(vset.obj());

  pair = Spairref(pair->cdr());
  Assert(pair->cdr()->isnull(), "bad set! form");

  compile(inst, rVal, vars, jf, pair->car(), Snext);

  Sinstvar(setinst);
  setinst.set(regv(rEnv)|regv(rVal), regv(targetr), pairref(vset.obj()));

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

  Sgcvar1(ifjmp);
  ifjmp = Sr1(IfFalseJump, &branchfalse);
  jf->toFix(labeli(&branchfalse), ifjmp.obj()->ref());
  ifjmp = vm->list(ifjmp.obj());

  Sinstvar(ifjmpinst);
  ifjmpinst.set(regv(rVal), rvEmpty, pairref(ifjmp.obj()));

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
  Sgcvar1(lambda);

  VarsPtr newvars = Sr1(VarsObj, vars);
  Sgcreserve(newvars);
  VarsProtectShrink(vm, newvars);

  newvars->initparam(vm, pair->car());

  ValueT lambdaentry; setlabel(&lambdaentry);
  ValueT lambdaend; setlabel(&lambdaend);

  lambda = Sr3(LambdaObj, targetr, newvars, &lambdaentry);
  jf->toFix(labeli(&lambdaentry), lambda.obj()->ref());
  lambda = vm->list(lambda.obj());

  inst->set(regv(rEnv), regv(targetr), pairref(lambda.obj()));

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

  Sgcvar1(varg);
  varg = vm->list(&carg);

  Sinstvar(arginst);
  arginst.set(regv(rVal)|regv(rArgl), regv(rArgl), pairref(varg.obj()));

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

  Sgcvar2(compileargs, argv);

  int count = 0;
  for (ValueT* arg = cdrval; !arg->isnull(); arg = Spairref(arg)->cdr())
    count++;

  if (count <= 0)
  {
    Sgcvar1(assign);

    assign = vm->list(&vassignargnull);
    inst->set(rvEmpty, regv(rArgl), pairref(assign.obj()));
  }

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

    Sgcvar1(first);
    first = vm->list(&carg);

    Sinstvar(initinst);
    initinst.set(regv(rVal), regv(rArgl), pairref(first.obj()));

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
    Sgcvar1(assign);
    AssignLabel* jtf;
    assign = jtf = Sr2(AssignLabel, rContinue, link);

    inst->set(regv(rProc), allreg, vm->list(assign.obj(), &vjumpproc));

    jf->toFix(Slabeli(link), jtf);
  }

  else if (targetr != rVal && !isreturn(link))
  {
    Sgcvar3(assign, assignreg, jmp);

    ValueT branchreturn; setlabel(&branchreturn);

    AssignLabel* jtf1;
    JumpLabel *jtf2;
    assign = jtf1 = Sr2(AssignLabel, rContinue, &branchreturn);
    jmp = jtf2 = Sr1(JumpLabel, link);
    assignreg = Sr2(AssignReg, targetr, rVal);

    PairPtr expr = vm->list(assign.obj(),
                            &vjumpproc,
                            &branchreturn,
                            assignreg.obj(),
                            jmp.obj());
    Sgcreserve(expr);

    jf->toFix(labeli(&branchreturn), jtf1);
    jf->toFix(Slabeli(link), jtf2);

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
  Sgcvar2(applyprim, callapp);

  ValueT branchprim; setlabel(&branchprim);
  ValueT branchcompile; setlabel(&branchcompile);
  ValueT aftercall; setlabel(&aftercall);

  CallApp* fjo;
  callapp = fjo = Sr2(CallApp, &branchcompile, &branchprim);
  setinst1v(inst, regv(rProc), rvEmpty, callapp);

  ValueT* compilelink = isnext(link) ? &aftercall : link;

  Sinstvar(lambdainst);
  compilelambdaappl(&lambdainst, jf, targetr, compilelink);
  lambdainst.label(&branchcompile);

  applyprim = Sr1(ApplyPrim, targetr);
  Sinstvar(priminst);
  setinst1v(&priminst, regv(rProc)|regv(rArgl), regv(targetr), applyprim);
  priminst.label(&branchprim);

  endwithlink(jf, &priminst, link);

  inst->append(lambdainst.parallel(&priminst)->labelend(&aftercall));

  jf->toFix(labeli(&branchcompile), fjo);
  jf->toFix(labeli(&branchprim), fjo);
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
    Sgcvar1(assign);

    assign = Sr2(Assign, targetr, pair->cdr());
    assign = vm->list(assign.obj());
    inst->set(rvEmpty, regv(targetr), pairref(assign.obj()));

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
    Sgcvar1(assign);

    assign = Sr2(Assign, targetr, val);
    setinst1v(inst, rvEmpty, targetr, assign);

    endwithlink(jf, inst, link);
  }
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
    Sgcvar1(inst);

    inst = extractlabel(jf, pairref(expr->cdr()));
    int label = labeli(first);

    jf->fix(label, pairref(inst.obj()));

    return pairref(inst.obj());
  }

  else
  {
    PairPtr inst = extractlabel(jf, pairref(expr->cdr()));

    ValueT val;
    setpair(&val, inst);
    expr->cdr(&val);

    return expr;
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
    pair->cdr(val);
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
  GCVar tmp(this);

  VM* vm = this;
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
    tmp = Sr2(RegFrame, saveregptr(cmd)->reg, regs);
    ValueT frm;
    if (frames != NULL)
      setpair(&frm, frames);

    frames = Sconsref(tmp.obj(), &frm);
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
    setvarglobalptr(cmd)->set(regs, getgenv());
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
    regs[rArgl] = regs[rVal];
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
    expr = pairref(pc->cdr());
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

  Debug(Print("realloc mem(%n) -> %p old(%n) -> %p \n", nsize, block, osize, ptr));

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

  Debug(Print("alloc mem(%d) -> %p \n", size, block));

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

Lexer::Lexer(VM* v, const String& in)
  :vm(v), buff(v)
{
  this->input = in;
  this->index = 0;

  init();
}

void Lexer::init()
{
  aheadToken = dLex();
}

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

	if (isEnd())
		return TOKEN_END;

  int token = TOKEN_UNKNOWN;

  switch(curChar()) {
  case '\'':
		token = TOKEN_QUOTE;
    advInput();
    break;
  case '`':
		token = TOKEN_QUASIQUOTE;
    advInput();
		break;
  case ',':
    token = TOKEN_UNQUOTE;
    advInput();
    if (!isEnd() && '@' == curChar())
    {
      token = TOKEN_UNQUOTE_SPLICING;
      advInput();
    }
    break;
  case '"':
    token = readString();
    break;
  case '(':
		token = TOKEN_LEFT_PAREN;
    advInput();
    break;
	case ')':
		token = TOKEN_RIGHT_PAREN;
    advInput();
    break;
  case '[':
		token = TOKEN_LEFT_SQUARE_PAREN;
    advInput();
    break;
	case ']':
		token = TOKEN_RIGHT_SQUARE_PAREN;
    advInput();
    break;
  case '.':
    token = TOKEN_DOT;
    advInput();
    if (!isEnd())
    {
      switch(curChar()){
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
  if(isEnd())
    return;

  switch(curChar()) {
  CASE_BLANK: advInput(); goto loop;
  case ';':
    while(!isEnd() && curChar() != '\n')
      advInput();

    advInput();
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
  if(!isEnd())
  {
		char c = curChar();
    switch(c){
    CASE_BLANK:
    case ')':
      break;
		default:
      buff.put(c);
      advInput();
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

  advInput();

  char c;
  while(!isEnd())
  {
    c = curCharAdv();
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
  if(!isEnd())
  {
    char c = curChar();
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
      advInput();
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

  Sgcvar1(sval);

  while (aheadToken != TOKEN_RIGHT_PAREN &&
         aheadToken != TOKEN_RIGHT_SQUARE_PAREN)
  {
    sval.obj()->reset();

    readValueT(sval.obj());

    if (Sisnull(sval.obj()))
    {
      if (aheadToken == TOKEN_DOT)
      {
        dot = true;

        Assert(!v->isnull(), "dot cannot be the first item");

        match(TOKEN_DOT);

        readValueT(sval.obj());

        Assert(aheadToken == TOKEN_RIGHT_SQUARE_PAREN ||
               aheadToken == TOKEN_RIGHT_PAREN,
               "must have only one item after dot");
        break;
      }
    }

    PairPtr tmp = vm->list(sval.obj());

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
      last = tmp;
    }
  }

  if (dot) last->cdr(sval.obj());
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
    Sgcvar1(v2);
    readValueT(v2.obj());
    setpair(v, Squote_ref(v2.obj()));
    break;
  }
	case TOKEN_UNQUOTE: {
    match(TOKEN_UNQUOTE);
    Sgcvar1(v2);
    readValueT(v2.obj());
    setpair(v, Su_quote_ref(v2.obj()));
    break;
  }
	case TOKEN_QUASIQUOTE: {
    match(TOKEN_QUASIQUOTE);
    Sgcvar1(v2);
    readValueT(v2.obj());
    setpair(v, Sq_quote_ref(v2.obj()));
    break;
  }
	case TOKEN_UNQUOTE_SPLICING: {
    match(TOKEN_UNQUOTE_SPLICING);
    Sgcvar1(v2);
    readValueT(v2.obj());
    setpair(v, Su_quote_s_ref(v2.obj()));
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
