#pragma once

#include "util.h"
#include "dum.h"

namespace Scheme {

static void *salloc(void *ptr, size_t nsize) {
  if (nsize == 0) {
    free(ptr);
    return NULL;
  }
  else
    return realloc(ptr, nsize);
}

struct RefObject;
typedef RefObject* RefPtr;

class PairObj;
typedef PairObj* PairPtr;

struct StrObj;
typedef StrObj* SymPtr;
typedef StrObj* StrPtr;

struct VarsObj;
typedef VarsObj* VarsPtr;

struct EnvObj;
typedef EnvObj* EnvPtr;

struct LambdaObj;
typedef LambdaObj* LambdaPtr;

class Instruction;
typedef Instruction* InstPtr;
class InstArr;

#define Sconsref(a, b) vm->consref(a, b)

#define Sr0(TYPE) vm->newobj<TYPE>()
#define Sr1(TYPE, a) vm->newobj<TYPE>(a)
#define Sr2(TYPE, a, b) vm->newobj<TYPE>(a, b)
#define Sr3(TYPE, a, b, c) vm->newobj<TYPE>(a, b, c)
#define Sr4(TYPE, a, b, c, d) vm->newobj<TYPE>(a, b, c, d)

union BasicNum {
  long i;
  double dbl;
};

union ValueU {
  RefPtr p;
  BasicNum num;
  CFunction f;
};

enum ValueTEnum {
  VT_UNDEFINED, // internal use
  VT_NULL, // nil or null
  VT_NUM_INTEGER,
  VT_NUM_RATIO,

  VT_TRUE,
  VT_FALSE,

  VT_LINK_NEXT,
  VT_LINK_RETURN,

  VT_CFUNCTION,

  VT_LABEL,


  /* all type below must be gcref type */
  VT_REF,
  VT_NUM_REAL,
  VT_NUM_COMPLEX,
  VT_REF_STR,
  VT_REF_SYM,
  VT_REF_PAIR,
};

//#define checkexp(c, e) (Assert(c, "fail to execute %s", #e), (e))
#define checkexp(c, e, TYPE) ((c) ? (e) : (TYPE) Util::throwerror("fail to execute" ## STR(e) ## " because " ## STR(c) ## " test failed"))

/* Link Next Return */
#define isnext(VT) (VT->t == VT_LINK_NEXT)
#define isreturn(VT) (VT->t == VT_LINK_RETURN)

/* SymObj Or StrObj */
#define issym(VT) (VT->t == VT_REF_SYM)
#define symref(VT) (SymPtr)(VT->ref())
#define Ssymref(VT) checkexp(issym(VT), symref(VT), SymPtr)
#define setsym(VT, e) ((VT)->t = VT_REF_SYM, (VT)->v.p = (e))
#define setstr(VT, e) ((VT)->t = VT_REF_STR, (VT)->v.p = (e))

/* Pair */
#define ispair(VT) ((VT)->t == VT_REF_PAIR)
#define pairref(VT) (PairPtr)((VT)->ref())
#define Spairref(VT) checkexp(ispair(VT), pairref(VT), PairPtr)

#define setpair(VT, e)                          \
  { PairPtr pe = e;                             \
    if(pe) {                                    \
      (VT)->t = VT_REF_PAIR;                    \
      (VT)->v.p = pe;                           \
    }}

/* Ref */
#define setref(VT, e)                           \
  { RefPtr pe = e;                              \
    if(pe) {                                    \
      (VT)->t = VT_REF;                         \
      (VT)->v.p = pe;                           \
    }}

/* Num */
#define isnumber(VT) (isnumi(VT) || isnumratio(VT) ||     \
                      isnumreal(VT) || isnumcomplex(VT))

#define setnumi(VT, e) ((VT)->t = VT_NUM_INTEGER, (VT)->v.num.i = e)
#define numi(VT) (VT)->v.num.i
#define isnumi(VT) (VT)->t == VT_NUM_INTEGER

#define setnumratio(VT, e) ((VT)->t = VT_NUM_RATIO, (VT)->v.num.dbl = e)
#define numratio(VT) (VT)->v.num.dbl
#define isnumratio(VT) (VT)->t == VT_NUM_RATIO

#define isnumreal(VT) (VT)->t == VT_NUM_REAL
#define isnumcomplex(VT) (VT)->t == VT_NUM_COMPLEX

#define setnum(VT, t, e) ((VT)->t = t, (VT)->v.num = e)
#define tnum(VT) (VT)->num()
#define Snum(VT) checkexp(isnum(VT), tnum(VT), NumVal)

/* Label */
#define islabel(VT) ((VT)->t == VT_LABEL)
#define labeli(VT) ((VT)->v.num.i)
#define Slabeli(VT) checkexp(islabel(VT), labeli(VT), int)
#define setlabel(VT) ( (VT)->t = VT_LABEL, (VT)->v.num.i = labelmax++ )

/* Null */
#define Sisnull(VT) (VT)->isnull()

/* True or False */
#define Sisfalse(VT) ((VT) == Sfalseref)
#define Sistrue(VT) (!Sisfalse(VT))

/* undefined */
#define isundefined(VT) ((VT)->t == VT_UNDEFINED)
#define setundefined(VT) ((VT)->t = VT_UNDEFINED)

/* CFunction */
#define iscfunction(VT) ((VT)->t == VT_CFUNCTION)
#define setcfunction(VT, f) ((VT)->t = VT_CFUNCTION, (VT)->v.f = f)

#define typet(VT) (VT)->t

struct ValueT {
  ValueU v;
  byte t;

  bool isnull() { return t == VT_NULL; }
  bool isref() { return t >= VT_REF; }

  byte gettype() { return t; }

  RefPtr ref() { return v.p; }
  BasicNum num() { return v.num; }
  CFunction cfunc() { return v.f; }

  ValueT() { reset(); }
  ValueT(int type):ValueT() { t = type; }
  ValueT(const ValueT& rhs):ValueT() {
    t = rhs.t; v = rhs.v;
  }
  ValueT(ValueT* rhs):ValueT() {
    t = rhs->t; v = rhs->v;
  }

  const ValueT& operator = (const ValueT& rhs) {
    t = rhs.t; v = rhs.v;
    return *this;
  }
  void copy(ValueT* rhs) {
    t = rhs->t; v = rhs->v;
  }
  const ValueT& operator = (ValueT* rhs) {
    copy(rhs);
    return *this;
  }

  bool refequal (const ValueT* rhs) const {
    return t == rhs->t && v.p == rhs->v.p;
	}

  void reset() { t = VT_NULL; v.p = NULL; }
};

#define WEAKTAG 0 // object is refered in weak map
#define GROUP0BIT 1 // object is put in group0
#define GROUP1BIT 2 // object is put in group1
#define FULLGCBIT 3 // set 1 when fullgc

#define bitmask(a) (1 << (a))

#define bit0mask bitmask(GROUP0BIT)
#define bit1mask bitmask(GROUP1BIT)
#define fullgcmask bitmask(FULLGCBIT)

#define GCBITS (bit0mask | bit1mask | fullgcmask)

#define GC(vm) (vm)->getgc()
#define Stk(vm) (vm)->getstk()
#define CachePair(vm) (vm)->getcachepair()
#define ObjGroup(vm) (vm)->getobjgroup()
#define Intern(vm) (vm)->getintern()
#define Const(vm) (vm)->getconst()
#define Compiler(vm) (vm)->getcompiler()
#define GEnv(vm) (vm)->getgenv()

#define Check(a) GC(vm)->checkTrace(a)

#define Visit1(a)                               \
  virtual void visit(VM* vm) {                  \
    Check(a);                                   \
  }

#define Visit2(a, b)                            \
  virtual void visit(VM* vm) {                  \
    Check(a);                                   \
    Check(b);                                   \
  }

class VM;

#define GetSize(T) virtual int getsize() { return sizeof(T); }

struct RefObject {
  RefObject() { marked = 0; gcnxt = NULL; }
  virtual ~RefObject() {}

  void markweak() { marked |= (1 << WEAKTAG); }

  bool isgcmark(byte bits) { return bits & marked; }
  void gcmark(byte bit) { marked = (marked & ~GCBITS) | bit; }

  RefPtr link(RefPtr ref) {
    gcnxt = ref;
    return this;
  }

  virtual void visit(VM* vm) {}
  virtual void finz(VM* vm);

  virtual int getsize() = 0;

  RefPtr gcnxt;
  byte marked;
};

struct NumRealObj : public RefObject {
  GetSize(NumRealObj)

  long numerator;
  long denominator;
};

struct NumComplexObj : public RefObject {
  GetSize(NumComplexObj)

  double real;
  double imag;
};

#define objstr(VT) (VT)->str
#define objstrl(VT) (VT)->len
#define objstrh(VT) (VT)->hash

struct StrObj : public RefObject {
  StrObj(const char* s, int n, int h): len(n), hash(h) {
    memcpy(str, s, n);
    str[n] = '\0';
  }

  static int totalsize(int n) {
    return (offsetof(StrObj, str) + sizeof(char*) * ((n) + 1));
  }

  virtual int getsize() { return totalsize(len); }

  int len;
  int hash;

  char str[1];
};

class SGC;

class StackFrame {
public:
  void freez(int v) { vars[v].reset(); frees.write(v); }

  ValueT* alloc(int* v) {
    if (etyidx < VEC_SIZE) { *v = etyidx++; return &vars[*v]; }

    else if (!frees.empty()) {
      *v = frees.read();
      return &vars[*v];
    }

    return NULL;
  }
  bool empty() { return etyidx == 0 || frees.full(); }

  void mark(VM* vm);
protected:
  friend class StackMatrix;

  StackFrame() { etyidx = 0; }
protected:
  static const int VEC_SIZE = 32;
  ValueT vars[VEC_SIZE];

  RingBuf<ushort, VEC_SIZE> frees;

  ushort etyidx;
};

typedef std::vector<StackFrame*> StkFrmVec;

class StackMatrix {
public:
  ValueT* alloc(int* h, int* v);
  void freez(int h, int v);

  void fullmark();
  bool stepmark();

  void startstep() { stkidx = 0; }

protected:
  friend class VM;
  StackMatrix(VM* v) { vm = v; stkidx = 0; }
protected:
  VM* vm;
  StkFrmVec stkvars;
  int stkidx;
};

#define Sinstvar(a) Instruction a (vm);

#define Sgcvar1(a) GCVar a(vm);
#define Sgcvar2(a, b) GCVar a(vm), b(vm);
#define Sgcvar3(a, b, c) Sgcvar2(a, b); Sgcvar1(c);
#define Sgcvar4(a, b, c, d) Sgcvar3(a, b, c); Sgcvar1(d);
#define Sgcvar5(a, b, c, d, e) Sgcvar4(a, b, c, d); Sgcvar1(e);

#define Sgcreserve(ref) gcreserve(vm, ref)
#define gcreserve(vm, ref) GCVar v ## ref ## __LINE__ (vm, ref);

#define vobj(VT) ((VT).object)

class GCVar {
public:
  GCVar(VM* v);
  GCVar(VM* v, RefPtr val): GCVar(v) {
    setref(object, val);
  }

  const GCVar& operator = (RefPtr val) {
    setref(object, val);
    return *this;
  }

  ~GCVar();

  ValueT* object;

protected:
  VM* vm;
  int hori;
  int vert;
};

typedef std::map<RefPtr, int> WeakMap;
typedef WeakMap::iterator WeakMapItr;

struct WeakRef {
  RefPtr obj;
  uint gidx;

  WeakRef(RefPtr p, uint u) { obj = p; gidx = u; }
};

#define Squote_ref(a) Sconsref(Skquote(), (a))
#define Sq_quote_ref(a) Sconsref(Skqquote(), (a))
#define Su_quote_ref(a) Sconsref(Skuquote(), (a))
#define Su_quote_s_ref(a) Sconsref(Skuquotes(), (a))

#define Strueref &ConstVal::strue
#define Sfalseref &ConstVal::sfalse

#define Snullref &ConstVal::snull
#define Sundefined &ConstVal::sundefined
#define Snext &ConstVal::linknext
#define Sreturn &ConstVal::linkreturn

#define Skuquotes() &Const(vm)->uquotes
#define Skuquote() &Const(vm)->uquote
#define Skqquote() &Const(vm)->qquote
#define Skquote() &Const(vm)->quote
#define iskquote(val) val->refequal(Skquote())

#define Skdefine() & Const(vm)->define
#define iskdefine(val) val->refequal(Skdefine())

#define isklambda(val) val->refequal(Sklambda())
#define Sklambda() & Const(vm)->lambda

#define iskset(val) val->refequal(Skset())
#define Skset() & Const(vm)->sset

#define iskbegin(val) val->refequal(Skbegin())
#define Skbegin() & Const(vm)->begin

#define iskif(val) val->refequal(Skif())
#define Skif() & Const(vm)->sif

enum ConstTK {
  CTK_QUOTE,
  CTK_QQUOTE,
  CTK_UQUOTE,
  CTK_UQUOTES,
  CTK_DEFINE,
  CTK_SET,
  CTK_BEGIN,
  CTK_LAMBDA,
  CTK_IF,
  CTK_COND,
  CTK_ELSE,
  CTK_LET,
  CTK_SYNRULES,
  CTK_ELLIP,
  CTK_MAX
};

class ConstVal {
public:
  static ValueT linknext;
  static ValueT linkreturn;

public:
  static ValueT snull;
  static ValueT sundefined;
  static ValueT strue;
  static ValueT sfalse;

  ValueT quote;
  ValueT qquote;
  ValueT uquote;
  ValueT uquotes;
  ValueT define;
  ValueT sset;
  ValueT begin;
  ValueT lambda;
  ValueT sif;
  ValueT cond;
  ValueT selse;
  ValueT let;
  ValueT synrules;
  ValueT ellip;
public:
  RefPtr getconst(const char* str) {
    return getconst(str, strlen(str));
  }

  RefPtr getconst(const char* str, int n);
protected:
  friend class VM;

  ConstVal(VM* v): vm(v) {
    memset(constlst, 0, sizeof(SymPtr*) * CTK_MAX);
  }
  void init();
  RefPtr initConstSym(const char* str);

  SymPtr constlst[CTK_MAX];

  VM* vm;
};

class RefObjGroup {
public:
  void swapobjset() { othIdx = curIdx; curIdx ^= 1; }

  void fullsweep();
  bool stepsweep();

  byte othbit() { return bitmask[othIdx]; }
  byte curbit() { return bitmask[curIdx]; }

  void addrefcur(RefPtr ref) { addref(ref, curIdx); }
  RefPtr recobj(RefPtr ref) {
    recobj(ref, curIdx);
    return ref;
  }

  void unsetfullgcmask() {
    bitmask[0] = bit0mask;
    bitmask[1] = bit1mask;
  }
  void setfullgcmask() {
    bitmask[0] = fullgcmask | bit0mask;
    bitmask[1] = fullgcmask | bit1mask;
  }

protected:
  template<class Ptr>
  Ptr recobj(Ptr ref, int idx) {
    addref(ref, idx);
    ref->gcmark(bitmask[idx]);
    return ref;
  }
  void addref(RefPtr ref, int idx) { gclst[idx] = ref->link(gclst[idx]); }

  friend class VM;
  RefObjGroup(VM* v) {
    vm = v;

    gclst[0] = NULL;
    gclst[1] = NULL;

    bitmask[0] = bit0mask;
    bitmask[1] = bit1mask;

    curIdx = 0;
    othIdx = 1;
  }
protected:
  VM* vm;

  static const int SIZE = 2;

  RefPtr gclst[SIZE];
  byte bitmask[SIZE];

  byte curIdx;
  byte othIdx;
};

class CachePairObj {
public:
  void addref(PairPtr ref);

  PairPtr getone();
  void fullsweep();
protected:
  friend class VM;
  CachePairObj(VM* v): vm(v) { cache = NULL; }
protected:
  VM* vm;
  PairPtr cache;
};

enum GCState {
  GCSNone,
  GCSMarkStk,
  GCSMarkReg,
  GCSMarkFrame,
  GCSMarkGray,
  GCSSweepObjGroup,
  GCSSweepInterns,
  GCSSweepEnd,
  GCSEnd,
};

class SGC {
public:
  typedef void (SGC::*TouchChild)(ValueT* v);
protected:
  TouchChild touchf;

  void addchildgraylst(ValueT* ref);
  void visitchild(ValueT* ref) { ref->ref()->visit(vm); }
public:
  void stepfullgc();

  void singlestep();

  void checkTrace(ValueT v) { checkTrace(&v); }
  void checkTrace(ValueT* v);
  void checkTrace(RefPtr ptr) {
    ValueT ref;
    setref(&ref, ptr);
    checkTrace(&ref);
  }

  void startstep();

  // perform a complete gc
  void fullgc();

  void toDel(RefPtr ref);

public:
  void debt(long size) { debtbytes = size; }
  long debt() { return debtbytes; }
  long gettotalbytes() { return selfbytes + debtbytes; }
  void setselfbytes(int s) { selfbytes = s; }
  //
  long debtbytes;
  long selfbytes;
protected:
  bool markgray();

  void sweepgray();
  void clearDel();

  friend class VM;
  SGC(VM* v) {
    vm = v;
    state = GCSNone;
    toDelLst = NULL;
    graylstLast = graylst = NULL;
    touchf = NULL;
    debtbytes = 0;
    selfbytes = 0;
  }
protected:
  VM* vm;

  int state;

  PairPtr graylst;
  PairPtr graylstLast;

  RefPtr toDelLst;
};

class Interns {
public:
  SymPtr intern(const char* str) { return intern(str, strlen(str)); }
  SymPtr intern(const char* str, int n);

  void checkResize();

  void fullsweep();
  bool stepsweep();

  void startstep() { bidx = 0; }

protected:
  void rehash(int oldl, int newl);

  friend class VM;
  Interns(VM* v);
  ~Interns();
  void init();

protected:
  VM* vm;

  const static int INIT_LEN = 128;

  // used in step sweep state
  int bidx;

  SymPtr* bucketlist;
  int blistlen;
  int bcount;
};

#define rvEmpty    (0)

enum Reg {
  rEnv = 0,
  rProc,
  rVal,
  rArgl,
  rContinue,
  rMax
};


#define allreg ((1 << rMax) - 1)
#define regv(r) (1 << (r))

#define vjtf(VT) (JumpToFix*)vobj(VT)

struct JumpToFix {
  JumpToFix(VM* v, int n): vm(v) {
    startlabel = n;
    arrToFix = NULL;
    size = 0;
  }
  ~JumpToFix();

  VM* vm;
  int startlabel;
  PairPtr* arrToFix;
  int size;

  void toFix(int label, RefPtr v);

  void fix(int label, PairPtr jmp);
};

class SCompiler {
public:
  PairPtr compile(ValueT* val);
  void compile(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* val, ValueT* link);
  void compilesym(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, SymPtr sym, ValueT* link);
  void compilepair(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, PairPtr val, ValueT* link);
  void compilelink(InstPtr inst, JumpToFix* jf, ValueT* link);
  void compileseq(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, PairPtr val, ValueT* link);

  void endwithlink(JumpToFix* jf, InstPtr inst, ValueT* link);

  void compileappcall(InstPtr inst, JumpToFix* jf, int targetr, ValueT* link);
  void compilelambdaappl(InstPtr inst, JumpToFix* jf, int targetr, ValueT* link);

  void makelambda(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, PairPtr val, ValueT* link);
  void makeiftest(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, PairPtr val, ValueT* link);
  void makedef(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* val);
  void makeset(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* val);
  void makeapp(InstPtr inst, int targetr, VarsPtr vars, JumpToFix* jf, ValueT* type, ValueT* cdrval, ValueT* link);
  void constructarg(InstPtr inst, VarsPtr vars, JumpToFix* jf, ValueT* cdrval);

protected:
  PairPtr extractlabel(JumpToFix* jf, PairPtr expr);
  void constructarg0(InstPtr inst, InstArr* iarr, int idx);

protected:
  friend class VM;
  SCompiler(VM* v): vm(v) { labelmax = 1; }

protected:
  VM* vm;

  int labelmax;
};

#define twoto(x)	(1<<(x))

struct TSlot {
  TSlot() { tv = NULL; next = NULL; }
  void settv(PairPtr p) { tv = p; }

  PairPtr tv;
  TSlot* next;
};

class GSymTable {
public:
  static const int MINLTSIZE = 4;
  PairPtr getslot(SymPtr sym);
  void getval(SymPtr sym, ValueT* v);
  void newkey(SymPtr sym, ValueT* val);
  void newkeyorupdate(SymPtr sym, ValueT* val);
protected:
  GSymTable(VM* v):vm(v) {}

  void init();
  TSlot* getpos(SymPtr sym);
  TSlot* getfreepos();
  void rehash();
  void insert(SymPtr sym, PairPtr tv);
protected:
  friend class VM;
  VM* vm;

  byte lsizenode;
  TSlot* slots;
  TSlot* lastfree;
};

class VM {
public:
  static VM* newVM() { return newVM(salloc); }
  static VM* newVM(ScmAlloc p);
  static void delVM(VM* v);

  void regCFunction(const char* name, CFunction f);
protected:
  void stepmarkregs();
  void stepmarkframes();
  void regfullmark();
  void checkgc();
protected:
  ValueT regs[rMax];

  PairPtr frames;
protected:
  void eval(ValueT* out, PairPtr expr);
protected:
  ScmAlloc frealloc;
  StrObj* newstr(const char* str, int len, int h);

public:
  template<class T, class P1, class P2, class P3>
  T* newobj(P1 p1, P2 p2, P3 p3) {
    return (T*)getobjgroup()->recobj(new (alloc(sizeof(T))) T (p1, p2, p3));
  }

  template<class T, class P1, class P2>
  T* newobj(P1 p1, P2 p2) {
    return (T*)getobjgroup()->recobj(new (alloc(sizeof(T))) T (p1, p2));
  }

  template<class T, class P1>
  T* newobj(P1 p1) {
    return (T*)getobjgroup()->recobj(new (alloc(sizeof(T))) T (p1));
  }

  PairPtr list(ValueT* a) {
    return consref(a, Snullref);
  }
  PairPtr list(ValueT* a, ValueT* b);
  PairPtr list(ValueT* a, ValueT* b, ValueT* c);
  PairPtr list(ValueT* a, ValueT* b, ValueT* c, ValueT* d);
  PairPtr list(ValueT* a, ValueT* b, ValueT* c, ValueT* d, ValueT* e);

public:
  void* alloc(size_t size);
  void* realloc(void* ptr, size_t osize, size_t nsize);
  void free(void* ptr, size_t size) {
    frealloc(ptr, 0);
    long debt = getgc()->debt();
    getgc()->debt(debt - size);
  }

  PairPtr consref(ValueT* h, ValueT* t);
  PairPtr getonepairnor();

  static const int MAXSHORTLEN = 40;
  StrObj* stringref(const char* str, int len);

public:
  // TODO: add weak feature
  void rmWeak(RefPtr ref) {
    WeakMapItr itr = weaks.find(ref);
    weaks.erase(itr);
  }

public:
  StackMatrix* getstk() { return &stk; }
  CachePairObj* getcachepair() { return &cachePair; }
  SGC* getgc() { return &gc; }
  RefObjGroup* getobjgroup() { return &objGroup; }
  Interns* getintern() { return &intern; }
  ConstVal* getconst() { return &consts; }
  SCompiler* getcompiler() { return &compiler; }
  GSymTable* getgenv() { return &genv; }
public:
  void makeseed();
  int seed;
protected:
  VM(ScmAlloc a);
  void init();
protected:
  uint weakIdx;
  WeakMap weaks;

protected:
  StackMatrix stk;
  RefObjGroup objGroup;
  CachePairObj cachePair;

  friend class SGC;
  SGC gc;

  SCompiler compiler;

  friend class Interns;
  Interns intern;

  friend class ConstVal;
  ConstVal consts;

  GSymTable genv;
};

#define frameref(VT) ((RegFrame*)(VT)->ref())

struct RegFrame : public RefObject {
  RegFrame(int r, ValueT rs[rMax]);

  void restore(ValueT regs[rMax]);

  virtual void visit(VM* vm) {
    for (int i = 0; i < rMax; i++)
      Check(regval[i]);
  }

  GetSize(RegFrame)

  int regs;
  ValueT regval[rMax];
};

class PairObj : public RefObject {
public:
  PairObj(ValueT* h, ValueT* t): scar(*h), scdr(*t) { }

  ValueT* car() { return &scar; }
  ValueT* cdr() { return &scdr; }

  void car(ValueT* obj) { scar = obj; }
  void cdr(ValueT* obj) { scdr = obj; }

  virtual void finz(VM* vm);

  Visit2(scar, scdr)

  GetSize(PairObj)

protected:
  friend class VM;
  PairObj() {}
protected:
  ValueT scar;
  ValueT scdr;
};

struct OuterVar {
  SymPtr name;
  int depth;
  int idx;

  OuterVar(): name(NULL), depth(-1), idx(-1) {}
  OuterVar(int d, int i): name(NULL), depth(d), idx(i) {}
};

#define jumpobjref(VT) ((FixJumpObj*)(VT)->ref())

struct FixJumpObj {
  virtual void fixJmp(int label, PairPtr dest) = 0;
};

#define execmdref(VT) (ExeCmd*)(VT)->ref()

struct ExeCmd {
  virtual int getcmd() = 0;
};

enum ExeCmdEnum {
  CMD_ASSIGN,
  CMD_LAMBDA,
  CMD_ASSIGN_REG,
  CMD_JUMP_PROC,
  CMD_JUMP_CONTINUE,
  CMD_JUMP_LABEL,
  CMD_SAVE_REG,
  CMD_RESTORE_REG,

  CMD_REF_LOCAL,
  CMD_REF_UP,
  CMD_REF_GLOBAL,

  CMD_DEF_LOCAL,
  CMD_DEF_GLOBAL,

  CMD_SET_LOCAL,
  CMD_SET_UP,
  CMD_SET_GLOBAL,

  CMD_IF_FALSE_JUMP,
  CMD_INIT_ARG,
  CMD_APPLY_PRIM,
  CMD_CALL_APP,
  CMD_CONS_ARG,
};


#define setinst1v(inst, r, m, v) \
  (v = vm->list(vobj(v)), (inst)->set(r, m, pairref(vobj(v))))

class Instruction {
public:
  Instruction(VM* v):vm(v), var(v) { set(rvEmpty, rvEmpty, NULL); }

  void set(int n, int m, PairPtr v) {
    rneed = n, rmod = m;
    var = expr = v;
  }

  const Instruction& operator = (InstPtr rhs) {
    rneed = rhs->rneed, rmod = rhs->rmod;
    setexpr(rhs->expr);
    return *this;
  }

  InstPtr append(InstPtr ptr);
  InstPtr parallel(InstPtr ptr);
  InstPtr tack(InstPtr ptr);

  InstPtr preserving(int regs, InstPtr i2);
  void saverestore(int sr);
  void label(ValueT* label);
  InstPtr labelend(ValueT* label);

  void endwithpair(PairPtr p2);

  void setexpr(PairPtr e) { var = expr = e; }

  int rneed;
  int rmod;
  PairPtr expr;

  GCVar var;
  VM* vm;
};

class InstArr {
public:
  InstArr(VM* v, int c): vm(v), count(c) {
    arr = (InstPtr)vm->alloc(sizeof(Instruction) * c);
    for (int i = 0; i < c; i++) {
      new (&arr[i]) Instruction(vm);
    }
  }
  ~InstArr() {
    for (int i = 0; i < count; i++) {
      arr[i].~Instruction();
    }
    vm->free(arr, sizeof(Instruction) * count);
  }

  InstPtr geti(int i) { return &arr[i]; }

  VM* vm;
  int count;
  InstPtr arr;
};

#define varsref(VT) (VarsPtr)((VT)->ref())

struct VarsObj : public RefObject {
  VarsObj(VarsObj* o):
    outer(o), local(NULL), nlocal(0), sizelocal(0),
    ovar(NULL), novar(0), sizeovar(0) {}

  void initparam(VM* vm, ValueT* param);
  int addovar(VM* vm, int depth, int idx);
  int addlocal(VM* vm, SymPtr sym);
  int looklocal(SymPtr sym);
  int lookovar(SymPtr sym);
  int lookouter(SymPtr sym, int* depth);

  void shrink(VM* vm);

  virtual void visit(VM* vm);
  virtual void finz(VM* vm);

  GetSize(VarsObj)

  VarsObj* outer;

  SymPtr* local;
  int nlocal;
  int sizelocal;

  OuterVar* ovar;
  int novar;
  int sizeovar;
};

#define lambdaptr(VT) ((LambdaPtr)(VT))

struct LambdaObj : public RefObject, public FixJumpObj, public ExeCmd {
  LambdaObj(int r, VarsPtr v, ValueT* e): targetr(r), vars(v), entry(*e) {
  }

  virtual int getcmd() { return CMD_LAMBDA; }

  virtual void fixJmp(int label, PairPtr dest) {
    Assert(islabel(&entry) && labeli(&entry) == label, "label error");
    setpair(&entry, dest);
  }

  ValueT* getentry() { return &entry; }

  Visit2(vars, entry)

  GetSize(LambdaObj)

  byte targetr;
  VarsPtr vars;
  ValueT entry;
};

#define envref(VT) (EnvObj*)(VT)->ref()

struct EnvObj : public RefObject {
  EnvObj(EnvObj* o, VarsPtr v):outer(o), vars(v) {
    locals = NULL, nlocal = 0;
    outers = NULL, nout = 0;
  }

  void initlocalout(VM* vm, VarsPtr vars);
  void extend(VM* vm, ValueT regs[rMax], ValueT* argl);

  GetSize(EnvObj)

  virtual void visit(VM* vm);
  virtual void finz(VM* vm);

  EnvObj* outer;
  VarsPtr vars;

  ValueT* locals;
  int nlocal;

  ValueT** outers;
  int nout;
};

#define closureptr(VT) ((ClosureObj*)VT)

struct ClosureObj : public RefObject {
  ClosureObj(EnvPtr e, LambdaPtr l): env(e), lambda(l) {}

  LambdaPtr getlambda() { return lambda; }

  Visit2(env, lambda)
  GetSize(ClosureObj)

  EnvPtr env;
  LambdaPtr lambda;
};
typedef ClosureObj* ClosurePtr;

#define assignptr(VT) ((Assign*)(VT))

struct Assign : public RefObject, public ExeCmd {
  Assign(int r, ValueT* v): reg(r), val(*v) {}

  virtual int getcmd() { return CMD_ASSIGN; }

  void assignreg(ValueT regs[rMax]) {
    regs[reg] = val;
  }

  Visit1(val)
  GetSize(Assign)

  byte reg;
  ValueT val;
};

struct AssignLabel : public Assign, public FixJumpObj {
  AssignLabel(int r, ValueT* v): Assign(r, v) {}

  virtual void fixJmp(int label, PairPtr dest) {
    Assert(islabel(&val) && labeli(&val) == label, "label error");
    setpair(&val, dest);
  }
};

#define assignregptr(VT) ((AssignReg*)(VT))

struct AssignReg : public RefObject, public ExeCmd {
  AssignReg(int d, int s): dst(d), src(s) {}

  virtual int getcmd() { return CMD_ASSIGN_REG; }

  void assignreg(ValueT regs[rMax]) {
    regs[dst] = regs[src];
  }

  GetSize(AssignReg)

  int dst;
  int src;
};

struct JumpProc : public RefObject, public ExeCmd {
  virtual int getcmd() { return CMD_JUMP_PROC; }
  GetSize(JumpProc)
};

struct JumpContinue : public RefObject, public ExeCmd {
  virtual int getcmd() { return CMD_JUMP_CONTINUE; }
  GetSize(JumpContinue)
};

#define jumplabelptr(VT) ((JumpLabel*)(VT))

struct JumpLabel : public RefObject, public FixJumpObj, public ExeCmd {
  JumpLabel(ValueT* v): entry(*v) {}

  virtual int getcmd() { return CMD_JUMP_LABEL; }

  virtual void fixJmp(int label, PairPtr dest) {
    Assert(islabel(&entry) && labeli(&entry) == label, "label error");
    setpair(&entry, dest);
  }

  Visit1(entry)
  GetSize(JumpLabel)

  ValueT entry;
};

#define saveregptr(VT) ((SaveReg*)(VT))

struct SaveReg : public RefObject, public ExeCmd {
  SaveReg(int r): reg(r) {}

  virtual int getcmd() { return CMD_SAVE_REG; }

  GetSize(SaveReg)

  byte reg;
};

#define restoreregptr(VT) ((RestoreReg*)(VT))

struct RestoreReg : public RefObject, public ExeCmd {
  RestoreReg(int r): reg(r) {}

  virtual int getcmd() { return CMD_RESTORE_REG; }
  GetSize(RestoreReg)

  byte reg;
};

#define reflocalptr(VT) ((RefLocalVar*)(VT))

struct RefLocalVar : public RefObject, public ExeCmd {
  RefLocalVar(int r, int off) : reg(r), offset(off) {}

  virtual int getcmd() { return CMD_REF_LOCAL; }

  void ref(ValueT regs[rMax], EnvPtr env) {
    ValueT* val = &env->locals[offset];

    Assert(!isundefined(val), "undefined local variable %s", objstr(env->vars->local[offset]));
    regs[reg] = val;
  }

  GetSize(RefLocalVar)

  byte reg;
  int offset;
};

#define refupptr(VT) ((RefUpVar*)(VT))

struct RefUpVar : public RefObject, public ExeCmd {
  RefUpVar(int r, int oi) :
    reg(r), oidx(oi) {}

  virtual int getcmd() { return CMD_REF_UP; }

  void ref(ValueT regs[rMax], EnvPtr env) {
    ValueT* val = env->outers[oidx];

    OuterVar* ov = &env->vars->ovar[oidx];
    Assert(!isundefined(val), "undefined local variable %s", objstr(ov->name));
    regs[reg] = val;
  }

  GetSize(RefUpVar)

  byte reg;
  int oidx;
};

#define refglobalptr(VT) ((RefGlobalVar*)(VT))

struct RefGlobalVar : public RefObject, public ExeCmd {
  RefGlobalVar(int r, SymPtr p) :
    reg(r), var(p) {}

  virtual int getcmd() { return CMD_REF_GLOBAL; }

  void ref(ValueT regs[rMax], GSymTable* genv) {
    ValueT val;
    genv->getval(var, &val);

    Assert(!isundefined(&val), "undefined global variable %s", objstr(var));
    regs[reg] = val;
  }

  Visit1(var)
  GetSize(RefGlobalVar)

  byte reg;
  SymPtr var;
};

#define defglobalptr(VT) ((DefGlobalVar*)(VT))

struct DefGlobalVar : public RefObject, public ExeCmd {
  DefGlobalVar(SymPtr v): var(v) {}

  virtual int getcmd() { return CMD_DEF_GLOBAL; }

  void def(ValueT regs[rMax], GSymTable* genv) {
    genv->newkeyorupdate(var, &regs[rVal]);
  }

  Visit1(var)
  GetSize(DefGlobalVar)

  SymPtr var;
};

#define deflocalptr(VT) ((DefLocalVar*)(VT))

struct DefLocalVar : public RefObject, public ExeCmd {
  DefLocalVar(int off): offset(off) {}

  virtual int getcmd() { return CMD_DEF_LOCAL; }

  void def(ValueT regs[rMax], EnvPtr env) {
    env->locals[offset] = &regs[rVal];
  }

  GetSize(DefLocalVar)

  int offset;
};

#define setvarlocalptr(ptr) ((SetVarLocal*)(ptr))

struct SetVarLocal : public RefObject, public ExeCmd {
  SetVarLocal(int off, int r): reg(r), offset(off) {}

  virtual int getcmd() { return CMD_SET_LOCAL; }

  void set(ValueT regs[rMax], EnvPtr env) {
    env->locals[offset] = &regs[rVal];
    setundefined(&regs[reg]);
  }

  GetSize(SetVarLocal)

  int offset;
  byte reg;
};

#define setvarupptr(ptr) ((SetVarUp*)(ptr))

struct SetVarUp : public RefObject, public ExeCmd {
  SetVarUp(int off, int r): reg(r), offset(off) {}

  virtual int getcmd() { return CMD_SET_UP; }

  void set(ValueT regs[rMax], EnvPtr env) {
    env->outers[offset]->copy(&regs[rVal]);
    setundefined(&regs[reg]);
  }

  GetSize(SetVarUp)

  int offset;
  byte reg;
};

#define setvarglobalptr(ptr) ((SetVarGlobal*)(ptr))

struct SetVarGlobal : public RefObject, public ExeCmd {
  SetVarGlobal(SymPtr p, int r): reg(r), var(p) {}

  virtual int getcmd() { return CMD_SET_GLOBAL; }

  void set(ValueT regs[rMax], GSymTable* genv) {
    PairPtr pair = genv->getslot(var);
    Assert(pair, "undefined global variable %s", objstr(var));

    pair->cdr(&regs[rVal]);
    setundefined(&regs[reg]);
  }

  Visit1(var)
  GetSize(SetVarGlobal)

  SymPtr var;
  byte reg;
};

#define iffalsejumpptr(ptr) ((IfFalseJump*)ptr)

struct IfFalseJump : public RefObject, public FixJumpObj, public ExeCmd {
  IfFalseJump(ValueT* jump): entry(*jump) {}

  virtual int getcmd() { return CMD_IF_FALSE_JUMP; }

  virtual void fixJmp(int label, PairPtr dest) {
    Assert(islabel(&entry) && labeli(&entry) == label, "label error");
    setref(&entry, dest);
  }

  Visit1(entry)
  GetSize(IfFalseJump)

  ValueT entry;
};

struct InitArg : public RefObject, public ExeCmd {
  virtual int getcmd() { return CMD_INIT_ARG; }
  GetSize(InitArg)
};

#define applyprimptr(VT) ((ApplyPrim*)(VT))

struct ApplyPrim : public RefObject, public ExeCmd {
  ApplyPrim(int r): targetr(r) {}

  virtual int getcmd() { return CMD_APPLY_PRIM; }
  GetSize(ApplyPrim)

  byte targetr;
};

#define callappptr(VT) ((CallApp*)(VT))

struct CallApp : public RefObject, public FixJumpObj, public ExeCmd {
  CallApp(ValueT* l1, ValueT* l2):lproc(*l1), lprim(*l2) {}

  virtual int getcmd() { return CMD_CALL_APP; }

  virtual void fixJmp(int label, PairPtr dest) {
    Assert(islabel(&lproc) && islabel(&lprim), "label error");
    if (labeli(&lproc) == label) {
      setpair(&lproc, dest);
    } else if (labeli(&lprim) == label) {
      setpair(&lprim, dest);
    } else {
      Error("label error %d", label);
    }
  }

  Visit2(lproc, lprim)
  GetSize(CallApp)

  ValueT lproc;
  ValueT lprim;
};

struct ConsArg : public RefObject, public ExeCmd {
  virtual int getcmd() { return CMD_CONS_ARG; }
  GetSize(ConsArg)
};

struct Lbuffer {
  static const int INIT_LEN = 128;

  VM* vm;

  char* buf;
  int size;
  int count;

  Lbuffer(VM* v):vm(v) {
    size = INIT_LEN;
    count = 0;
    buf = (char*)vm->alloc(INIT_LEN);
  }
  ~Lbuffer() {
    vm->free(buf, size);
    buf = NULL;
    size = 0;
    count =0;
  }

  void put(char c) {
    if (count + 1 >= size) {
      int ns = size * 2;
      buf = (char*)vm->realloc(buf, size, ns);
      size = ns;
    }
    buf[count++] = c;
  }
  void reset() { count = 0; }
};

class Lexer {
public:
  Lexer(VM* v, const String& in);

  void readOne(ValueT* v);
protected:
  bool isEnd() { return index >= input.size(); }
  int readNum();
  int readString();
  int readSymbol(char init);
  int readSymbol();

  void match(int type);
  void readValueT(ValueT* v);
  void readListT(ValueT* v);
  void init();

  char curCharAdv() { return input[index++]; }
  char curChar() { return input[index]; }
  void advInput() { ++index; }

  void skipBlankComment();
  int dLex();
protected:
  VM* vm;

	int aheadToken;
  int readI;
  Lbuffer buff;

	int index;
	String input;
};

};
