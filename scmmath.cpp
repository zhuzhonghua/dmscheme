#include "vm.h"
#include "scmmath.h"

namespace Scheme {

static scm_int Sgcd(scm_int a, scm_int b)
{
  a = std::abs(a);
  b = std::abs(b);

  while (b != 0)
  {
    scm_int tmp = a % b;
    a = b;
    b = tmp;
  }

  return a;
}

static scm_int Slcm(scm_int a, scm_int b)
{
  return std::abs(Sgcd(a, b) * a * b);
}

static void numuptoratio(VM* vm, ValueT* a)
{
  Assert(isnumi(a), "wrong up type %d", typet(a));
  scm_int si = numi(a);
  setnumratio(a, Sr2(NumRatioObj, si, 1));
}

static void numuptoreal(ValueT* a)
{
  if (isnumi(a))
  {
    scm_int si = numi(a);
    setnumreal(a, si);
  }

  else if (isnumratio(a))
  {
    NumRatioObj* ratio = ratioref(a);
    setnumreal(a, ratio->numerator / (double)ratio->denominator);
  }

  else
    Error("numuptoreal wrong up type %d", typet(a));
}

static void numtocomplex(VM*vm, ValueT* a)
{
  if (isnumi(a))
  {
    scm_int si = numi(a);
    setnumcomplex(a, Sr2(NumComplexObj, si, 0));
  }

  else if (isnumratio(a))
  {
    double sd = numrationu(a) / (double)numratiode(a);
    setnumcomplex(a, Sr2(NumComplexObj, sd, 0));
  }

  else if (isnumreal(a))
  {
    double sd = numreal(a);
    setnumcomplex(a, Sr2(NumComplexObj, sd, 0));
  }

  else
    Error("numuptocomplex wrong up type %d", typet(a));
}

static void numsynctype(VM* vm, ValueT* a1, ValueT* a2, ValueT* a1p, ValueT* a2p)
{
  *a1 = a1p;
  *a2 = a2p;

  if (typet(a1) == typet(a2)) return;

  switch(typet(a1)) {
  case VT_NUM_INTEGER:
    switch(typet(a2)) {
    case VT_NUM_RATIO: numuptoratio(vm, a1); break;
    case VT_NUM_REAL: numuptoreal(a1); break;
    case VT_NUM_COMPLEX: numtocomplex(vm, a1); break;
    }
    break;
  case VT_NUM_RATIO:
    switch(typet(a2)) {
    case VT_NUM_INTEGER: numuptoratio(vm, a2); break;
    case VT_NUM_REAL: numuptoreal(a1); break;
    case VT_NUM_COMPLEX: numtocomplex(vm, a1); break;
    }
    break;
  case VT_NUM_REAL:
    switch(typet(a2)) {
    case VT_NUM_INTEGER: numuptoreal(a2); break;
    case VT_NUM_RATIO: numuptoreal(a2); break;
    case VT_NUM_COMPLEX: numtocomplex(vm, a1); break;
    }
    break;
  case VT_NUM_COMPLEX:
    switch(typet(a2)) {
    case VT_NUM_INTEGER: numtocomplex(vm, a2); break;
    case VT_NUM_RATIO: numtocomplex(vm, a2); break;
    case VT_NUM_REAL: numtocomplex(vm, a2); break;
    }
    break;
  }
}

static void numadd(VM* vm, ValueT* out, ValueT* a1, ValueT* a2)
{
  GCVar a1p(vm), a2p(vm);
  numsynctype(a1p.obj(), a2p.obj(), a1, a2);
  a1 = a1p.obj(), a2 = a2p.obj();

  switch(typet(a1)) {
  case VT_NUM_INTEGER:
    setnumi(out, numi(a1) + numi(a2));
    break;
  case VT_NUM_RATIO:{
    scm_int de = Slcm(numratiode(a1), numratiode(a2));
    scm_int dp1 = de / numratiode(a1);
    scm_int dp2 = de / numratiode(a2);
    setnumratio(a, Sr2(NumRatioObj, numrationu(a1) * dp1 + numrationu(a2) * dp2, de));
    break;
  }
  case VT_NUM_REAL:
    setnumreal(out, numreal(a1) + numreal(a2));
    break;
  case VT_NUM_COMPLEX:
    setnumcomplex(out, Sr2(NumComplexObj,
                           numcomplexreal(a1) + numcomplexreal(a2),
                           numcompleximag(a1) + numcompleximag(a2)));
    break;
  }
}

static void numsubtract(VM* vm, ValueT* out, ValueT* a1, ValueT* a2)
{
  GCVar a1p(vm), a2p(vm);
  numsynctype(a1p.obj(), a2p.obj(), a1, a2);
  a1 = a1p.obj(), a2 = a2p.obj();

  switch(typet(a1)) {
  case VT_NUM_INTEGER:
    setnumi(out, numi(a1) - numi(a2));
    break;
  case VT_NUM_RATIO:{
    scm_int de = Slcm(numratiode(a1), numratiode(a2));
    scm_int dp1 = de / numratiode(a1);
    scm_int dp2 = de / numratiode(a2);
    setnumratio(a, Sr2(NumRatioObj, numrationu(a1) * dp1 - numrationu(a2) * dp2, de));
    break;
  }
  case VT_NUM_REAL:
    setnumreal(out, numreal(a1) - numreal(a2));
    break;
  case VT_NUM_COMPLEX:
    setnumcomplex(out, Sr2(NumComplexObj,
                           numcomplexreal(a1) - numcomplexreal(a2),
                           numcompleximag(a1) - numcompleximag(a2)));
    break;
  }
}

static void nummultiply(VM* vm, ValueT* out, ValueT* a1, ValueT* a2)
{
  GCVar a1p(vm), a2p(vm);
  numsynctype(a1p.obj(), a2p.obj(), a1, a2);
  a1 = a1p.obj(), a2 = a2p.obj();

  switch(typet(a1)) {
  case VT_NUM_INTEGER:
    setnumi(out, numi(a1) * numi(a2));
    break;
  case VT_NUM_RATIO:
    setnumratio(a, Sr2(NumRatioObj,
                       numrationu(a1) * numrationu(a2) ,
                       numratiode(a1) * numratiode(a2)));
    break;
  case VT_NUM_REAL:
    setnumreal(out, numreal(a1) * numreal(a2));
    break;
  case VT_NUM_COMPLEX: {
    double re1 = numcomplexreal(a1), re2 = numcomplexreal(a2);
    double ig1 = numcompleximag(a1), ig2 = numcompleximag(a2);
    setnumcomplex(out, Sr2(NumComplexObj, (re1 * re2 - ig1 * ig2), re1 * ig2 + ig1 * re2));
    break;
  }
  }
}


static void numdivide(VM* vm, ValueT* out, ValueT* a1, ValueT* a2)
{
  GCVar a1p(vm), a2p(vm);
  numsynctype(a1p.obj(), a2p.obj(), a1, a2);
  a1 = a1p.obj(), a2 = a2p.obj();

  switch(typet(a1)) {
  case VT_NUM_INTEGER: {
    if (0 == numi(a1) % numi(a2))
      setnumi(out, numi(a1) / numi(a2));

    else
    {
      scm_int gd = Sgcd(numi(a1), numi(a2));
      setnumratio(a, Sr2(NumRatioObj, numi(a1) / gd, numi(a2) / gd));
    }
    break;
  }
  case VT_NUM_RATIO:
    setnumratio(a, Sr2(NumRatioObj,
                       numrationu(a1) * numratiode(a2) ,
                       numratiode(a1) * numrationu(a2)));
    break;
  case VT_NUM_REAL:
    setnumreal(out, numreal(a1) / numreal(a2));
    break;
  case VT_NUM_COMPLEX: {
    double re1 = numcomplexreal(a1), re2 = numcomplexreal(a2);
    double ig1 = numcompleximag(a1), ig2 = numcompleximag(a2);

    double de = std::sqrt(ig1) + std::sqrt(ig2);
    double realnu = re1 * re2 + ig1 * ig2, imagnu = ig1 * re2 - re1 * ig2;
    setnumcomplex(out, Sr2(NumComplexObj, realnu / de, imagnu / de));
    break;
  }
  }
}

#define regc(NAME, TYPE, FUNC) vm->regCFunction(NAME, TYPE ## :: ## FUNC);

void ScmMath::init(VM* vm)
{
  regc("+", ScmMath, add);
  regc("-", ScmMath, subtract);
  regc("*", ScmMath, multiply);
  regc("/", ScmMath, divide);
  regc("gcd", ScmMath, gcd);
  regc("lcm", ScmMath, lcm);
  regc("numerator", ScmMath, numerator);
  regc("denominator", ScmMath, denominator);
  regc("number?", ScmMath, numberp);
  regc("complex?", ScmMath, complexp);
  regc("real?", ScmMath, realp);
  regc("rational?", ScmMath, rationalp);
  regc("integer?", ScmMath, integerp);
}

void ScmMath::numerator(VM* vm, ValueT* out, ValueT* args)
{
  PairPtr pair = Spairref(args);
  ValueT* n = pair->car();

  Assert(isnumratio(n), "numerator not a ratio %d", typet(n));
  Assert(Sisnull(pair->cdr()), "numerator need only one arg");

  setnumi(out, numrationu(n));
}

void ScmMath::denominator(VM* vm, ValueT* out, ValueT* args)
{
  PairPtr pair = Spairref(args);
  ValueT* n = pair->car();

  Assert(isnumratio(n), "denominator not a ratio %d", typet(n));
  Assert(Sisnull(pair->cdr()), "denominator need only one arg");

  setnumi(out, numratiode(n));
}

void ScmMath::add(VM* vm, ValueT* out, ValueT* args)
{
  if (Sisnull(args))
    setnumi(out, 0);

  else
  {
    PairPtr pair = Spairref(args);
    ValueT* n = pair->car();
    Assert(isnumber(n), "add not a number %d", typet(n));

    *out = n;
    GCVar out2(vm);

    for (args = pair->cdr(); !Sisnull(args); args = pair->cdr())
    {
      pair = Spairref(args);
      n = pair->car();

      Assert(isnumber(n), "add not a number %d", typet(n));

      numadd(vm, out2.obj(), out, n);
      *out = out2.obj();
    }
  }
}

void ScmMath::subtract(VM* vm, ValueT* out, ValueT* args)
{
  PairPtr pair = Spairref(args);
  ValueT* n = pair->car();
  Assert(isnumber(n), "subtract not a number");
  *out = n;

  for (args = pair->cdr(); !Sisnull(args); args = pair->cdr())
  {
    pair = Spairref(args);
    n = pair->car();

    Assert(isnumber(n), "subtract not a number %d", typet(n));

    ValueT o2;
    numsubtract(&o2, out, n);
    *out = o2;
  }
}

void ScmMath::multiply(VM* vm, ValueT* out, ValueT* args)
{
  if (Sisnull(args))
    setnumi(out, 1);

  else
  {
    PairPtr pair = Spairref(args);
    ValueT* n = pair->car();
    Assert(isnumber(n), "add not a number");

    *out = n;
    for (args = pair->cdr(); !Sisnull(args); args = pair->cdr())
    {
      pair = Spairref(args);
      n = pair->car();

      Assert(isnumber(n), "multiply not a number %d", typet(n));

      ValueT o2;
      nummultiply(&o2, out, n);
      *out = o2;
    }
  }
}

static bool iszero(ValueT* a)
{
  switch(typet(a)) {
  case VT_NUM_INTEGER:
    return 0 == numi(a);
  case VT_NUM_RATIO:
    return Util::isFloatEqual(0.0, numratio(a));
  case VT_NUM_REAL:
    return false;
  case VT_NUM_COMPLEX:
    return true;
  default:
    Error("something error won't reach here %d", typet(a));
    return false;
  }
}

void ScmMath::divide(VM* vm, ValueT* out, ValueT* args)
{
  PairPtr pair = Spairref(args);
  ValueT* n = pair->car();
  Assert(isnumber(n), "subtract not a number");
  *out = n;

  for (args = pair->cdr(); !Sisnull(args); args = pair->cdr())
  {
    pair = Spairref(args);
    n = pair->car();

    Assert(isnumber(n), "divide not a number %d", typet(n));
    Assert(!iszero(n), "divide cannot be zero");

    ValueT o2;
    numdivide(&o2, out, n);
    *out = o2;
  }
}

void ScmMath::gcd(VM* vm, ValueT* out, ValueT* args)
{
  if (Sisnull(args))
    setnumi(out, 0);

  else
  {
    PairPtr pair = Spairref(args);
    ValueT* n = pair->car();
    Assert(isnumi(n), "gcd not a number %d", typet(n));

    *out = n;

    for (args = pair->cdr(); !Sisnull(args); args = pair->cdr())
    {
      pair = Spairref(args);
      n = pair->car();

      Assert(isnumi(n), "gcd not a number %d", typet(n));

      scm_int tmp = Sgcd(numi(out), numi(n));
      setnumi(out, tmp);
    }
  }
}

void ScmMath::lcm(VM* vm, ValueT* out, ValueT* args)
{
  if (Sisnull(args))
    setnumi(out, 1);

  else
  {
    PairPtr pair = Spairref(args);
    ValueT* n = pair->car();
    Assert(isnumi(n), "lcm not a number %d", typet(n));

    *out = n;

    for (args = pair->cdr(); !Sisnull(args); args = pair->cdr())
    {
      pair = Spairref(args);
      n = pair->car();

      Assert(isnumi(n), "lcm not a number %d", typet(n));

      scm_int tmp = Slcm(numi(out), numi(n));
      setnumi(out, tmp);
    }
  }
}

void ScmMath::numberp(VM* vm, ValueT* out, ValueT* args)
{
  PairPtr pair = Spairref(args);
  ValueT* n = pair->car();

  Assert(Sisnull(pair->cdr()), "numberp need only one arg");

  if (isnumber(n))
    *out = Strueref;

  else
    *out = Sfalseref;
}

void ScmMath::complexp(VM* vm, ValueT* out, ValueT* args)
{
  PairPtr pair = Spairref(args);
  ValueT* n = pair->car();

  Assert(Sisnull(pair->cdr()), "complexp need only one arg");

  if (isnumcomplex(n))
    *out = Strueref;

  else
    *out = Sfalseref;
}

void ScmMath::realp(VM* vm, ValueT* out, ValueT* args)
{
  PairPtr pair = Spairref(args);
  ValueT* n = pair->car();

  Assert(Sisnull(pair->cdr()), "realp need only one arg");

  if (isnumreal(n))
    *out = Strueref;

  else
    *out = Sfalseref;
}

void ScmMath::rationalp(VM* vm, ValueT* out, ValueT* args)
{
  PairPtr pair = Spairref(args);
  ValueT* n = pair->car();

  Assert(Sisnull(pair->cdr()), "rationalp need only one arg");

  if (isnumratio(n))
    *out = Strueref;

  else
    *out = Sfalseref;
}

void ScmMath::integerp(VM* vm, ValueT* out, ValueT* args)
{
  PairPtr pair = Spairref(args);
  ValueT* n = pair->car();

  Assert(Sisnull(pair->cdr()), "integerp need only one arg");

  if (isnumi(n))
    *out = Strueref;

  else
    *out = Sfalseref;
}

};
