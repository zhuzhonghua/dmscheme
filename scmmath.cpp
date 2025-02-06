#include "vm.h"
#include "scmmath.h"

namespace Scheme {

#define regc(NAME, TYPE, FUNC) vm->regCFunction(NAME, TYPE ## :: ## FUNC);

void ScmMath::init(VM* vm)
{
  regc("+", ScmMath, add);
  regc("-", ScmMath, subtract);
  regc("*", ScmMath, multiply);
  regc("/", ScmMath, divide);
}

static void numtoratio(ValueT* a)
{
  Assert(isnumi(a), "wrong up type %d", typet(a));
  setnumratio(a, numi(a));
}

static void numtoreal(ValueT* a)
{
  Assert(isnumi(a) || isnumratio(a), "wrong up type %d", typet(a));
}

static void numtocomplex(ValueT* a)
{
}

static void numsynctype(ValueT* a1, ValueT* a2, ValueT* a1p, ValueT* a2p)
{
  *a1 = a1p;
  *a2 = a2p;

  if (typet(a1) == typet(a2)) return;

  switch(typet(a1)) {
  case VT_NUM_INTEGER:
    switch(typet(a2)) {
    case VT_NUM_RATIO: numtoratio(a1); break;
    case VT_NUM_REAL: numtoreal(a1); break;
    case VT_NUM_COMPLEX: numtocomplex(a1); break;
    }
    break;
  case VT_NUM_RATIO:
    switch(typet(a2)) {
    case VT_NUM_INTEGER: numtoratio(a2); break;
    case VT_NUM_REAL: numtoreal(a1); break;
    case VT_NUM_COMPLEX: numtocomplex(a1); break;
    }
    break;
  case VT_NUM_REAL:
    switch(typet(a2)) {
    case VT_NUM_INTEGER: numtoreal(a2); break;
    case VT_NUM_RATIO: numtoreal(a2); break;
    case VT_NUM_COMPLEX: numtocomplex(a1); break;
    }
    break;
  case VT_NUM_COMPLEX:
    switch(typet(a2)) {
    case VT_NUM_INTEGER: numtocomplex(a2); break;
    case VT_NUM_RATIO: numtocomplex(a2); break;
    case VT_NUM_REAL: numtocomplex(a2); break;
    }
    break;
  }
}

#define NumABOp(NAME, OP)                                         \
  static void num ## NAME (ValueT* out, ValueT* a1, ValueT* a2)   \
  {                                                               \
    ValueT a1p, a2p; numsynctype(&a1p, &a2p, a1, a2);             \
    switch(typet(&a1p)) {                                         \
    case VT_NUM_INTEGER:                                          \
      setnumi(out, numi(&a1p) OP numi(&a2p)); break;              \
    case VT_NUM_RATIO:                                            \
      setnumratio(out, numratio(&a1p) OP numratio(&a2p)); break;  \
    case VT_NUM_REAL: break;                                      \
    case VT_NUM_COMPLEX: break;                                   \
    }                                                             \
  }

NumABOp(add, +)

NumABOp(subtract, -)

NumABOp(multiply, *)

NumABOp(divide, -)

void ScmMath::add(ValueT* out, ValueT* args)
{
  if (Sisnull(args))
    setnumi(out, 0);

  else
  {
    PairPtr pair = Spairref(args);
    ValueT* n = pair->car();
    Assert(isnumber(n), "add not a number %d", typet(n));

    *out = n;
    for (args = pair->cdr(); !Sisnull(args); args = pair->cdr())
    {
      pair = Spairref(args);
      n = pair->car();

      Assert(isnumber(n), "add not a number %d", typet(n));

      ValueT o2;
      numadd(&o2, out, n);
      *out = o2;
    }
  }
}

void ScmMath::subtract(ValueT* out, ValueT* args)
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

void ScmMath::multiply(ValueT* out, ValueT* args)
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

void ScmMath::divide(ValueT* out, ValueT* args)
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

};
