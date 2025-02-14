#include "vm.h"

using namespace Scheme;

void test(VM* vm, const char* stat)
{
  Lexer lex(vm, stat);

  Sreservevt(expr);
  lex.readOne(expr);

  PairPtr exprstat = Compiler(vm)->compile(expr);

  Sreservevt(exprout);
  vm->eval(exprout, exprstat);

  GC(vm)->fullgc();
}

int main(int argc, char **argv)
{
  VM vm;

  test(&vm, "(+ 1 2)");

  return 0;
}
