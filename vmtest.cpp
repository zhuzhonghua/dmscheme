#include "vm.h"

using namespace Scheme;

void test(VM* vm, const char* stat)
{
  ReaderFromInput reader(vm, stat);
  Lexer lex(vm, &reader);

  Sreservevt(expr);
  lex.readOne(expr);

  PairPtr exprstat = Compiler(vm)->compile(expr);
  setpair(expr, exprstat);

  Sreservevt(exprout);
  vm->eval(exprout, exprstat);

  GC(vm)->fullgc();
}

int main(int argc, char **argv)
{
  VM vm;

  test(&vm, "(+ 1 2)");

  std::cout << std::endl << "pause";
  String input;
  getline(std::cin, input);

  return 0;
}
