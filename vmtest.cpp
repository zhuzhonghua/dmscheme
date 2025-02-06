#include "vm.h"

using namespace Scheme;

int main(int argc, char **argv)
{
  VM* vm = VM::newVM();

  Sgcvar1(expr);

  try
  {
    //  loop:
    String in;
    if (getline(std::cin, in))
    {
      Lexer lex(vm, in);
      lex.readOne(vobj(expr));
      // goto loop;
    }
  }
  catch(String &exception)
  {
    std::cout << exception << std::endl;
  }

  GC(vm)->fullgc();
  VM::delVM(vm);

  std::cout << std::endl << "pause";
  String input;
  getline(std::cin, input);
}
