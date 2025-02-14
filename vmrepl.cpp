#include "vm.h"

int main(int argc, char **argv)
{
  Scheme::VM vm;

  Scheme::GCVar expr(&vm);

  Scheme::Lexer lex(&vm, );
  lex.readOne(expr.obj());

  try
  {
    //  loop:
    String in;
    if (getline(std::cin, in))
    {

      // goto loop;
    }
  }
  catch(String &exception)
  {
    std::cout << exception << std::endl;
  }

  GC(&vm)->fullgc();

  std::cout << std::endl << "pause";
  String input;
  getline(std::cin, input);
}
