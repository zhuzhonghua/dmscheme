#pragma once

#include "dum.h"

namespace Scheme {

class ScmMath {
public:
  static void init(VM* vm);
  static void add(ValueT* out, ValueT* args);
  static void subtract(ValueT* out, ValueT* args);
  static void multiply(ValueT* out, ValueT* args);
  static void divide(ValueT* out, ValueT* args);
};
};
