#pragma once

#include "dum.h"

namespace Scheme {

class ScmMath {
public:
  static void init(VM* vm);
  static void add(VM* vm, ValueT* out, ValueT* args);
  static void subtract(VM* vm, ValueT* out, ValueT* args);
  static void multiply(VM* vm, ValueT* out, ValueT* args);
  static void divide(VM* vm, ValueT* out, ValueT* args);
  static void gcd(VM* vm, ValueT* out, ValueT* args);
  static void lcm(VM* vm, ValueT* out, ValueT* args);
  static void numerator(VM* vm, ValueT* out, ValueT* args);
  static void denominator(VM* vm, ValueT* out, ValueT* args);
  static void numberp(VM* vm, ValueT* out, ValueT* args);
  static void complexp(VM* vm, ValueT* out, ValueT* args);
  static void realp(VM* vm, ValueT* out, ValueT* args);
  static void rationalp(VM* vm, ValueT* out, ValueT* args);
  static void integerp(VM* vm, ValueT* out, ValueT* args);
};
};
