#pragma once

#include <string>
#include <sstream>
#include <fstream>
#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <list>
#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <cfloat>
#include <cmath>
#include <cctype>
#include <ctime>

namespace Scheme {

typedef std::string String;
typedef std::stringstream StringStream;

typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char byte;

typedef long scm_int;

class Util {
public:
  static String stringPrintf(const char* fmt, ...) {
    int size = 128;
    std::string str;
    va_list ap;
    int times = 5;
    while (true && times-- > 0)
    {
      str.resize(size);
      va_start(ap, fmt);
      int n = vsnprintf((char *)str.data(), size, fmt, ap);
      va_end(ap);

      // n might be bigger than size
      if (n > -1 && n < size)
      {
        str.resize(n);
        return str;
      }

      size *= 2;
    }
    if (times < 0)
      throw "internal error at printf";

    return str;
  }

  static bool isFloatEqual(double a, double b) {
    return std::abs(a - b) <= DBL_EPSILON;
  }
  static bool isFloatEqual(float a, float b) {
    return std::abs(a - b) <= FLT_EPSILON;
  }
  static void error(const String &info) {
    throw info;
  }
  static int throwerror(const char* info) {
    throw info;
    return 0;
  }

  static uint hash(const char* s, int l, int seed) {
    int h = seed ^ l;
    for (; l > 0; l--)
      h ^= ((h<<5) + (h>>2) + (byte)(s[l - 1]));
    return h;
  }
};

#define Debug(x) x

#define StringPrint Util::stringPrintf
#define STR(s) #s
//#define Print(...) printf(StringPrint(__VA_ARGS__).c_str());
#define Print(...) fprintf(stderr, __VA_ARGS__)

#define FILE_LINE_FUNCTION StringPrint("%s:%d:%s \t", __FILE__, __LINE__, __FUNCTION__)
//#define Error(...) Util::error(FILE_LINE_FUNCTION + StringPrint(__VA_ARGS__) + "\nerror happended\n");
#define Error(...) Util::error(StringPrint(__VA_ARGS__) + "\nerror happended\n");

#define Assert(condition, ...) do { if (!(condition)) { Error(#condition ## __VA_ARGS__); } } while (0)

#define FltEqual Util::isFloatEqual

#define ValueCStr(ptr) ptr->cStr().c_str()

#define MULTILINE(...) #__VA_ARGS__

template<typename T, ushort size>
class RingBuf {
public:
  T read() {
//    Assert(!empty(), "internal error ringbuf empty while reading");

    T v = buf[freer++];
    if (freer == size + 1) freer = 0;

    return v;
  }
  void write(T v) {
    Assert(!full(), "internal error ringbuf full when write");

    buf[freew++] = v;
    if (freew == size + 1) freew = 0;
  }

  bool empty() { return freer == freew; }
  bool full() { return freew - freer == size || freew + 1 == freer; }

  RingBuf() { freer = freew = 0; }
protected:
  T buf[size + 1];
  ushort freer;
  ushort freew;
};

};
