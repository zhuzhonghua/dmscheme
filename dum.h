#pragma once

namespace Scheme {

typedef void * (*ScmAlloc) (void *ptr, size_t nsize);

struct ValueT;
typedef void (*CFunction)(ValueT* out, ValueT* args);

class VM;

};
