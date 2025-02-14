#pragma once

namespace Scheme {

class VM;

typedef void * (*ScmAlloc) (void *ptr, size_t nsize);

struct ValueT;
typedef void (*CFunction)(VM* vm, ValueT* out, ValueT* args);


};
