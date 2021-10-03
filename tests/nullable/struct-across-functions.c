#include <stdlib.h>

typedef struct {
  int * ptr;
} S;

int f(S *s) {
  return *(s->ptr);
}

void g(int * arr, S *s)
{
  s->ptr = arr;
}

