typedef struct {
  int *x;
} point;

int f(point *p, int b) {
  int *w = p->x;
  if (b) {
    return *w;
  }
  return (int)w;
}
