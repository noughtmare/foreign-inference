typedef struct {
  int *x;
} point;

int f(point *p, int b) {
  if (b) {
    return *p->x;
  }
  return 0;
}
