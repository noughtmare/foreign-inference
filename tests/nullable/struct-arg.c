typedef struct {
  int *f;
} t;

int f(t *s) {
  return *s->f;
}
