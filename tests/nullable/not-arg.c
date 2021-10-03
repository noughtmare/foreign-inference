int f() {
  int x = 0;
  volatile int *i = &x;
  
  return *i;
}

