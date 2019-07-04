
int f(int a, int b)
//@ requires b > 0;
//@ ensures result == a * b;
{
  int p = a;
  int q = b;
  if (q < 0) {
    p = -a;
    q = -b;
  }

  //@ assert q >= 0;

  int r = 0;
  while (q > 0) {
    //@ invariant 0 <= q;
    //@ invariant r + p * q == a * b;
    //@ variant   q;
    if (q % 2 == 1)
      r = r + p;
    p = p + p;
    q = q / 2;
  }
  return r;
}

/* Local Variables: */
/* compile-command: "make -C ../.. && why3 prove -P alt-ergo test.c" */
/* End: */
