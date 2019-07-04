
// la multiplication dite russe

int mult(int a, int b)
//@ ensures result == a * b;
{
  int p = a;
  int q = b;
  if (q < 0) {
    p = -a;
    q = -b;
  }
  int r = 0;
  while (q > 0) {
    //@ invariant 0 <= q;
    //@ invariant r + p * q == a * b;
    //@ variant   q;
    if (q % 2 == 1)
      r += p;
    p *= 2;
    q /= 2;
  }
  return r;
}
