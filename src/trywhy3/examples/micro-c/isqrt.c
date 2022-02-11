
int isqrt(int n)
//@ requires n >= 0;
//@ ensures  result * result <= n < (result + 1) * (result + 1);
{ int r = 0;
  int s = 1;
  while (s <= n) {
    //@ invariant 0 <= r;
    //@ invariant r * r <= n;
    //@ invariant s == (r+1) * (r+1);
    //@ variant   n - s;
    r++;
    s += 2 * r + 1;
  }
  return r;
}
