
// la somme des n premiers entiers

int triangular(int n)
//@ requires n >= 0;
//@ ensures  result == n * (n+1) / 2;
{
  int s = 0;
  int k = 0;
  while (k <= n) {
    //@ invariant k <= n+1;
    //@ invariant s == (k - 1) * k / 2;
    //@ variant   n - k;
    s += k;
    k++;
  }
  return s;
}

