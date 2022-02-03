
#include <stdio.h>

// la somme des n premiers entiers

int triangular(int n)
//@ requires n >= 0;
//@ ensures  result == n * (n + 1) / 2;
{
  int s = 0;
  for (int k = 0; k <= n; k++) {
    //@ invariant k <= n + 1;
    //@ invariant s == (k - 1) * k / 2;
    //@ variant   n - k;
    s += k;
  }
  return s;
}

int triangular2(int n)
/*@ requires n >= 0;
  @ ensures  result == n * (n + 1) / 2;
  @ variant  n; */
{
  if (n == 0) return 0;
  return n + triangular2(n - 1);
}

int main() {
  printf("somme 1 + .. + 100 = %d\n", triangular(100));
  printf("somme 1 + .. + 100 = %d\n", triangular2(100));
  return 0;
}
