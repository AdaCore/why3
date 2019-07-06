
// tri par insertion

#include <stdio.h>
#include <stdlib.h>

void sort(int a[], int n)
//@ requires length(a) == n >= 1;
//@ ensures  forall i,j. 0 <= i <= j < n -> a[i] <= a[j];
{
  for (int m = 1; m < n; m++) {
    //@ invariant 1 <= m <= n;
    //@ invariant forall i,j. 0 <= i <= j < m -> a[i] <= a[j];
    //@ variant   n - m;
    int x = a[m];
    int k;
    for (k = m; k > 0 && a[k-1] > x; k--) {
        //@ invariant 0 <= k <= m;
        //@ invariant forall i,j. 0 <= i <= j < k               -> a[i] <= a[j];
        //@ invariant forall i,j. 0 <= i      < k <      j <= m -> a[i] <= a[j];
        //@ invariant forall i,j.               k < i <= j <= m -> a[i] <= a[j];
        //@ invariant forall   j.               k <      j <= m -> x    <  a[j];
        //@ variant   k;
      a[k] = a[k-1];
    }
    a[k] = x;
  }
}

int main() {
  int n = 42;
  int a[n];
  for (int i = 0; i < n; i++) {
    //@ invariant 0 <= i <= n;    //@ variant n - i;
    a[i] = rand() % 100;
    printf("%d, ", a[i]);
  }
  printf("\n");
  sort(a, n);
  for (int i = 0; i < n; i++) {
    //@ invariant 0 <= i <= n;    //@ variant n - i;
    printf("%d, ", a[i]);
  }
  printf("\n");
  return 0;
}

