
#include <stdio.h>
#include <stdlib.h>

// recherche dichotomique dans un tableau trié

int dicho(int a[], int n, int v) {
  //@ requires length(a) == n;
  //@ requires forall i1, i2. 0 <= i1 <= i2 < n -> a[i1] <= a[i2];
  //@ ensures  -1 <= result < n;
  //@ ensures  result == -1 -> forall i. 0 <= i < n -> a[i] != v;
  //@ ensures  result >= 0  -> a[result] == v;
  int l = 0;
  int u = n-1;
  int r = -1;
  while (l <= u) {
    //@ invariant 0 <= l && u < n;
    //@ invariant r == -1;
    //@ invariant forall i. 0 <= i < n -> a[i] == v -> l <= i <= u;
    //@ variant   u - l;
    int m = (l + u) / 2;
    if (a[m] < v)
      l = m+1;
    else if (a[m] > v)
      u = m-1;
    else {
      r = m;
      break;
    }
  }
  return r;
}

int main() {
  int n = 42;
  int a[n];
  a[0] = rand() % 100;
  printf("%d, ", a[0]);
  for (int i = 1; i < n; i++) {
    //@ invariant 1 <= i <= n;
    //@ invariant forall i1, i2. 0 <= i1 <= i2 < i -> a[i1] <= a[i2];
    //@ variant  n - i;
    a[i] = a[i-1] + rand() % 10;
    printf("%d, ", a[i]);
  }
  printf("\n");
  //@ assert forall i1, i2. 0 <= i1 <= i2 < length(a) -> a[i1] <= a[i2];
  printf("quelle valeur cherchez-vous ? ");
  int v;
  scanf("%d", &v);
  int r = dicho(a, n, v);
  if (r == -1)
    printf("valeur absente\n");
  else
    printf("valeur présente à la position %d\n,", r);
}


