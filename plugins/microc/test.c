
#include <stdio.h>
#include <stdlib.h>

//@ function int foo(int x) = x+1;
//@ predicate bar(int x, int y) = x>y;

int foo(int a[], int x)
//@ requires length(a) >= 1;
//@ requires a[0] == 0;
//@ ensures  result == 0;
{
  x = 2;
  a[0] = 1;
  return 0;
}

int main()
{
  int s = 0;
  int a[10];
  a[0] = 0;
  int r = foo(a, 10);
  //@ assert r == 0;
  //@ assert bar(1, r);
  int x = 10 + rand() % 10;
  //@ assert 10 <= x <= 19;
  s++;
}



/* Local Variables: */
/* compile-command: "make -C ../.. && why3 prove -P alt-ergo test.c" */
/* End: */
