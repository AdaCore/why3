
#include <stdio.h>
#include <stdlib.h>

int foo(int a[]) {
  //@ requires length(a) >= 1;
  //@ ensures  a[0] == old(a[0]) + 1;
  a[0] = a[0] + 1;
}

int main()
{
  int x = 42;
  //@ label L;
  //@ assert x == 42;
  x = x+1;
  //@ assert at(x, L) == 42;
  while (x > 0) {
    //@ invariant x >= 0;
    //@ variant x;
    x--;
  }
  //@ assert x == 0;
  int a[10];
  a[0] = 41;
  //@ label ICI;
  foo(a);
  //@ assert a[0] == 42;
  //@ assert at(a[0], ICI) == 41;
}



/* Local Variables: */
/* compile-command: "make -C ../.. && why3 prove -P alt-ergo test.c" */
/* End: */
