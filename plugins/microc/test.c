
#include <stdio.h>
#include <stdlib.h>

int foo(int a[])
//@ requires length(a) >= 1;
//@ ensures result == 0 ;
{
  return a[0];
}

int main()
{
  int a[10];
  int r = foo(a);
  //@ assert r == 0;
  int x = 10 + rand() % 10;
  //@ assert 10 <= x <= 19;
}



/* Local Variables: */
/* compile-command: "make -C ../.. && why3 prove -P alt-ergo test.c" */
/* End: */
