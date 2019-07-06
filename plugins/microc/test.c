
#include <stdio.h>

int main()
{
  int x;
  //@ assert x == 0;
  printf("%d", 2);
}



/* Local Variables: */
/* compile-command: "make -C ../.. && why3 prove -P alt-ergo test.c" */
/* End: */
