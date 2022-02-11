
#include <stdio.h>

void loop1(int b)
//@ requires b > 0;
{
  while (--b) {
    //@ invariant b > 0;
    //@ variant b;
    ;
  }
  //@ assert b == 0;
}

void loop2(int b)
//@ requires b >= 0;
{
  while (b) {
    //@ invariant b >= 0;
    //@ variant b;
    b--;
  }
  //@ assert b == 0;
}
