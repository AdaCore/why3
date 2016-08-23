/* run.config
   OPT: -journal-disable -jessie3
*/


/*@ requires x <= 1000000;
  @ ensures \result == x+1;
  @*/
int f(int x) {
  return x+1;
}

int g;

/*@ requires 0 <= g <= 1000000;
  @ requires 0 <= x <= 1000000;
  @ ensures g == \old(g)+x;
  @*/
void h(int x) {
  g += x;
}


/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 incr.c"
End:
*/
