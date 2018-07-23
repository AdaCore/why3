
/* run.config
   OPT: -journal-disable -jessie3
*/

/*@ requires 0 <= x <= 1000;
  @ ensures \result - x > 0;
  @*/
int f(int x) {
  return x+1;
}


/*@ requires 10 <= x <= 100;
  @*/
void g(int x) {
  int y;
  y = f(x-1);
  //@ assert y - x >= 0;
}



/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 call.c"
End:
*/
