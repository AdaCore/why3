/* run.config
   OPT: -journal-disable -jessie3
*/

// ISSUE: assignment Mem non implemented

/*@ requires \valid(t+(0..10));
  @ ensures \result == t[0];
  @*/
int f(int t[]) {
  return t[0];
}

/*@ requires \valid(t+(0..10));
  @ ensures t[0] == \old(t[0]);
  @ ensures t[1] == 42;
  @*/
void g(int t[]) {
  t[1] = 42;
}


/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -add-path ../.. -jessie3 array.c"
End:
*/
