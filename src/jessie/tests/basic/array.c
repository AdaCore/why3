/* run.config
   OPT: -journal-disable -jessie3
*/



/*@ // requires \valid(t+(0..10));
  @ ensures \result == t[0];
  @*/
int f(int t[]) {
  return t[0];
}



/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -add-path ../.. -jessie3 array.c"
End:
*/
