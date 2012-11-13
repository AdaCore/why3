/* run.config
   OPT: -journal-disable -jessie3
*/


/*@ ensures \result == x+1;
  @*/
int f(int x) {
  return x+1;
}


/*
Local Variables:
compile-command: "frama-c -add-path ../.. -jessie3 incr.c"
End:
*/


