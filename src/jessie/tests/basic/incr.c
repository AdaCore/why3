/* run.config
   OPT: -journal-disable -jessie3
*/


/*@ ensures \result == x+1;
  @*/
int f(int x) {
  return x+1;
}

#if 0

int g;

/*@ ensures g == \old(g)+x;
  @*/
void h(int x) {
  g += x;
}

#endif

/*
Local Variables:
compile-command: "frama-c -add-path ../.. -jessie3 incr.c"
End:
*/


