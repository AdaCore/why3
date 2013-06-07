


/*@ ensures \result == t[0];
  @*/
int f(int t[]) {
  return t[0];
}



/*
Local Variables:
compile-command: "frama-c -add-path ../.. -jessie3 array.c"
End:
*/
