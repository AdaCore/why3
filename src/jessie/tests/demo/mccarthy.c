/* run.config
   OPT: -journal-disable -jessie3
*/


/*@ decreases 101-n ;
  @ ensures n <= 100 ==> \result == 91;
  @ ensures n >= 101 ==> \result == n - 10;
  @*/
int f91(int n) {
  if (n <= 100) {
    return f91(f91(n + 11));
  }
  else
    return n - 10;
}

/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 mccarthy.c"
End:
*/
