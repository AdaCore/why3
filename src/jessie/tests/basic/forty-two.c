/* run.config
   OPT: -journal-disable -jessie3
*/

void f(void) {
  //@ assert 6*7 == 42;
}

//@ ensures \result == 42;
int g(void) {
  return 6*7;
}

/*
Local Variables:
compile-command: "frama-c -add-path ../.. -jessie3 forty-two.c"
End:
*/



