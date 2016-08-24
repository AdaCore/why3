/* run.config
   OPT: -journal-disable -jessie3
*/

int f(void) {
  //@ assert 6*7 == 42;
  return 0;
}

void g(void) {
  int x = 6;
  //@ assert x*7 == 42;
}

//@ ensures \result == 42;
int h(void) {
  return 6*7;
}

/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 forty-two.c"
End:
*/
