/* run.config
   OPT: -journal-disable -jessie3
*/

int x = 42;

void f(void) {
  //@ assert 6*7 == x;
}


/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 global.c"
End:
*/
