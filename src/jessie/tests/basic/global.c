/* run.config
   OPT: -journal-disable -jessie3
*/



int x = 6;

int test0(void) {
  return x;
}

void test1(void) {
  x = 3;
}


const int y = 7;

void f(void) {
  // This should be proved
  //@ assert 6*y == 42;
  // This should not be proved
  //@ assert x*7 == 42;
  x++;
}

/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 global.c"
End:
*/
