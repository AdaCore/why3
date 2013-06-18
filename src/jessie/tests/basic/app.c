
/* run.config
   OPT: -journal-disable -jessie3
*/


//@ logic integer f(integer x) = x+1;


//@ requires f(x+0) >= 0;
int g(int x) {
  return x;
}



/*
Local Variables:
compile-command: "frama-c -add-path ../.. -jessie3 app.c"
End:
*/


