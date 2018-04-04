
/* run.config
   OPT: -journal-disable -jessie3
*/

//@ logic integer sum_upto(integer n) = n*(n+1) / 2;

/*@ lemma sum_rec: \forall integer n; n >= 0 ==>
  @     sum_upto(n+1) == sum_upto(n)+n+1;
  @*/

/*@ requires 0 <= x <= 60000;
  @ decreases x;
  @ ensures \result == sum_upto(x+0);
  @*/
long sum(int x) {
  long tmp;
  if (x == 0) return 0;
  tmp = sum (x-1);
  return /* x+ */ tmp; // CONVERSION ISSUE
}

/*@ requires 0 <= x <= 60000;
  @ decreases x;
  @ ensures \result == sum_upto(x+0);
  @*/
long sum2(int x) {
  if (x == 0) return 0;
  else return /* x + */ sum2(x-1);  // CONVERSION ISSUE
}

/*@ ensures \result == 36;
  @*/
long main () {
  long i = sum(8);
  return i;
}



/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 rec.c"
End:
*/
