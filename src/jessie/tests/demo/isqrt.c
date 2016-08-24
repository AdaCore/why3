/* run.config
   OPT: -journal-disable -jessie3
*/


//@ logic integer sqr(integer x) = x * x;

/*@ requires x >= 0;
  @ requires x <= 1000000000; // to prevent integer overflow
  @ ensures \result >= 0 && sqr(\result+0) <= x && x < sqr(\result + 1);
  @*/
int isqrt(int x) {
  int count = 0, sum = 1;
  /*@ loop invariant count >= 0 && x >= sqr(count+0) && sum == sqr(count+1);
    @ loop variant  x - count;
    @*/
  while (sum <= x) { ++count; sum += 2 * count + 1; }
  return count;
}

//@ ensures \result == 4;
int main () {
  int r;
  r = isqrt(17);
  //@ assert r < 4 ==> \false;
  //@ assert r > 4 ==> \false;
  return r;
}


/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 isqrt.c"
End:
*/
