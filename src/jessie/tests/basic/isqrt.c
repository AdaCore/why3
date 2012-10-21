
//@ logic integer sqr(integer x) = x * x;

/*@ requires x >= 0;
  @ ensures \result >= 0 && sqr(\result) <= x && x < sqr(\result + 1);
  @*/
int isqrt(int x) {
  int count = 0, sum = 1;
  /*@ loop invariant count >= 0 && x >= sqr(count) && sum == sqr(count+1);
    @ loop variant  x - count; 
    @*/
  while (sum <= x) sum += 2 * ++count + 1;
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
compile-command: "frama-c -add-path ../.. -jessie3 isqrt.c"
End:
*/


