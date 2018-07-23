/* run.config
   OPT: -journal-disable -jessie3
*/

// ISSUE WITH -1 in program (workaround: 0-1)
// ISSUES WITH CONVERSION long <-> int

//@ lemma mean: \forall integer x, y; x <= y ==> x <= (x+y)/2 <= y;

/* predicate sorted{L}(long *t, integer a, integer b) =
  @    \forall integer i,j; a <= i <= j <= b ==> t[i] <= t[j];
  @*/

/*@ requires n >= 0 ;
  @ requires \valid(t+(0..n-1));
  @ // requires sorted(t,0,n-1);
  @ requires \forall integer i,j; 0 <= i <= j < n ==> t[i] <= t[j];
  @ ensures -1 <= \result+0 < n;
  @ ensures \result >= 0 ==> t[\result+0] == v;
  @ ensures \result == -1 ==>
  @     \forall integer k; 0 <= k < n ==> t[k] != v;
  @*/
int binary_search(long t[], int n, long v) {
  int l = 0, u = n-1;
  /*@ loop invariant 0 <= l && u <= n-1;
    @ loop invariant
    @   \forall integer k; 0 <= k < n && t[k] == v ==> l <= k <= u;
    @ loop variant u-l;
    @*/
  while (l <= u ) {
    int m = (l + u) / 2;
    //@ assert l <= m <= u;
    if (t[m] < v) l = m + 1;
    else if (t[m] > v) u = m - 1;
    else return m;
  }
  return 0-1;
}

/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 binary_search.c"
End:
*/
