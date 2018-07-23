/* run.config
   OPT: -journal-disable -jessie3
*/

// ISSUE: predicate with labels not implemented

/* selection sort */



/*@ predicate Swap{L1,L2}(int *a, integer i, integer j) =
  @   \at(a[i],L1) == \at(a[j],L2) &&
  @   \at(a[j],L1) == \at(a[i],L2) &&
  @   \forall integer k; k != i && k != j
  @       ==> \at(a[k],L1) == \at(a[k],L2);
  @*/

/*@ inductive Permut{L1,L2}(int *a, integer l, integer h) {
  @  case Permut_refl{L}:
  @   \forall int *a, integer l, h; Permut{L,L}(a, l, h) ;
  @  case Permut_sym{L1,L2}:
  @    \forall int *a, integer l, h;
  @      Permut{L1,L2}(a, l, h) ==> Permut{L2,L1}(a, l, h) ;
  @  case Permut_trans{L1,L2,L3}:
  @    \forall int *a, integer l, h;
  @      Permut{L1,L2}(a, l, h) && Permut{L2,L3}(a, l, h) ==>
  @        Permut{L1,L3}(a, l, h) ;
  @  case Permut_swap{L1,L2}:
  @    \forall int *a, integer l, h, i, j;
  @       l <= i <= h && l <= j <= h && Swap{L1,L2}(a, i, j) ==>
  @     Permut{L1,L2}(a, l, h) ;
  @ }
  @*/

/*@ predicate Sorted{L}(int *a, integer l, integer h) =
  @   \forall integer i,j; l <= i <= j < h ==> a[i] <= a[j] ;
  @*/



/*@ requires \valid(t+i) && \valid(t+j);
  @ assigns t[i],t[j];
  @ ensures Swap{Old,Here}(t,i,j);
  @*/
void swap(int t[], int i, int j) {
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
}

/*@ requires \valid(t+(0..(n-1)));
  @ behavior sorted:
  @   ensures Sorted(t,0,n);
  @ behavior permutation:
  @   ensures Permut{Old,Here}(t,0,n-1);
  @*/
void min_sort(int t[], int n) {
  int i,j;
  int mi,mv;
  if (n <= 0) return;
  /*@ loop invariant 0 <= i < n;
    @ for sorted:
    @  loop invariant
    @   Sorted(t,0,i) &&
    @   (\forall integer k1, k2 ;
    @      0 <= k1 < i <= k2 < n ==> t[k1] <= t[k2]) ;
    @ for permutation:
    @  loop invariant Permut{Pre,Here}(t,0,n-1);
    @ loop variant n-i;
    @*/
  for (i=0; i<n-1; i++) {
    // look for minimum value among t[i..n-1]
    mv = t[i]; mi = i;
    /*@ loop invariant i < j && i <= mi < n;
      @ for sorted:
      @  loop invariant
      @    mv == t[mi] &&
      @    (\forall integer k; i <= k < j ==> t[k] >= mv);
      @ for permutation:
      @  loop invariant
      @   Permut{Pre,Here}(t,0,n-1);
      @ loop variant n-j;
      @*/
    for (j=i+1; j < n; j++) {
      if (t[j] < mv) {
        mi = j ; mv = t[j];
      }
    }
  L:
    swap(t,i,mi);
    //@ assert Permut{L,Here}(t,0,n-1);
  }
}


/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 selection_sort.c"
End:
*/
