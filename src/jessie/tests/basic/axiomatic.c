/* run.config
   OPT: -journal-disable -jessie3
*/


//@ logic integer f1(integer x) = x*x + 1;

//@ lemma l1: \forall integer x; f1(x) >= 1;

/*@ axiomatic BagInt {
  @   type bag;
  @   logic integer occ(integer x, bag b);
  @   axiom extensionality: \forall bag b1,b2;
  @     (\forall integer x; occ(x,b1) == occ(x,b2)) ==> b1 == b2;
  @   logic bag singleton(integer x);
  @   axiom occ_singleton_eq: \forall integer x;
  @     occ(x,singleton(x)) == 1;
  @   axiom occ_singleton_neq: \forall integer x,y;
  @     x != y ==> occ(x,singleton(y)) == 0;
  @   logic bag bag_union(bag b1,bag b2);
  @   axiom occ_union: \forall integer x, bag b1,b2;
  @     occ(x,bag_union(b1,b2)) == occ(x,b1) + occ(x,b2);
  @   lemma l2:  f1(1) == 2;
  @ }
  @*/

/*@  lemma union_comm: \forall bag b1,b2;
  @     bag_union(b1,b2) == bag_union(b2,b1);
  @*/



/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 axiomatic.c"
End:
*/
