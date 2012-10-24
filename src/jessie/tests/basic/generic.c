
/*@ axiomatic Bag {
  @   type bag<X>;
  @ //  logic integer occ<X>(<X> x, bag<X> b);
  @ //  axiom extensionality<X>: \forall bag<X> b1,b2;
  @ //    (\forall <X> x, occ(x,b1) == occ(x,b2)) ==> b1 == b2;
  @ //  logic bag<X> singleton<X>(<X> x);
  @ //  axiom occ_singleton_eq<X>: \forall <X> x;
  @ //    occ(x,singleton(x)) == 1;
  @ //  axiom occ_singleton_neq<X>: \forall <X> x,y;
  @ //    x != y ==> occ(x,singleton(y)) == 0;
  @ //  logic bag<X> bag_union<X>(bag<X> b1,bag<X> b2);
  @ //  axiom occ_union<X>: \forall <X> x, bag<X> b1,b2;
  @ //    occ(x,union(b1,b2)) == occ(x,b1) + occ(x,b2);
  @   lemma l2:  f1(1) == 2;
  @ }
  @*/
