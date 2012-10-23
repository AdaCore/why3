/* run.config
   OPT: -journal-disable -jessie3
*/


//@ lemma l1: 6*7 == 42;

/*@ axiomatic Bag {
  @   type bag<X>;
  @ //  logic bag<X> bag_union<X>(bag<X> b1,bag<X> b2);
  @ //  axiom union_comm<X>: \forall bag<X> b1,b2;
  @ //     bag_union(b1,b2) == bag_union(b2,b1);
  @ }
  @*/

//@ lemma l2: 6+7 == 13;




/*
Local Variables:
compile-command: "frama-c -add-path ../.. -jessie3 axiomatic.c"
End:
*/
