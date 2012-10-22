/* run.config
   OPT: -journal-disable -jessie3
*/


/*@ axiomatic Bag {
  @   type bag;
  @   logic bag my_union(bag b1,bag b2);
  @   axiom union_comm: \forall bag b1,b2;
  @      my_union(b1,b2) == my_union(b2,b1);
  @ }
  @*/




/*
Local Variables:
compile-command: "frama-c -add-path ../.. -jessie3 axiomatic.c"
End:
*/
