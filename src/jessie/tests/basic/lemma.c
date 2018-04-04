/* run.config
   OPT: -journal-disable -jessie3
*/


/*@ lemma test1 : 2+2 == 4;
  @*/

/*@ lemma test2 : \forall integer x; x*x >= 0;
  @*/

/*@ lemma test2r : \forall real x; x*x >= 0.0;
  @*/

/*@ lemma test3 : \forall integer x,y; x+y == y+x;
  @*/

/*@ lemma test3r : \forall real x,y; x+y == y+x;
  @*/

/*@ lemma test4 : \forall integer x,y; x-y == -(y-x);
  @*/

/*@ lemma test4r : \forall real x,y; x-y == -(y-x);
  @*/

/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 lemma.c"
End:
*/
