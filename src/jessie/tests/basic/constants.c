/* run.config
   OPT: -journal-disable -jessie3
*/


/*@ lemma test1 : 2 + 0xa == 0xc;
  @*/

/*@ lemma test_ofl : 0xffffffff + 1 == 0x100000000;
  @*/

/*@ lemma test2 : 0.0 + 1.1 == 1.1;
  @*/

/*@ lemma test3 : 10.0 * 0.1 == 1.0;
  @*/

/*@ lemma test4 : 0x1.1p4 == 17.0;
  @*/


/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 constants.c"
End:
*/
