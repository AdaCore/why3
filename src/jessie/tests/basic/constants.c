/* run.config
   OPT: -journal-disable -jessie3
*/


/*@ lemma test1 : 2 + 0xa == 0xc;
  @*/

/*@ lemma test2 : 0.0 + 1.1 == 1.1;
  @*/


/*
Local Variables:
compile-command: "frama-c -add-path ../.. -jessie3 constants.c"
End:
*/


