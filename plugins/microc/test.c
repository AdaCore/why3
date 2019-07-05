
int f(int x)
//@ requires x >= 0;
{
  int y = x >= 0;
  { y++; }
  //@ assert y == 2;
}

/* Local Variables: */
/* compile-command: "make -C ../.. && why3 prove -P alt-ergo test.c" */
/* End: */
