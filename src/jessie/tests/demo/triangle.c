/* run.config
   OPT: -journal-disable -jessie3
*/

// ISSUE: \let not implemented
// ISSUE: floats not implemented

/* Area of a triangle, a formal revisit
 * http://hal.inria.fr/hal-00790071
 */

/*@ requires 0 <= x;
  @ ensures \result==\round_double(\NearestEven,\sqrt(x));
  @*/
double sqrt(double x);



/*@ logic real S(real a, real b, real c) =
  @  \let s = (a+b+c)/2;
  @        \sqrt(s*(s-a)*(s-b)*(s-c));
  @ */

/*@ requires 0 <= c <= b <= a && a <= b + c && a <= 0x1p255;
  @ ensures 0x1p-513 < \result
  @    ==> \abs(\result-S(a,b,c)) <= (53./8*0x1p-53 + 29*0x1p-106)*S(a,b,c);
  @ */

double triangle (double a,double b, double c) {
  return (0x1p-2*sqrt((a+(b+c))*(a+(b-c))*(c+(a-b))*(c-(a-b))));
}




/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 triangle.c"
End:
*/
