/* run.config
   OPT: -journal-disable -jessie3
*/

// ISSUE: enum not implemented

/* Dijkstra's dutch flag */

typedef enum Color {BLUE = 1, WHITE = 2, RED = 3 } color;

/*@ predicate is_color(color c) =
  @   c == BLUE || c == WHITE || c == RED ;
  @*/

/*@ predicate is_color_array{L}(color *t, integer l) =
  @   \valid(t+(0..(l-1))) &&
  @   \forall integer i; 0 <= i < l ==> is_color(t[i]) ;
  @*/

/*@ predicate is_monochrome{L}(color *t,integer i, integer j, color c) =
  @   \forall integer k; i <= k < j ==> t[k] == c ;
  @*/


/*@ requires \valid(t+(i..j));
  @ behavior decides_monochromatic:
  @   ensures \result <==> is_monochrome(t,i,j,c);
  @*/
int isMonochrome(color t[], int i, int j, color c) {
  /*@ loop invariant i <= k &&
    @   \forall integer l; i <= l < k ==> t[l] == c;
    @ loop variant j - k;
    @*/
  for (int k = i; k < j; k++) if (t[k] != c) return 0;
  return 1;
}

/*@ requires \valid(t+i);
  @ requires \valid(t+j);
  @ behavior i_j_swapped:
  @   assigns t[i],t[j];
  @   ensures t[i] == \old(t[j]) && t[j] == \old(t[i]);
  @*/
void swap(color t[], int i, int j) {
  color z = t[i];
  t[i] = t[j];
  t[j] = z;
}

/*@ requires l >= 0 && is_color_array(t, l);
  @ behavior sorts:
  @   ensures
  @     (\exists integer b,r;
  @        is_monochrome(t,0,b,BLUE) &&
  @        is_monochrome(t,b,r,WHITE) &&
  @        is_monochrome(t,r,l,RED));
  @*/
void flag(color t[], int l) {
  int b = 0;
  int i = 0;
  int r = l;
  /*@ loop invariant
    @   is_color_array(t,l) &&
    @   0 <= b <= i <= r <= l &&
    @   is_monochrome(t,0,b,BLUE) &&
    @   is_monochrome(t,b,i,WHITE) &&
    @   is_monochrome(t,r,l,RED);
    @ loop variant r - i;
    @*/
  while (i < r) {
    switch (t[i]) {
    case BLUE:
      swap(t,b++, i++);
      break;
    case WHITE:
      i++;
      break;
    case RED:
      swap(t,--r, i);
      break;
    }
  }
}



/*
Local Variables:
compile-command: "frama-c -load-module ../../Jessie3.cmxs -jessie3 flag.c"
End:
*/
