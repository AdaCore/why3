#if defined(TEST_GMP) || defined(TEST_WHY3) || defined(TEST_MINIGMP)
#define BENCH
#else
#define COMPARE
#ifdef COMPARE_MINI
#define TEST_MINIGMP
#else
#define TEST_GMP
#endif
#define TEST_WHY3
#define TEST_ADD
#define TEST_MUL
#define TEST_DIV
#endif

#ifdef TEST_MINIGMP
#include "mini-gmp.c"
#endif
#ifdef TEST_GMP
#include <gmp.h>
#endif
#ifdef TEST_WHY3
#include "build/add.h"
#include "build/mul.h"
#include "build/div.h"
#endif

#include "mt19937-64.c"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <time.h>

#define TMP_ALLOC_LIMBS(n) malloc((n) * 8)

void mpn_dump(mp_ptr ap, mp_size_t an) {
  for (mp_size_t i = 0; i != an; ++i)
    printf("%016lx ", ap[i]);
  printf("\n");
}



void init_valid (mp_ptr ap, mp_ptr bp, mp_size_t an, mp_size_t bn) {
  for (int i = 0; i <= an; i++)
    ap[i] = genrand64_int64();
  for (int i = 0; i <= bn; i++)
    bp[i] = genrand64_int64();
  while (bp[bn-1]==0)
    bp[bn-1] = genrand64_int64();
  return;
}

int main () {
  mp_ptr ap, bp, rp, refp, rq, rr, refq, refr;
  mp_size_t max_n, an, bn, rn;
#ifdef BENCH
  struct timeval begin, end;
  double elapsed;
#endif
  uint64_t c, refc;
  //gmp_randstate_t rands;
  //TMP_DECL;
  //TMP_MARK;

  //tests_start ();
  //TESTS_REPS (reps, argv, argc);

  //gmp_randinit_default(rands);
  //gmp_randseed_ui(rands, 42);
  /* Re-interpret reps argument as a size argument.  */

  init_genrand64((unsigned long long)time(NULL));
  max_n = 20;

  ap = TMP_ALLOC_LIMBS (max_n + 1);
  bp = TMP_ALLOC_LIMBS (max_n + 1);
  /* nap = TMP_ALLOC_LIMBS (max_n + 1); */
  /* nbp = TMP_ALLOC_LIMBS (max_n + 1); */
  rp = TMP_ALLOC_LIMBS (2 * max_n);
  refp = TMP_ALLOC_LIMBS (2 * max_n);
  rq = TMP_ALLOC_LIMBS (max_n + 1);
  rr = TMP_ALLOC_LIMBS (max_n + 1);
  refq = TMP_ALLOC_LIMBS (max_n + 1);
  refr = TMP_ALLOC_LIMBS (max_n + 1);

#ifdef TEST_ADD
#ifdef BENCH
  printf ("#an bn t(s)\n");
#endif
  for (an = 2; an <= max_n; an += 1)
    {
      for (bn = 1; bn <= an; bn += 1)
	{
	  init_valid (ap, bp, an, bn);
#ifdef BENCH
          elapsed = 0;
          for (int iter = 0; iter != 10000; ++iter) {
            init_valid (ap, bp, an, bn);
            gettimeofday(&begin, NULL);
            for (int i = 0; i != 1000; ++i)
              {
#endif

#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            c = mpn_add (refp, ap, an, bp, bn);
#endif
#ifdef TEST_WHY3
            refc = wmpn_add (rp, ap, bp, an, bn);
#endif

#ifdef BENCH
              }
            gettimeofday(&end, NULL);
            elapsed +=
            (end.tv_sec - begin.tv_sec)
            + ((end.tv_usec - begin.tv_usec)/1000000.0);
          }
          printf ("%d %d %f\n", an, bn, elapsed);
          if (an==bn)
            printf ("\n"); //for gnuplot
#endif
#ifdef COMPARE
	  rn = an;
	  if (mpn_cmp (refp, rp, rn))
	    {
	      printf ("ERROR, an = %d, bn = %d, rn = %d\n",
		      (int) an, (int) bn, (int) rn);
	      printf ("a: "); mpn_dump (ap, an);
	      printf ("b: "); mpn_dump (bp, bn);
	      printf ("r:   "); mpn_dump (rp, rn);
	      printf ("ref: "); mpn_dump (refp, rn);
	      abort();
	    }
          if (c != refc)
	    {
	      printf ("ERROR, an = %d, bn = %d, rn = %d\n",
		      (int) an, (int) bn, (int) rn);
	      printf ("a: "); mpn_dump (ap, an);
	      printf ("b: "); mpn_dump (bp, bn);
	      printf ("c:    %016lx\n", c);
	      printf ("refc: %016lx\n", refc);
	      abort();
	    }
#endif
        }
    }
#ifdef COMPARE
  printf ("addition ok\n");
#endif
#endif
#ifdef TEST_MUL
#ifdef BENCH
  printf ("#an bn t(s)\n");
#endif
  for (an = 2; an <= max_n; an += 1)
    {
      for (bn = 1; bn <= an; bn += 1)
	{
	  init_valid (ap, bp, an, bn);
#ifdef BENCH
          elapsed = 0;
          for (int iter = 0; iter != 5000; ++iter) {
            init_valid (ap, bp, an, bn);
            gettimeofday(&begin, NULL);
            for (int i = 0; i != 1000; ++i)
              {
#endif
#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            mpn_mul (refp, ap, an, bp, bn);
#endif
#ifdef TEST_WHY3
            wmpn_mul (rp, ap, bp, an, bn);
#endif

#ifdef BENCH
              }
            gettimeofday(&end, NULL);
            elapsed +=
            (end.tv_sec - begin.tv_sec)
            + ((end.tv_usec - begin.tv_usec)/1000000.0);
          }
          printf ("%d %d %f\n", an, bn, elapsed);
          if (an==bn)
            printf ("\n"); //for gnuplot
#endif
#ifdef COMPARE
	  rn = an + bn;
	  if (mpn_cmp (refp, rp, rn))
	    {
	      printf ("ERROR, an = %d, bn = %d, rn = %d\n",
		      (int) an, (int) bn, (int) rn);
	      printf ("a: "); mpn_dump (ap, an);
	      printf ("b: "); mpn_dump (bp, bn);
	      printf ("r:   "); mpn_dump (rp, rn);
	      printf ("ref: "); mpn_dump (refp, rn);
	      abort();
	    }
#endif
        }
    }
#ifdef COMPARE
  printf ("multiplication ok\n");
#endif
#endif
#ifdef TEST_DIV
#ifdef BENCH
  printf ("#an bn t(s)\n");
#endif
  for (an = 2; an <= max_n; an += 1)
    {
      for (bn = 1; bn <= an; bn += 1)
	{
	  init_valid (ap, bp, an, bn);
#ifdef TEST_MINIGMP
          mpn_copyi(refr, ap, an);
#endif

#ifdef BENCH
          elapsed = 0;
          for (int iter = 0; iter != 10000; ++iter) {
            init_valid (ap, bp, an, bn);
#ifdef TEST_MINIGMP
            mpn_copyi(refr, ap, an);
#endif
            gettimeofday(&begin, NULL);
            for (int i = 0; i != 1000; ++i)
              {
#endif
#ifdef TEST_GMP
                mpn_tdiv_qr(refq, refr, 0, ap, an, bp, bn);
#endif
#ifdef TEST_MINIGMP
                mpn_div_qr (refq, refr, an, bp, bn);
#endif
#ifdef TEST_WHY3
                wmpn_tdiv_qr(rq, rr, ap, bp, an, bn);
#endif

#ifdef BENCH
              }
            gettimeofday(&end, NULL);
            elapsed +=
              (end.tv_sec - begin.tv_sec)
              + ((end.tv_usec - begin.tv_usec)/1000000.0);
          }
          printf ("%d %d %f\n", an, bn, elapsed);
          if (an==bn)
            printf ("\n"); //for gnuplot
#endif
#ifdef COMPARE
            rn = bn;
          if (mpn_cmp (refr, rr, rn))
	    {
          printf ("ERROR, an = %d, bn = %d, rn = %d\n",
            (int) an, (int) bn, (int) rn);
          printf ("a: "); mpn_dump (ap, an);
          printf ("b: "); mpn_dump (bp, bn);
          printf ("q:    "); mpn_dump (rq, an-bn+2);
          printf ("refq: "); mpn_dump (refq, an-bn+2);
          printf ("r:    "); mpn_dump (rr, rn);
          printf ("refr: "); mpn_dump (refr, rn);
          abort();
        }
          rn = an - bn + 1;
          if (mpn_cmp (refq, rq, rn))
	    {
          printf ("ERROR, an = %d, bn = %d, qn = %d\n",
            (int) an, (int) bn, (int) rn);
          printf ("a: "); mpn_dump (ap, an);
          printf ("b: "); mpn_dump (bp, bn);
          printf ("q:   "); mpn_dump (rq, rn);
          printf ("refq: "); mpn_dump (refq, rn);
          abort();
        }
#endif
	}
        }
#endif
#ifdef COMPARE
  printf ("division ok\n");
#endif
          //TMP_FREE;
          //tests_end ();
          return 0;
        }
