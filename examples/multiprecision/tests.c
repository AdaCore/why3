#if defined(TEST_GMP) || defined(TEST_WHY3) || defined(TEST_MINIGMP)
#define BENCH
#else
#define COMPARE
#ifdef COMPARE_MINI
#define TEST_MINIGMP
#else
#define TEST_GMP
#endif
#define TEST_ADD
#define TEST_MUL
#define TEST_TOOM
#define TEST_DIV
#define TEST_SQRT1
#define TEST_SQRTREM
#define TEST_POWM
#endif

#ifdef TEST_MINIGMP
#include "mini-gmp.c"
#else
#include <gmp.h>
extern void __gmpn_powm (mp_ptr, mp_srcptr, mp_size_t, mp_srcptr, mp_size_t,
                      mp_srcptr, mp_size_t, mp_ptr);
#endif

#ifdef TEST_LIB
#include "wmp.h"
extern wmp_limb_t sqrt1(wmp_ptr, wmp_limb_t);
#endif

#ifndef TEST_WHY3
#define TEST_WHY3
#endif

#if defined(TEST_WHY3) && !defined(TEST_LIB)
#include "build/add.h"
#include "build/mul.h"
#include "build/div.h"
#include "build/toom.h"
#include "build/sqrt1.h"
#include "build/sqrt.h"
#include "build/powm.h"
#endif

#include "mt19937-64.c"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <time.h>

#define TMP_ALLOC_LIMBS(n) (mp_ptr)malloc((n) * 8)

void mpn_dump(mp_ptr ap, mp_size_t an) {
  for (mp_size_t i = 0; i != an; ++i)
    printf("%016lx ", ap[i]);
  printf("\n");
}

void init_valid (mp_ptr ap, mp_ptr bp, mp_size_t an, mp_size_t bn) {
  for (int i = 0; i < an; i++)
    ap[i] = genrand64_int64();
  for (int i = 0; i < bn; i++)
    bp[i] = genrand64_int64();
  while (bp[bn-1]==0)
    bp[bn-1] = genrand64_int64();
  return;
}

void init_valid_1(mp_ptr ap, mp_size_t an) {
  for (int i = 0; i < an; i++)
    ap[i] = genrand64_int64();
  while (ap[an-1]<2)
    ap[an-1] = genrand64_int64();
  return;
}

int main () {
  mp_ptr ap, bp, rp, refp, rq, rr, refq, refr, ep, rep, mp, tp;
  mp_size_t max_n, max_add, max_mul, max_toom, max_div, max_sqrt, max_powm,
    an, bn, rn, cn;
  int nb, nb_iter;
  double elapsed;
#ifdef BENCH
  struct timeval begin, end;
#endif
  uint64_t a, c, refc;
  //gmp_randstate_t rands;
  //TMP_DECL;
  //TMP_MARK;

  //tests_start ();
  //TESTS_REPS (reps, argv, argc);

  //gmp_randinit_default(rands);
  //gmp_randseed_ui(rands, 42);
  /* Re-interpret reps argument as a size argument.  */

#ifdef BENCH
  init_genrand64(0);
#else
  init_genrand64((unsigned long long)time(NULL));
#endif
  max_n = 1000;
  max_add = 50;
  max_mul = 20;
  max_toom = 95;
  max_div = 20;
  max_sqrt = 95;
  max_powm = 50;
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
  tp = TMP_ALLOC_LIMBS(2 * max_n);
  ep = TMP_ALLOC_LIMBS(max_n + 1);
  mp = TMP_ALLOC_LIMBS(max_n + 1);

#ifdef TEST_ADD
#ifdef BENCH
  printf ("#an bn t(µs)\n");
#endif
  for (an = 2; an <= max_add; an += 1)
    {
      for (bn = 1; bn <= an; bn += 1)
	{
          elapsed = 0;
          nb_iter = 1000;
          for (int iter = 0; iter != nb_iter; ++iter) {
            init_valid (ap, bp, an, bn);
            nb = 10000 / an;
#ifdef BENCH
            gettimeofday(&begin, NULL);
            for (int i = 0; i != nb; ++i)
              {
#endif

#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            c = mpn_add (refp, ap, an, bp, bn);
#endif
#ifdef TEST_WHY3
            refc = wmpn_add (rp, ap, an, bp, bn);
#endif

#ifdef BENCH
              }
            gettimeofday(&end, NULL);
            elapsed +=
            (end.tv_sec - begin.tv_sec) * 1000000.0
            + (end.tv_usec - begin.tv_usec);
#endif
          }
          elapsed = elapsed / (nb * nb_iter);
#ifdef BENCH
          printf ("%ld %ld %g\n", an, bn, elapsed);
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
  printf ("#an bn t(µs)\n");
#endif
  for (an = 2; an <= max_mul; an += 1)
    {
      for (bn = 1; bn <= an; bn += 1)
	{
          elapsed = 0;
          nb_iter = 500;
          for (int iter = 0; iter != nb_iter; ++iter) {
            init_valid (ap, bp, an, bn);
            nb = 5000 / an;
#ifdef BENCH
            gettimeofday(&begin, NULL);
            for (int i = 0; i != nb; ++i)
              {
#endif
#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            mpn_mul (refp, ap, an, bp, bn);
#endif
#ifdef TEST_WHY3
            wmpn_mul (rp, ap, an, bp, bn);
#endif

#ifdef BENCH
              }
            gettimeofday(&end, NULL);
            elapsed +=
            (end.tv_sec - begin.tv_sec) * 1000000.0
            + (end.tv_usec - begin.tv_usec);
#endif
          }
          elapsed = elapsed / (nb * nb_iter);
#ifdef BENCH
          printf ("%ld %ld %g\n", an, bn, elapsed);
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

#ifdef TEST_TOOM
#ifdef BENCH
  printf ("#an bn t(µs)\n");
#endif

  for (bn = 35; bn <= max_toom; bn += 2)
    {
      //mp_ptr ws = TMP_ALLOC_LIMBS(9 * bn / 2 + 32);
      //an = (bn * 3) / 2;
      an = bn * 6;
      elapsed = 0;
      nb_iter = 500;
      for (int iter = 0; iter != nb_iter; ++iter) {
        init_valid (ap, bp, an, bn);
        nb = 5000 / bn;
#ifdef BENCH
        gettimeofday(&begin, NULL);
        for (int i = 0, maxi = nb; i != maxi; ++i)
          {
#endif
#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            mpn_mul (refp, ap, an, bp, bn);
#endif
#ifdef TEST_WHY3
            wmpn_mul (rp, ap, an, bp, bn);
#endif

#ifdef BENCH
          }
        gettimeofday(&end, NULL);
        elapsed +=
          (end.tv_sec - begin.tv_sec) * 1000000.0
          + (end.tv_usec - begin.tv_usec);
#endif
      }
      elapsed = elapsed / (nb * nb_iter);
#ifdef BENCH
      printf ("%ld %ld %g\n", an, bn, elapsed);
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
      //free(ws);
    }
#ifdef COMPARE
  printf ("toom ok\n");
#endif
#endif

#ifdef TEST_DIV
#ifdef BENCH
  printf ("#an bn t(µs)\n");
#endif
  for (an = 2; an <= max_div; an += 1)
    {
      for (bn = 1; bn <= an; bn += 1)
	{
          elapsed = 0;
          nb_iter = 1000;
          for (int iter = 0; iter != nb_iter; ++iter) {
            init_valid (ap, bp, an, bn);
#ifdef TEST_MINIGMP
            mpn_copyi(refr, ap, an);
#endif
            nb = 1500 / an;
#ifdef BENCH
            gettimeofday(&begin, NULL);
            for (int i = 0; i != nb; ++i)
              {
#endif
#ifdef TEST_GMP
                mpn_tdiv_qr(refq, refr, 0, ap, an, bp, bn);
#endif
#ifdef TEST_MINIGMP
                mpn_div_qr (refq, refr, an, bp, bn);
#endif
#ifdef TEST_WHY3
                wmpn_tdiv_qr(rq, rr, ap, an, bp, bn);
#endif

#ifdef BENCH
              }
            gettimeofday(&end, NULL);
            elapsed +=
              (end.tv_sec - begin.tv_sec) * 1000000.0
              + (end.tv_usec - begin.tv_usec);
#endif
          }
          elapsed = elapsed / (nb * nb_iter);
#ifdef BENCH
          printf ("%ld %ld %g\n", an, bn, elapsed);
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
#ifdef COMPARE
  printf ("division ok\n");
#endif
#endif
#ifdef TEST_SQRT1
#ifdef BENCH
  printf ("#t(s)\n");
#endif

      elapsed = 0;
      an = bn = rn = 1;
      for (int iter = 0; iter != 500; ++iter) {
        init_valid (bp, ap, 1, 1);
        a = *ap;
        if (a < 0x4000000000000000) continue;
#ifdef BENCH
        gettimeofday(&begin, NULL);
        for (int i = 0; i != 100; ++i)
          {
#endif
#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            mpn_sqrtrem (refr, refp, ap, 1);
            refc = *refr;
#endif
#ifdef TEST_WHY3
            c = sqrt1 (rp, a);
#endif

#ifdef BENCH
          }
        gettimeofday(&end, NULL);
        elapsed +=
          (end.tv_sec - begin.tv_sec)
          + ((end.tv_usec - begin.tv_usec)/1000000.0)
        printf ("%f\n", elapsed);
        printf ("\n"); //for gnuplot
#endif
#ifdef COMPARE
      if (mpn_cmp (refp, rp, rn) || c != refc)
        {
          printf ("ERROR, i=%d\n",
                  (int) iter);
          printf ("a: "); mpn_dump (ap, an);
          printf ("r:   "); mpn_dump (rp, rn);
          printf ("ref: "); mpn_dump (refp, rn);
          printf ("c:    %016lx\n", c);
          printf ("refc: %016lx\n", refc);
          abort();
        }
#endif
    }
#ifdef COMPARE
    printf ("sqrt1 ok\n");
#endif
#endif

#ifdef TEST_SQRTREM
#ifdef BENCH
  printf ("#an t(µs)\n");
#endif
  bn=1;
  for (an = 1; an <= max_sqrt; an += 1)
    {
      elapsed = 0;
      nb_iter = 1000;
      for (int iter = 0; iter != nb_iter; ++iter) {
        init_valid (bp, ap, 1, an);
#ifdef TEST_MINIGMP
        mpn_copyi(refr, ap, an);
#endif
#ifdef BENCH
        gettimeofday(&begin, NULL);
        nb = 1500 / an;
        for (int i = 0; i != nb; ++i)
          {
#endif
#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            rn = mpn_sqrtrem(refq, refr, ap, an);
#endif
#ifdef TEST_WHY3
            cn = wmpn_sqrtrem(rq, rr, ap, an);
#endif

#ifdef BENCH
          }
        gettimeofday(&end, NULL);
        elapsed +=
          (end.tv_sec - begin.tv_sec) * 1000000.0
          + (end.tv_usec - begin.tv_usec);
#endif
      }
      elapsed = elapsed / (nb * nb_iter);
#ifdef BENCH
      printf ("%d %f\n", an, elapsed);
      printf ("\n"); //for gnuplot
#endif
#ifdef COMPARE
      if (cn != rn)
        {
          printf ("ERROR, an = %d, expected rn = %d, actual rn = %d\n",
                  (int) an, (int) rn, (int) cn);
          printf ("a: "); mpn_dump (ap, an);
          printf ("s: "); mpn_dump (rq, (an+1)/2);
          printf ("refs: "); mpn_dump (refq, (an+1)/2);
          printf ("r: "); mpn_dump (rr, cn);
          printf ("refr: "); mpn_dump (refr, rn);
          abort ();
        }
      if (mpn_cmp (refr, rr, rn))
        {
          printf ("ERROR, an = %d, rn = %d\n",
                  (int) an, (int) rn);
          printf ("a: "); mpn_dump (ap, an);
          printf ("s: "); mpn_dump (rq, (an+1)/2);
          printf ("refs: "); mpn_dump (refq, (an+1)/2);
          printf ("r: "); mpn_dump (rr, rn);
          printf ("refr: "); mpn_dump (refr, rn);
          abort();
        }
      if (mpn_cmp (refq, rq, (an+1)/2))
        {
          printf ("ERROR, an = %d, rn = %d\n",
                  (int) an, (int) rn);
          printf ("a: "); mpn_dump (ap, an);
          printf ("s: "); mpn_dump (rq, (an+1)/2);
          printf ("refs: "); mpn_dump (refq, (an+1)/2);
          printf ("r: "); mpn_dump (rr, rn);
          printf ("refr: "); mpn_dump (refr, rn);
          abort();
        }
#endif
    }
#ifdef COMPARE
  printf ("sqrtrem ok\n");
#endif
#endif

#ifdef TEST_POWM
#ifdef TEST_MINIGMP
  printf ("powm not available in mini-GMP\n");
  goto skip;
#endif
#ifdef BENCH
  printf ("#an bn t(µs)\n");
#endif
  for (an = 2; an <= max_powm; an += 5)
    {
      for (rn = 1; rn <= max_powm; rn += 5)
	{
          elapsed = 0;
          nb_iter = 1;
          for (int iter = 0; iter != nb_iter; ++iter) {
            init_valid_1 (ap, an);
            init_valid_1 (ep, an);
            init_valid_1 (tp, 2 * rn);
            init_valid_1 (mp, rn);
            mp[0] |= 1;
            nb = 150 / an;
#ifdef BENCH
            gettimeofday(&begin, NULL);
            for (int i = 0; i != nb; ++i)
              {
#endif
#ifdef TEST_GMP
                __gmpn_powm(refr, ap, an, ep, an, mp, rn, tp);
#endif
#ifdef TEST_WHY3
                wmpn_powm(rr, ap, an, ep, an, mp, rn, tp);
#endif

#ifdef BENCH
              }
            gettimeofday(&end, NULL);
            elapsed +=
              (end.tv_sec - begin.tv_sec) * 1000000.0
              + (end.tv_usec - begin.tv_usec);
#endif
          }
          elapsed = elapsed / (nb * nb_iter);
#ifdef BENCH
          printf ("%ld %ld %g\n", an, rn, elapsed);
          if (an==rn)
            printf ("\n"); //for gnuplot
#endif
#ifdef COMPARE
          if (mpn_cmp (refr, rr, rn))
	    {
          printf ("ERROR, an = %d, rn = %d\n",
            (int) an, (int) rn);
          printf ("b: "); mpn_dump (ap, an);
          printf ("e: "); mpn_dump (ep, an);
          printf ("m: "); mpn_dump (mp, rn);
          printf ("r:    "); mpn_dump (rr, rn);
          printf ("refr: "); mpn_dump (refr, rn);
          abort();
        }
#endif
	}
        }
#ifdef COMPARE
  printf ("powm ok\n");
#endif
 skip:
#endif

  //TMP_FREE;
  //tests_end ();
  return 0;
}
