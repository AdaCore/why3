#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <time.h>
#include <math.h>
#include <alloca.h>

#if defined(TEST_GMP) || defined(TEST_WHY3) || defined(TEST_MINIGMP)
#define BENCH
#if !(defined(TEST_ADD) || defined(TEST_MUL) || defined(TEST_TOOMB) || defined(TEST_TOOMM) || defined(TEST_TOOMU) || defined(TEST_DIV) || defined(TEST_SQRT1) || defined(TEST_SQRTREM) || defined(TEST_POWM) || defined(TEST_ZADD) || defined(TEST_ZSUB) || defined(TEST_ZMUL) || defined(TEST_MILLERRABIN))
#error "missing TEST_foo macro definition"
#endif //no TEST_OP
#else //no TEST_LIB
#define COMPARE
#define TEST_WHY3
#ifdef COMPARE_MINI
#define TEST_MINIGMP
#else //MINI
#define TEST_GMP
#endif //MINI
#define TEST_ADD
#define TEST_MUL
#define TEST_TOOMB
#define TEST_TOOMM
#define TEST_TOOMU
#define TEST_DIV
#define TEST_SQRT1
#define TEST_SQRTREM
#define TEST_POWM
#define TEST_ZADD
#define TEST_ZSUB
#define TEST_ZMUL
#ifndef COMPARE_MINI
#define TEST_MILLERRABIN
#endif
#endif

#ifdef TEST_MINIGMP
#include "mini-gmp.c"
#else
#include <gmp.h>
extern void __gmpn_powm (mp_ptr, mp_srcptr, mp_size_t, mp_srcptr, mp_size_t,
                      mp_srcptr, mp_size_t, mp_ptr);
#endif

#define SIZ(x) ((x)->_mp_size)
#define ABSIZ(x) ABS (SIZ (x))
#define PTR(x) ((x)->_mp_d)
#define ALLOC(x) ((x)->_mp_alloc)

#include "wmp.h"

extern wmp_limb_t sqrt1(wmp_ptr, wmp_limb_t);
extern void normalize(wmp_ptr, wmp_size_t*);

#include "mt19937-64.c"

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

void init_mpz_1 (mpz_ptr a, mp_size_t an) {
  mp_ptr ap = mpz_realloc(a, an);
  for (int i = 0; i < an; i++)
    ap[i] = genrand64_int64();
  while (ap[an-1]<1)
    ap[an-1] = genrand64_int64();
  SIZ(a) = an;
  return;
}

void init_valid_1(mp_ptr ap, mp_size_t an) {
  for (int i = 0; i < an; i++)
    ap[i] = genrand64_int64();
  while (ap[an-1]<2)
    ap[an-1] = genrand64_int64();
  return;
}

void compare_mpz (mpz_ptr u, mpz_ptr v, mpz_ptr w, mpz_ptr refw,
                  mp_size_t an, mp_size_t bn) {
  if (SIZ(w) != SIZ(refw) || (mpn_cmp (PTR(w), PTR(refw), SIZ(w))))
    {
      printf ("ERROR, an = %d, bn = %d", (int) an, (int) bn);
      printf ("a: "); mpn_dump (PTR(u), an);
      printf ("b: "); mpn_dump (PTR(v), bn);
      printf ("r:   "); mpn_dump (PTR(w), SIZ(w));
      printf ("ref: "); mpn_dump (PTR(refw), SIZ(refw));
      abort();
    }
}

#ifdef TEST_MILLERRABIN
#ifdef TEST_WHY3
void wmpz_powm (mpz_ptr r, mpz_ptr b, mpz_ptr e, mpz_ptr m) {
  mp_ptr rp, tp;
  mp_ptr bp, ep, mp;
  int32_t es = SIZ(e);
  int32_t n = SIZ(m);
  int cnt;
  int32_t rn, bn, en, itch;
  mpz_t new_b;
  mp = PTR(m);
  //ASSUME: e > 0
  //ASSUME: m odd
  //ASSUME: m > 0
  //ASSUME: b >= 0
  if (es == 0)
    {
      SIZ(r) = n != 1 || mp[0] != 1;
      PTR(r)[0] = 1;
      return;
    }
  bn = SIZ(b);
  if (bn == 0)
    {
      SIZ(r) = 0;
      return;
    }
  ep = PTR(e);
  en = es;
  if (en == 1 && ep[0] == 1)
    {
      rp = alloca (n * sizeof(uint64_t));
      bp = PTR(b);
      if (bn >= n)
        {
          mp_ptr qp = alloca ((bn - n + 1) * sizeof(uint64_t));
          wmpn_tdiv_qr (qp, rp, 0L, bp, bn, mp, n);
          rn = n;
          normalize (rp, &rn);
        }
      else
        {
          wmpn_copyi (rp, bp, bn);
          rn = bn;
        }
      goto ret;
    }
  tp = alloca (3*n * sizeof(uint64_t));
  rp = tp;
  tp += n;
  bp = PTR (b);
  //  printf ("bn %d en %d n %d\n", bn, en, n);
  wmpn_powm (rp, bp, bn, ep, en, mp, n, tp);
  rn = n;
  normalize (rp, &rn);
 ret:
  wmpz_realloc(r, rn);
  SIZ(r) = rn;
  wmpn_copyi (PTR(r), rp, rn);
  //  printf ("%d\n", rn);
}
#else
#define wmpz_powm mpz_powm
#define wmpn_mul_n mpn_mul_n
#ifdef TEST_GMP
#define wmpn_tdiv_qr(q, r, qxn, x, sx, y, sy) \
  mpn_tdiv_qr(q, r, qxn, x, sx, y, sy)
#else
//FIXME can we avoid a copy?
#define wmpn_tdiv_qr(q, r, qxn, x, sx, y, sy)    \
do {                                             \
  mpn_div_qr(q, x, sx, y, sy);                   \
  mpn_copyi(r,x,sy);                             \
 } while (0)
#endif
#define wmpz_cmp mpz_cmp
#define wmpz_cmp_ui mpz_cmp_ui
#define wmpz_set_ui mpz_set_ui
#define wmpz_tdiv_q_2exp mpz_tdiv_q_2exp
#define wmpz_add_ui mpz_add_ui
#define wmpz_sub_ui mpz_sub_ui
#define wmpz_realloc mpz_realloc
#define normalize(DST, NLIMBS) \
  do {                                                                  \
    while (*(NLIMBS) > 0)                                               \
      {                                                                 \
        if ((DST)[*(NLIMBS) - 1] != 0)                                  \
          break;                                                        \
        (*(NLIMBS))--;                                                  \
      }                                                                 \
  } while (0)

#endif

void sqrmod (mp_ptr qp, mp_ptr tp, mpz_ptr y, mpz_ptr n)
{
  int32_t yn, nn;
  mp_ptr yp, np;
  yn = SIZ(y);
  nn = SIZ(n);
  yp = PTR(y);
  np = PTR(n);
  wmpn_mul_n(tp, yp, yp, yn);
  wmpn_tdiv_qr(qp, yp, 0, tp, 2 * yn, np, nn);
  yn = nn;
  normalize(yp, &yn);
  wmpz_realloc(y, yn);
  SIZ(y) = yn;
}

static int do_millerrabin (mpz_ptr n, mpz_ptr nm1, mpz_ptr x, mpz_ptr y,
                           mpz_ptr q, unsigned long int k,
                           mp_ptr qp, mp_ptr tp)
{
  wmpz_powm (y,x,q,n);
  if (wmpz_cmp_ui (y, 1L) == 0 || wmpz_cmp (y, nm1) == 0)
    return 1;
  for (unsigned long int i = 1; i < k; i++)
    {
      sqrmod (qp, tp, y, n);
      // mpz_powm_ui(y,2,n);
      if (wmpz_cmp (y, nm1) == 0)
        return 1;
      if (wmpz_cmp_ui (y, 1L) <= 0)
        return 0;
    }
  return 0;
}

#define MPZ_TMP_INIT(X, NLIMBS)						\
  do {									\
    mpz_ptr __x = (X);							\
    __x->_mp_alloc = (NLIMBS);						\
    __x->_mp_d = TMP_ALLOC_LIMBS (NLIMBS);				\
  } while (0)

void urandomm (mpz_t a, mpz_t upper)
{
  mp_ptr ap, up;
  mp_size_t un;
  uint64_t um;
  int cnt;
  un = SIZ(upper);
  wmpz_realloc (a, un);
  ap = PTR(a);
  up = PTR(upper);
  for (int i = 0; i < un; i++) {
    ap[i] = genrand64_int64();
  }
  um = up[un-1];
  if (um <= 1)
    {
      SIZ(a) = un - 1;
      return;
    }
  cnt = __builtin_clz(up[un-1]);
  ap[un-1] >>= cnt;
  while (ap[un-1] >= um || ap[un-1] == 0) {
    ap[un-1] = genrand64_int64();
    ap[un-1] >>= cnt;
  }
  SIZ(a) = un;
}

static int wmpz_millerrabin (mpz_ptr n, int reps)
{
  int r = 0;
  mpz_t nm1, nm3, x, y, q;
  mp_ptr qp, tp;
  unsigned long int k;
  int is_prime;
  //  printf ("%d\n", SIZ(n));
  MPZ_TMP_INIT(nm1,SIZ(n)+1);
  wmpz_sub_ui (nm1, n, 1L);

  MPZ_TMP_INIT(x, SIZ(n)+1);
  MPZ_TMP_INIT(y, SIZ(n)+1); //TODO check

  //ASSUME n > 0
  //ASSUME n odd

  wmpz_set_ui (x, 210L);
  wmpz_powm (y, x, nm1, n);

  if (wmpz_cmp_ui (y, 1L) != 0)
    {
      goto ret;
    }

  MPZ_TMP_INIT(q, SIZ(n));
  k = mpz_scan1 (nm1, 0L);
  wmpz_tdiv_q_2exp (q, nm1, k);

  MPZ_TMP_INIT (nm3, SIZ(n) + 1);
  wmpz_sub_ui (nm3, n, 3L);

  is_prime = 1;
  qp = alloca ((SIZ(n) + 1) * sizeof(uint64_t));
  tp = alloca ((2 * SIZ(n)) * sizeof(uint64_t));
  for (r = 0; r < reps && is_prime; r++)
    {
      /* 2 to n-2 inclusive, don't want 1, 0 or -1 */
      urandomm (x, nm3);
      wmpz_add_ui (x, x, 2L);
      is_prime = do_millerrabin(n, nm1, x, y, q, k, qp, tp);
    }
 ret:
  //  if (r > 0) printf ("%d reps done", r);
  return r;
}

void mr_candidate (mpz_t c, int len) {
  init_mpz_1(c, len);
  mpz_setbit (c, 0);
}

#endif //TEST_MILLERRABIN

int main () {
  mp_ptr ap, bp, rp, refp, rq, rr, refq, refr, ep, rep, mp, tp;
  mp_size_t max_n, max_add, max_mul, max_toom, max_div, max_sqrt, max_powm,
    an, bn, rn, cn;
  mpz_t u, v, w, refw, cp;
  int nb, nb_iter;
  double elapsed;
  mpz_init(cp);
  mpz_init(u);
  mpz_init(v);
  mpz_init(w);
  mpz_init(refw);
#ifdef BENCH
  struct timeval begin, end;
#endif
  uint64_t a, c, refc;

  //TMP_DECL;
  //TMP_MARK;

  //tests_start ();
  //TESTS_REPS (reps, argv, argc);


  //gmp_randseed_ui(rands, 42);
  /* Re-interpret reps argument as a size argument.  */

#ifdef BENCH
  init_genrand64(0);
#else
  init_genrand64((unsigned long long)time(NULL));
#endif
  max_n = 100000;
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
            refc = mpn_add (refp, ap, an, bp, bn);
#endif
#ifdef TEST_WHY3
            c = wmpn_add (rp, ap, an, bp, bn);
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
          printf ("%d %d %g\n", (int)an, (int)bn, elapsed);
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
          printf ("%d %d %g\n", (int)an, (int)bn, elapsed);
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

#ifdef TEST_TOOMB
#ifdef BENCH
  printf ("#an bn t(µs)\n");
#endif

  for (bn = 5; bn <= max_toom * 10; bn = (int)ceil(bn * 1.1))
    {
      //mp_ptr ws = TMP_ALLOC_LIMBS(9 * bn / 2 + 32);
      //an = (bn * 3) / 2;
      an = bn;
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
      printf ("%d %d %g\n", (int)an, (int)bn, elapsed);
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
  printf ("balanced toom ok\n");
#endif
#endif //TOOMB

#ifdef TEST_TOOMM
#ifdef BENCH
  printf ("#an bn t(µs)\n");
#endif

  for (bn = 5; bn <= max_toom * 5; bn = (int)ceil(bn * 1.1))
    {
      //mp_ptr ws = TMP_ALLOC_LIMBS(9 * bn / 2 + 32);
      //an = (bn * 3) / 2;
      an = 6 * bn;
      elapsed = 0;
      nb_iter = 300;
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
      printf ("%d %d %g\n", (int)an, (int)bn, elapsed);
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
  printf ("medium toom ok\n");
#endif
#endif //TOOMM

#ifdef TEST_TOOMU
#ifdef BENCH
  printf ("#an bn t(µs)\n");
#endif

  for (bn = 5; bn <= max_toom * 5 ;bn = (int)ceil(bn * 1.1))
    {
      //mp_ptr ws = TMP_ALLOC_LIMBS(9 * bn / 2 + 32);
      //an = (bn * 3) / 2;
      an = 24 * bn;
      elapsed = 0;
      nb_iter = 100;
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
      printf ("%d %d %g\n", (int)an, (int)bn, elapsed);
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
  printf ("unbalanced toom ok\n");
#endif
#endif //TOOMU

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
                wmpn_tdiv_qr(rq, rr, 0, ap, an, bp, bn);
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
          printf ("%d %d %g\n", (int)an, (int)bn, elapsed);
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
        printf ("%g\n", elapsed);
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
  for (an = 1; an <= max_sqrt * 15; an = (int)ceil(an * 1.1))
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
      printf ("%d %g\n", (int)an, elapsed);
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
          printf ("%d %d %g\n", (int)an, (int)rn, elapsed);
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

#ifdef TEST_ZADD
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
            init_mpz_1 (u, an);
            init_mpz_1 (v, bn);
            mpz_realloc (w, an+1);
            mpz_realloc (refw, an+1);
            nb = 10000 / an;
#ifdef BENCH
            gettimeofday(&begin, NULL);
            for (int i = 0; i != nb; ++i)
              {
#endif

#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            mpz_add (refw, u, v);
#endif
#ifdef TEST_WHY3
            wmpz_add (w, u, v);
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
          printf ("%d %d %g\n", (int)an, (int)bn, elapsed);
          if (an==bn)
            printf ("\n"); //for gnuplot
#endif
#ifdef COMPARE
          compare_mpz (u, v, w, refw, an, bn);
          mpz_add (refw, u, u);
          wmpz_add (w, u, u);
          compare_mpz (u, u, w, refw, an, bn);
          mpz_set(w,u);
          mpz_set (refw, u);
          mpz_add (refw, refw, v);
          wmpz_add (w, w, v);
          compare_mpz (w,v,w,refw,an,bn);
          mpz_set(w,v);
          mpz_set (refw, v);
          mpz_add (refw, u, refw);
          wmpz_add (w, u, w);
          compare_mpz (u,w,w,refw,an,bn);
#endif
        }
    }
#ifdef COMPARE
  printf ("mpz addition ok\n");
#endif
#endif


#ifdef TEST_ZSUB
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
            init_mpz_1 (u, an);
            init_mpz_1 (v, bn);
            mpz_realloc (w, an+1);
            mpz_realloc (refw, an+1);
            nb = 10000 / an;
#ifdef BENCH
            gettimeofday(&begin, NULL);
            for (int i = 0; i != nb; ++i)
              {
#endif

#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            mpz_sub (refw, u, v);
#endif
#ifdef TEST_WHY3
            wmpz_sub (w, u, v);
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
          printf ("%d %d %g\n", (int)an, (int)bn, elapsed);
          if (an==bn)
            printf ("\n"); //for gnuplot
#endif
#ifdef COMPARE
          compare_mpz (u, v, w, refw, an, bn);
          mpz_sub (refw, u, u);
          wmpz_sub (w, u, u);
          compare_mpz (u, u, w, refw, an, bn);
          mpz_set(w,u);
          mpz_set (refw, u);
          mpz_sub (refw, refw, v);
          wmpz_sub (w, w, v);
          compare_mpz (w,v,w,refw,an,bn);
          mpz_set(w,v);
          mpz_set (refw, v);
          mpz_sub (refw, u, refw);
          wmpz_sub (w, u, w);
          compare_mpz (u,w,w,refw,an,bn);
#endif
        }
    }
#ifdef COMPARE
  printf ("mpz subtraction ok\n");
#endif
#endif


#ifdef TEST_ZMUL
#ifdef BENCH
  printf ("#an bn t(µs)\n");
#endif
  for (an = 2; an <= max_mul; an += 1)
    {
      for (bn = 1; bn <= an; bn += 1)
        {
          elapsed = 0;
          nb_iter = 1000;
          for (int iter = 0; iter != nb_iter; ++iter) {
            init_mpz_1 (u, an);
            init_mpz_1 (v, bn);
            mpz_realloc (w, an+1);
            mpz_realloc (refw, an+1);
            nb = 10000 / an;
#ifdef BENCH
            gettimeofday(&begin, NULL);
            for (int i = 0; i != nb; ++i)
              {
#endif

#if defined(TEST_GMP) || defined(TEST_MINIGMP)
            mpz_mul (refw, u, v);
#endif
#ifdef TEST_WHY3
            wmpz_mul (w, u, v);
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
          printf ("%d %d %g\n", (int)an, (int)bn, elapsed);
          if (an==bn)
            printf ("\n"); //for gnuplot
#endif
#ifdef COMPARE
          compare_mpz (u, v, w, refw, an, bn);
          mpz_mul (refw, u, u);
          wmpz_mul (w, u, u);
          compare_mpz (u, u, w, refw, an, bn);
          mpz_set(w,u);
          mpz_set (refw, u);
          mpz_mul (refw, refw, v);
          wmpz_mul (w, w, v);
          compare_mpz (w,v,w,refw,an,bn);
          mpz_set(w,v);
          mpz_set (refw, v);
          mpz_mul (refw, u, refw);
          wmpz_mul (w, u, w);
          compare_mpz (u,w,w,refw,an,bn);
#endif
        }
    }
#ifdef COMPARE
  printf ("mpz multiplication ok\n");
#endif
#endif

#ifdef TEST_MILLERRABIN
#define REPS 25
  nb_iter = 50;
  elapsed = 0;
  int i = 0;
  int len;
  for (len = 16; len <= 200; len=(int)ceil(len * 1.1)){
#ifdef BENCH
    for (i = 0; i < nb_iter; i++) {
#endif
      mr_candidate(cp, len);
#ifdef BENCH
      gettimeofday(&begin, NULL);
#endif
      c = wmpz_millerrabin(cp,REPS);
      //   if (c > 0)
      //printf (" at step %d\n", i);
#ifdef BENCH
      gettimeofday(&end, NULL);
      elapsed +=
        (end.tv_sec - begin.tv_sec) * 1000000.0
        + (end.tv_usec - begin.tv_usec);
    }
    elapsed = elapsed/nb_iter;
    printf ("%d   %g\n", len, elapsed);
#endif
#ifdef COMPARE
    refc = mpz_millerrabin(cp,REPS);
    if (c != refc) {
      printf ("c %ld refc %ld\n", c, refc);
      abort ();
    }
#endif
  }
#ifdef COMPARE
  printf ("Miller-Rabin ok\n");
#endif
#endif
  //TMP_FREE;
  //tests_end ();
  return 0;
}
