#ifndef __WMP_H__
#define __WMP_H__

#include <stdlib.h>
#include <stdint.h>

typedef int32_t wmp_size_t;
typedef uint64_t wmp_limb_t;
typedef wmp_limb_t *wmp_ptr;
typedef wmp_limb_t const *wmp_srcptr;

#if !defined(__GMP_H__) && !defined(__MINI_GMP_H__)
typedef struct {
  int _mp_alloc;
  int _mp_size;
  wmp_limb_t *_mp_d;
} __mpz_struct;
#endif

typedef __mpz_struct wmpz_t[1];
typedef __mpz_struct *wmpz_ptr;
typedef __mpz_struct const *wmpz_srcptr;

#ifdef __cplusplus
extern "C" {
#endif

static inline void wmpz_init (wmpz_ptr p)  {
  p->_mp_alloc = 1;
  p->_mp_size = 0;
  p->_mp_d = malloc(sizeof(uint64_t));
}



void wmpz_clear (wmpz_ptr);
wmp_ptr wmpz_realloc (wmpz_ptr, wmp_size_t);

void wmpz_set_ui (wmpz_ptr, uint64_t);
void wmpz_set_si (wmpz_ptr, int64_t);
uint64_t wmpz_get_ui (wmpz_srcptr);

// whitespace, leading base prefix, and base detection are not supported.
int32_t wmpz_set_str (wmpz_ptr, char const *, int32_t base);
// not verified when size >= 0x2000000.
// sp == NULL is not supported.
char *wmpz_get_str (char *, int32_t base, wmpz_srcptr);

int32_t wmpz_cmp (wmpz_srcptr, wmpz_srcptr);
int32_t wmpz_cmp_ui (wmpz_srcptr, uint64_t);
int32_t wmpz_cmp_si (wmpz_srcptr, int64_t);

int32_t wmpz_cmpabs (wmpz_srcptr, wmpz_srcptr);
int32_t wmpz_cmpabs_ui (wmpz_srcptr, uint64_t);

int32_t wmpz_sgn (wmpz_srcptr);
void wmpz_abs (wmpz_ptr, wmpz_srcptr);

void wmpz_add (wmpz_ptr, wmpz_srcptr, wmpz_srcptr);
void wmpz_add_ui (wmpz_ptr, wmpz_srcptr, uint64_t);

void wmpz_sub (wmpz_ptr, wmpz_srcptr, wmpz_srcptr);
void wmpz_sub_ui (wmpz_ptr, wmpz_srcptr, uint64_t);
void wmpz_ui_sub (wmpz_ptr, uint64_t, wmpz_srcptr);

void wmpz_mul (wmpz_ptr, wmpz_srcptr, wmpz_srcptr);
void wmpz_mul_si (wmpz_ptr, wmpz_srcptr, int64_t);
void wmpz_mul_ui (wmpz_ptr, wmpz_srcptr, uint64_t);

void wmpz_mul2exp (wmpz_ptr, wmpz_srcptr, uint64_t);
void wmpz_tdiv_q_2exp (wmpz_ptr, wmpz_srcptr, uint64_t);

void wmpz_tdiv_qr (wmpz_ptr quot, wmpz_ptr rem, wmpz_srcptr, wmpz_srcptr);
uint64_t wmpz_tdiv_qr_ui (wmpz_ptr quot, wmpz_ptr rem, wmpz_srcptr, uint64_t);



int32_t wmpn_cmp (wmp_srcptr, wmp_srcptr, wmp_size_t);

void wmpn_copyi (wmp_ptr, wmp_srcptr, wmp_size_t);
void wmpn_copyd (wmp_ptr, wmp_srcptr, wmp_size_t);

int32_t wmpn_zero_p (wmp_srcptr, wmp_size_t);
void wmpn_zero (wmp_ptr, wmp_size_t);

wmp_limb_t wmpn_add (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_srcptr, wmp_size_t);
wmp_limb_t wmpn_add_n (wmp_ptr, wmp_srcptr, wmp_srcptr, wmp_size_t);
wmp_limb_t wmpn_sub (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_srcptr, wmp_size_t);
wmp_limb_t wmpn_sub_n (wmp_ptr, wmp_srcptr, wmp_srcptr, wmp_size_t);
void wmpn_mul (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_srcptr, wmp_size_t);
void wmpn_mul_n (wmp_ptr, wmp_srcptr, wmp_srcptr, wmp_size_t);

wmp_limb_t wmpn_lshift (wmp_ptr, wmp_srcptr, wmp_size_t, uint64_t);
wmp_limb_t wmpn_rshift (wmp_ptr, wmp_srcptr, wmp_size_t, uint64_t);

void wmpn_powm (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_srcptr, wmp_size_t,
                wmp_srcptr, wmp_size_t, wmp_ptr);

// not verified when rp and up are aliased.
wmp_limb_t wmpn_add_1 (wmp_ptr rp, wmp_srcptr up, wmp_size_t, wmp_limb_t);
wmp_limb_t wmpn_sub_1 (wmp_ptr rp, wmp_srcptr up, wmp_size_t, wmp_limb_t);
wmp_limb_t wmpn_mul_1 (wmp_ptr rp, wmp_srcptr up, wmp_size_t, wmp_limb_t);
wmp_limb_t wmpn_addmul_1 (wmp_ptr rp, wmp_srcptr up, wmp_size_t, wmp_limb_t);
wmp_limb_t wmpn_submul_1 (wmp_ptr rp, wmp_srcptr up, wmp_size_t, wmp_limb_t);

// not verified when qp and up are aliased.
wmp_limb_t wmpn_divrem_1 (wmp_ptr qp, wmp_srcptr up, wmp_size_t, wmp_limb_t);

// not verified when rp and np are aliased. qxn must be == 0.
void wmpn_tdiv_qr (wmp_ptr qp, wmp_ptr rp, wmp_size_t qxn, wmp_srcptr np,
                   wmp_size_t nn, wmp_srcptr dp, wmp_size_t dn);

// not verified when rp and np are aliased.
wmp_size_t wmpn_sqrtrem (wmp_ptr sp, wmp_ptr rp, wmp_srcptr np, wmp_size_t);

wmp_size_t wmpn_set_str (wmp_ptr, unsigned char const *, uint32_t, int32_t base);
// not verified when un >= 0x2000000
wmp_size_t wmpn_get_str (unsigned char *, int32_t base, wmp_srcptr, wmp_size_t);

#ifdef __cplusplus
}
#endif

#endif
