#ifndef __WMP_H__
#define __WMP_H__

#include <stdint.h>

typedef int32_t wmp_size_t;
typedef uint64_t wmp_limb_t;
typedef wmp_limb_t *wmp_ptr;
typedef wmp_limb_t const *wmp_srcptr;

typedef struct
{
int _alloc;
int _size;
uint64_t * _ptr;
} __mpz_struct;

typedef __mpz_struct *mpz_ptr;

#ifdef __cplusplus
extern "C" {
#endif

mpz_ptr wmpz_init ();
void wmpz_clear (mpz_ptr);
wmp_ptr wmpz_realloc(mpz_ptr, wmp_size_t);

void wmpz_set_ui(mpz_ptr, uint64_t);
void wmpz_set_si(mpz_ptr, int64_t);
uint64_t wmpz_get_ui(mpz_ptr);

int32_t wmpz_cmp(mpz_ptr, mpz_ptr);
int32_t wmpz_cmp_ui(mpz_ptr, uint64_t);

void wmpz_add(mpz_ptr, mpz_ptr, mpz_ptr);
void wmpz_add_ui(mpz_ptr, mpz_ptr, uint64_t);

void wmpz_sub(mpz_ptr, mpz_ptr, mpz_ptr);
void wmpz_sub_ui(mpz_ptr, mpz_ptr, uint64_t);
void wmpz_ui_sub(mpz_ptr, uint64_t, mpz_ptr);

void wmpz_mul(mpz_ptr, mpz_ptr, mpz_ptr);
void wmpz_mul_si(mpz_ptr, mpz_ptr, int64_t);
void wmpz_mul_ui(mpz_ptr, mpz_ptr, uint64_t);

void wmpz_mul2exp(mpz_ptr, mpz_ptr, uint64_t);
void wmpz_tdiv_q_2exp(mpz_ptr, mpz_ptr, uint64_t);

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

#ifdef __cplusplus
}
#endif

#endif
