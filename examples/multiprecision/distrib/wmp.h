#ifndef __WMP_H__
#define __WMP_H__

#include <stdint.h>

typedef uint32_t wmp_size_t;
typedef uint64_t wmp_limb_t;
typedef wmp_limb_t *wmp_ptr;
typedef wmp_limb_t const *wmp_srcptr;

#ifdef __cplusplus
extern "C" {
#endif

wmp_limb_t wmpn_add (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_srcptr, wmp_size_t);

wmp_limb_t wmpn_add_1 (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_limb_t);

wmp_limb_t wmpn_add_n (wmp_ptr, wmp_srcptr, wmp_srcptr, wmp_size_t);

wmp_limb_t wmpn_add_in_place (wmp_ptr, wmp_size_t, wmp_srcptr, wmp_size_t);

wmp_limb_t wmpn_add_1_in_place (wmp_ptr, wmp_size_t, wmp_limb_t);

int32_t wmpn_cmp (wmp_srcptr, wmp_srcptr, wmp_size_t);

void wmpn_copyi (wmp_ptr, wmp_srcptr, wmp_size_t);

int32_t wmpn_zero_p (wmp_srcptr, wmp_size_t);

void wmpn_zero (wmp_ptr, wmp_size_t);

wmp_limb_t wmpn_sub (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_srcptr, wmp_size_t);

wmp_limb_t wmpn_sub_1 (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_limb_t);

wmp_limb_t wmpn_sub_n (wmp_ptr, wmp_srcptr, wmp_srcptr, wmp_size_t);

wmp_limb_t wmpn_sub_in_place (wmp_ptr, wmp_size_t, wmp_srcptr, wmp_size_t);

wmp_limb_t wmpn_sub_1_in_place (wmp_ptr, wmp_size_t, wmp_limb_t);

void wmpn_mul (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_srcptr, wmp_size_t);

wmp_limb_t wmpn_mul_1 (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_limb_t);

void wmpn_mul_n (wmp_ptr, wmp_srcptr, wmp_srcptr, wmp_size_t);

wmp_limb_t wmpn_addmul_1 (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_limb_t);

wmp_limb_t wmpn_submul_1 (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_limb_t);

wmp_limb_t wmpn_lshift (wmp_ptr, wmp_srcptr, wmp_size_t, uint64_t);

wmp_limb_t wmpn_rshift (wmp_ptr, wmp_srcptr, wmp_size_t, uint64_t);

wmp_limb_t wmpn_lshift_in_place (wmp_ptr, wmp_size_t, uint64_t);

wmp_limb_t wmpn_rshift_in_place (wmp_ptr, wmp_size_t, uint64_t);

wmp_limb_t wmpn_divrem_1 (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_limb_t);

void wmpn_tdiv_qr (wmp_ptr, wmp_ptr, wmp_srcptr, wmp_size_t, wmp_srcptr, wmp_size_t);

void wmpn_tdiv_qr_in_place (wmp_ptr, wmp_srcptr, wmp_size_t, wmp_srcptr, wmp_size_t);

wmp_size_t wmpn_sqrtrem (wmp_ptr, wmp_ptr, wmp_srcptr, wmp_size_t);

#ifdef __cplusplus
}
#endif

#endif
