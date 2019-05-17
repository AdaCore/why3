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

#ifdef __cplusplus
}
#endif

#endif
