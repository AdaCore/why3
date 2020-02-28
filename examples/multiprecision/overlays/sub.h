#ifndef SUBOLD_H_INCLUDED
#include <stdint.h>

static inline uint64_t wmpn_sub_n1(uint64_t * r, uint64_t * x, uint64_t * y, int32_t sz) {
  extern uint64_t __gmpn_sub_n(uint64_t * r, uint64_t * x, uint64_t * y, int32_t sz);
  return __gmpn_sub_n(r, x, y, sz);
}

static inline uint64_t wmpn_sub1(uint64_t * r, uint64_t * x, int32_t sx, uint64_t * y, int32_t sy) {
  extern uint64_t __gmpn_sub(uint64_t * r, uint64_t * x, int32_t sx, uint64_t * y, int32_t sy);
  return __gmpn_sub(r, x, sx, y, sy);
}

static inline uint64_t wmpn_sub_n_in_place(uint64_t * x, uint64_t * y, int32_t sz) {
  extern uint64_t __gmpn_sub_n(uint64_t * r, uint64_t * x, uint64_t * y, int32_t sz);
  return __gmpn_sub_n(x, x, y, sz);
}

static inline uint64_t wmpn_sub_in_place(uint64_t * x, int32_t sx, uint64_t * y, int32_t sy) {
  extern uint64_t __gmpn_sub(uint64_t * r, uint64_t * x, int32_t sx, uint64_t * y, int32_t sy);
  return __gmpn_sub(x, x, sx, y, sy);
}

#define SUBOLD_H_INCLUDED
#endif // SUBOLD_H_INCLUDED
