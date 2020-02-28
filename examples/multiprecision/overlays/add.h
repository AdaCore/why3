#ifndef ADDOLD_H_INCLUDED
#include <stdint.h>

static inline uint64_t wmpn_add_n1(uint64_t * r, uint64_t * x, uint64_t * y, int32_t sz) {
  extern uint64_t __gmpn_add_n(uint64_t * r, uint64_t * x, uint64_t * y, int32_t sz);
  return __gmpn_add_n(r, x, y, sz);
}

static inline uint64_t wmpn_add1(uint64_t * r, uint64_t * x, int32_t sx, uint64_t * y, int32_t sy) {
  extern uint64_t __gmpn_add(uint64_t * r, uint64_t * x, int32_t sx, uint64_t * y, int32_t sy);
  return __gmpn_add(r, x, sx, y, sy);
}

static inline uint64_t wmpn_add_n_in_place(uint64_t * x, uint64_t * y, int32_t sz) {
  extern uint64_t __gmpn_add_n(uint64_t * r, uint64_t * x, uint64_t * y, int32_t sz);
  return __gmpn_add_n(x, x, y, sz);
}

static inline uint64_t wmpn_add_in_place(uint64_t * x, int32_t sx, uint64_t * y, int32_t sy) {
  extern uint64_t __gmpn_add(uint64_t * r, uint64_t * x, int32_t sx, uint64_t * y, int32_t sy);
  return __gmpn_add(x, x, sx, y, sy);
}

#define ADDOLD_H_INCLUDED
#endif // ADDOLD_H_INCLUDED
