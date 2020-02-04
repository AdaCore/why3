#ifndef MUL_H_INCLUDED
#include <stdint.h>

static inline uint64_t wmpn_mul_1(uint64_t * r, uint64_t * x, int32_t sz, uint64_t y) {
  extern uint64_t __gmpn_mul_1(uint64_t * r, uint64_t * x, int32_t sz, uint64_t y);
  return __gmpn_mul_1(r, x, sz, y);
}

static inline uint64_t wmpn_addmul_1(uint64_t * r, uint64_t * x, int32_t sz, uint64_t y) {
  extern uint64_t __gmpn_addmul_1(uint64_t * r, uint64_t * x, int32_t sz, uint64_t y);
  return __gmpn_addmul_1(r, x, sz, y);
}

static inline uint64_t wmpn_mul_1_in_place(uint64_t * x, int32_t sz, uint64_t y) {
  extern uint64_t __gmpn_mul_1(uint64_t * r, uint64_t * x, int32_t sz, uint64_t y);
  return __gmpn_mul_1(x, x, sz, y);
}

static inline uint64_t wmpn_submul_1(uint64_t * r, uint64_t * x, int32_t sz, uint64_t y) {
  extern uint64_t __gmpn_submul_1(uint64_t * r, uint64_t * x, int32_t sz, uint64_t y);
  return __gmpn_submul_1(r, x, sz, y);
}

static inline uint64_t wmpn_addmul_2(uint64_t * r, uint64_t * x, int32_t sz, uint64_t * y) {
  extern uint64_t __gmpn_addmul_2(uint64_t * r, uint64_t * x, int32_t sz, uint64_t * y);
  return __gmpn_addmul_2(r, x, sz, y);
}

#define MUL_H_INCLUDED
#endif // MUL_H_INCLUDED
