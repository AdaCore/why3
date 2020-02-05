#ifndef UINT64GMP_H_INCLUDED

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include <alloca.h>

typedef unsigned __int128 uint128_t;

struct __mul64_double_result
{ uint64_t __field_0;
uint64_t __field_1;
};


#define UWtype uint64_t
#define UHWtype uint32_t
#define W_TYPE_SIZE 64
#define __ll_B ((UWtype) 1 << (W_TYPE_SIZE / 2))
#define __ll_lowpart(t) ((UWtype) (t) & (__ll_B - 1))
#define __ll_highpart(t) ((UWtype) (t) >> (W_TYPE_SIZE / 2))


#define umul_ppmm(w1, w0, u, v)						\
  do {									\
    UWtype __x0, __x1, __x2, __x3;					\
    UHWtype __ul, __vl, __uh, __vh;					\
    UWtype __u = (u), __v = (v);					\
									\
    __ul = __ll_lowpart (__u);						\
    __uh = __ll_highpart (__u);						\
    __vl = __ll_lowpart (__v);						\
    __vh = __ll_highpart (__v);						\
									\
    __x0 = (UWtype) __ul * __vl;					\
    __x1 = (UWtype) __ul * __vh;					\
    __x2 = (UWtype) __uh * __vl;					\
    __x3 = (UWtype) __uh * __vh;					\
									\
    __x1 += __ll_highpart (__x0);/* this can't give carry */		\
    __x1 += __x2;		/* but this indeed can */		\
    if (__x1 < __x2)		/* did we get it? */			\
      __x3 += __ll_B;		/* yes, add it in the proper pos. */	\
									\
    (w1) = __x3 + __ll_highpart (__x1);					\
    (w0) = (__x1 << W_TYPE_SIZE/2) + __ll_lowpart (__x0);		\
  } while (0)


#define __udiv_qrnnd_c(q, r, n1, n0, d) \
  do {									\
    UWtype __d1, __d0, __q1, __q0, __r1, __r0, __m;			\
									\
									\
    __d1 = __ll_highpart (d);						\
    __d0 = __ll_lowpart (d);						\
									\
    __q1 = (n1) / __d1;							\
    __r1 = (n1) - __q1 * __d1;						\
    __m = __q1 * __d0;							\
    __r1 = __r1 * __ll_B | __ll_highpart (n0);				\
    if (__r1 < __m)							\
      {									\
	__q1--, __r1 += (d);						\
	if (__r1 >= (d)) /* i.e. we didn't get carry when adding to __r1 */\
	  if (__r1 < __m)						\
	    __q1--, __r1 += (d);					\
      }									\
    __r1 -= __m;							\
									\
    __q0 = __r1 / __d1;							\
    __r0 = __r1  - __q0 * __d1;						\
    __m = __q0 * __d0;							\
    __r0 = __r0 * __ll_B | __ll_lowpart (n0);				\
    if (__r0 < __m)							\
      {									\
	__q0--, __r0 += (d);						\
	if (__r0 >= (d))						\
	  if (__r0 < __m)						\
	    __q0--, __r0 += (d);					\
      }									\
    __r0 -= __m;							\
									\
    (q) = __q1 * __ll_B | __q0;						\
    (r) = __r0;								\
  } while (0)


static inline struct __mul64_double_result mul64_double(uint64_t x, uint64_t y)
{
 struct __mul64_double_result result;
 umul_ppmm (result.__field_1, result.__field_0, x, y);
 return result;
}

static inline uint64_t div64_2by1(uint64_t ul, uint64_t uh, uint64_t d)
{
  uint64_t q, r;
  __udiv_qrnnd_c (q, r, uh, ul, d);
  return q;
  //return (((uint128_t)uh << 64) | ul) / d;
}


struct __add64_with_carry_result
{ uint64_t __field_0;
uint64_t __field_1;
};

static inline struct __add64_with_carry_result
add64_with_carry(uint64_t x, uint64_t y, uint64_t c)
{
struct __add64_with_carry_result result;
uint64_t r = x + y + c;
result.__field_0 = r;
if (r == x) result.__field_1 = c;
else result.__field_1 = (r < x);
return result;
}

struct __sub64_with_borrow_result
{ uint64_t __field_0;
uint64_t __field_1;
};

static inline struct __sub64_with_borrow_result
sub64_with_borrow(uint64_t x, uint64_t y, uint64_t b)
{
struct __sub64_with_borrow_result result;
uint64_t r = x - y - b;
result.__field_0 = r;
if (r > x) result.__field_1 = 1;
else if (r == x) result.__field_1 = b;
else result.__field_1 = 0;
return result;
}

struct __add64_3_result
{ uint64_t __field_0;
uint64_t __field_1;
};

static inline struct __add64_3_result add64_3(uint64_t x, uint64_t y, uint64_t z)
{
struct __add64_3_result result;
uint64_t r, c1, c2;
r = x + y;
c1 = r < y;
r += z;
c2 = r < z;
result.__field_1 = c1 + c2;
result.__field_0 = r;
return result;
}

struct __lsld64_result
{ uint64_t __field_0;
uint64_t __field_1;
};

static inline struct __lsld64_result lsld64(uint64_t x, uint64_t cnt)
{
struct __lsld64_result result;
result.__field_1 = x >> (64 - cnt);
result.__field_0 = x << cnt;
return result;
}


#define UINT64GMP_H_INCLUDED
#endif // UINT64GMP_H_INCLUDED
