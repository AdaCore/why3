#
# 'Checking a large routine' Alan Mathison Turing, 1949
#

#@ function factorial(n: int) -> int

#@ assume factorial(0) == 1

#@ assume forall n. n > 0 -> factorial(n) == n * factorial(n-1)

def routine(n):
    #@ requires n >= 0
    #@ ensures  result == factorial(n)
    u = 1
    for r in range(n):
        #@ invariant u == factorial(r)
        v = u
        for s in range(1, r+1):
            #@ invariant u == s * factorial(r)
            u += v
    return u
