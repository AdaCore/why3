
# same as sqrt.py, but with a function

def isqrt(n):
    #@ requires n >= 0
    #@ ensures  result * result <= n < (result + 1) * (result + 1)
    r = 0
    s = 1
    while s <= n:
        #@ invariant 0 <= r
        #@ invariant r * r <= n
        #@ invariant s == (r+1) * (r+1)
        #@ variant   n - s
        r = r + 1
        s = s + 2 * r + 1
    return r
