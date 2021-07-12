
def pgcd(a, b):
    #@ requires a > 0 and b > 0
    while a != b:
        #@ invariant a > 0 and b > 0
        #@ variant a + b
        if a < b:
            b -= a
        else:
            a -= b
    return a

