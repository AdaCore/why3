
def fact(n):
    #@ ensures result >= 1
    #@ variant n
    if n <= 1:
        return 1
    return n * fact(n - 1)
