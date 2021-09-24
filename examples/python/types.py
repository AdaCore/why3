
#@ function f(x: list) -> int

def test1(x):
    #@ requires f(x) == f(x)
    return len(x)

print(test1([1,2,3]))

#@ function g(x: list[int]) -> int

#@ assume forall l. g(l) == len(l)

def test2(x):
    #@ requires x[0] == 1
    #@ requires len(x) == 3
    #@ ensures result > g(x)
    return x[0] + len(x)

print(test2([1,2,3]))

