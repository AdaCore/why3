
a = 0
b = 1
while b < 100:
  ## invariant b >= a >= 0
  ## invariant b >= 1
  ## variant 200 - b - a
  print(a)
  b = a+b
  ## assert b >= 1
  a = b-a

# lists
l = range(0, 10)
## assert forall i. 0 <= i < 10 -> l[i] >= 0
l[2] = 42
## assert l[2] == 42
i = 0
while i < 10:
  ## invariant 0 <= i
  ## invariant forall j. 0 <= j < i -> l[j] == 0
  ## invariant len(l) == 10
  l[i] = 0
  i = i+1

# arithmetic
# Python's division is *Euclidean* division
q = -4 // 3
## assert q == -2
r = -4 % 3
## assert r == 2
## assert 4 // -3 == -2
## assert 4 % -3 == -2

# Local Variables:
# compile-command: "make -C ../.. && why3 ide test.py"
# End:
