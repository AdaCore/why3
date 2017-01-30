
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
l = range(0, 10)
## assert forall i. 0 <= i < 10 -> l[i] >= 0

# Local Variables:
# compile-command: "make -C ../.. && why3 ide test.py"
# End:
