
a = 0
b = 1
while b < 100:
  #@ invariant b >= a >= 0
  #@ invariant b >= 1
  #@ variant 200 - b - a
  print(a)
  b = a+b
  #@ assert b >= 1
  a = b-a

# lists
l = range(0, 10)
#@ assert forall i. 0 <= i < 10 -> l[i] >= 0
l[2] = 42
#@ assert l[2] == 42
i = 0
while i < 10:
  #@ invariant 0 <= i
  #@ invariant forall j. 0 <= j < i -> l[j] == 0
  #@ variant 10 - i
  l[i] = 0
  i = i+1

sum = 0
for x in l:
  #@ invariant sum >= 0
  print(x)
  #@ assert x >= 0
  sum = sum+x

# Python's division is neither Euclidean division, nor computer division
#@ assert  4 //  3 ==  1 and  4 %  3 ==  1
#@ assert -4 //  3 == -2 and -4 %  3 ==  2
#@ assert  4 // -3 == -2 and  4 % -3 == -2
#@ assert -4 // -3 ==  1 and -4 % -3 == -1

# Local Variables:
# compile-command: "make -C ../.. && why3 prove -P alt-ergo test.py"
# End:

