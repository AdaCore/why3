
a = 0
b = 1
while b < 100:
  print(a)
  b = a+b
  a = b-a

# Local Variables:
# compile-command: "make -C ../.. && why3 ide test.py"
# End:
