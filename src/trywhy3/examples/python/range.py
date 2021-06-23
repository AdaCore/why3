
s = 0

for x in range(100, -1, -1):
    #@ invariant s == 5050 - x*(x+1)//2
    s = s + x

#@ assert s == 5050

s = 0

for x in range(1, 100, 2):
    #@ invariant s == x'index * (2*x'index + 1)
    s = s + x + x+1

#@ assert s == 5050
