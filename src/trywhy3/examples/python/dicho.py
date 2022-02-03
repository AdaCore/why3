
from random import randint

n = 42
a = [0] * n
#@ assert len(a) == n

a[0] = randint(0, 100)
for i in range(1, n):
    #@ invariant forall i1, i2. 0 <= i1 <= i2 < i -> a[i1] <= a[i2]
    a[i] = a[i-1] + randint(0, 10)

#@ assert forall i1, i2. 0 <= i1 <= i2 < len(a) -> a[i1] <= a[i2]

print(a)
v = int(input("quelle valeur cherchez-vous : "))

l = 0
u = n-1
r = -1
while l <= u:
    #@ invariant 0 <= l and u < n
    #@ invariant r == -1
    #@ invariant forall i. 0 <= i < n -> a[i] == v -> l <= i <= u
    #@ variant   u-l
    m = (l + u) // 2
    if a[m] < v:
        l = m+1
    elif a[m] > v:
        u = m-1
    else:
        r = m
        break

if r == -1:
    #@ assert forall i. 0 <= i < n -> a[i] != v
    print("valeur absente")
else:
    #@ assert a[r] == v
    print("position", r)

