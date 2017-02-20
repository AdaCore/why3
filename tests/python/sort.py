
from random import randint

n = 42
a = [0] * n

### On remplit le tableau "a"

for i in range(0, len(a)):
    a[i] = randint(0, 100)

print(a)

### Et maintenant on le trie

m = 1
while m < len(a):
    #@ invariant 1 <= m <= len(a)
    #@ invariant forall i,j. 0 <= i <= j < m -> a[i] <= a[j]
    #@ variant   len(a) - m
    x = a[m]
    k = m
    while k > 0 and a[k-1] > x:
        #@ invariant 0 <= k <= m
        #@ invariant forall i,j. 0 <= i <= j < k               -> a[i] <= a[j]
        #@ invariant forall i,j. 0 <= i      < k <      j <= m -> a[i] <= a[j]
        #@ invariant forall i,j.               k < i <= j <= m -> a[i] <= a[j]
        #@ invariant forall   j.               k <      j <= m -> x    <  a[j]
        #@ variant   k
        a[k] = a[k-1]
        k = k - 1
    a[k] = x
    m = m + 1

#@ assert forall i,j. 0 <= i <= j < len(a) -> a[i] <= a[j]

print(a)

