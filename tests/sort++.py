
from random import randint

n = 42
a = [0] * n

### On remplit le tableau "a"

for i in range(0, len(a)):
    a[i] = randint(0, 100)

print(a)

### On prend une photo de "a"

photo = [0] * n
k = 0
while k < len(a):
    #@ invariant 0 <= k <= len(a)
    #@ invariant forall i. 0 <= i < k -> photo[i] == a[i]
    #@ variant len(a) - k
    photo[k] = a[k]
    k = k + 1

#@ assert forall i. 0 <= i < len(a) -> photo[i] == a[i]

### Et maintenant on le trie

m = 1
while m < len(a):
    #@ invariant 1 <= m <= len(a)
    #@ invariant forall i,j. 0 <= i <= j < m -> a[i] <= a[j]
    #@ invariant forall v. occurrence(v, a) == occurrence(v, photo)
    #@ variant   len(a) - m
    x = a[m]
    k = m
    while k > 0 and a[k-1] > x:
        #@ invariant 0 <= k <= m
        #@ invariant forall i,j. 0 <= i <= j < k               -> a[i] <= a[j]
        #@ invariant forall i,j. 0 <= i      < k <      j <= m -> a[i] <= a[j]
        #@ invariant forall i,j.               k < i <= j <= m -> a[i] <= a[j]
        #@ invariant forall   j.               k <      j <= m -> x    <  a[j]
        #@ invariant forall v. occurrence(v, a[k <- x]) == occurrence(v, photo)
        #@ variant   k
        a[k] = a[k-1]
        k = k - 1
        #@ assert occurrence(x, a[k <- x]) == occurrence(x, photo)
    a[k] = x
    m = m + 1

#@ assert forall i,j. 0 <= i <= j < len(a) -> a[i] <= a[j]
#@ assert forall v. occurrence(v, a) == occurrence(v, photo)

print(a)

