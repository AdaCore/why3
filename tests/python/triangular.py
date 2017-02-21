
print("somme des n premiers entiers")

n = int(input("entrez n : "))
#@ assume n >= 0

s = 0
k = 0
while k <= n:
    #@ invariant 0 <= k <= n+1
    #@ invariant 2 * s == (k - 1) * k
    s = s + k
    k = k + 1

print(s)
#@ assert 2 * s == n * (n+1)
