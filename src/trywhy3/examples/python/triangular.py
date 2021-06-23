
print("somme des n premiers entiers")

n = int(input("entrez n : "))
#@ assume n >= 0

s = 0
k = 0
while k <= n:
    #@ invariant k <= n+1
    #@ invariant s == (k - 1) * k // 2
    #@ variant n - k
    s = s + k
    k = k + 1

print(s)
#@ assert s == n * (n+1) // 2
