
print("racine carrée entière")

n = int(input("entrez n : "))
#@ assume n >= 0

r = 0
s = 1
while s <= n:
    #@ invariant 0 <= r
    #@ invariant r * r <= n
    #@ invariant s == (r+1) * (r+1)
    #@ variant   n - s
    r += 1
    s += 2 * r + 1

print(r)
#@ assert r*r <= n < (r+1)*(r+1)
