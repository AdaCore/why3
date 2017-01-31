
a = int(input("entrez a : "))
b = int(input("entrez b : "))

#@ assume b >= 0

p = a
q = b
r = 0
while q > 0:
    #@ invariant 0 <= q and r + p * q == a * b
    #@ variant   q
    if q % 2 == 1:
        r = r + p
    p = p + p
    q = q // 2

print(r)
#@ assert r == a * b
