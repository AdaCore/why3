
print("la multiplication dite russe")

a = int(input("entrez a : "))
b = int(input("entrez b : "))

p = a
q = b

if q < 0:
    p = -a
    q = -b

#@ assert q >= 0

r = 0
while q > 0:
    #@ invariant 0 <= q
    #@ invariant r + p * q == a * b
    #@ variant   q
    print(p, q, r)
    if q % 2 == 1:
        r = r + p
    p = p + p
    q = q // 2
print(p, q, r)
print("a * b =", r)
#@ assert r == a * b
