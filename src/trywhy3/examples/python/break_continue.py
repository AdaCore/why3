### Exemple pour break ###

s = 0

for i in range(100):
    #@ invariant s == i
    #@ invariant i < 11
    if i == 10:
        break
    s += 1

#@ assert s == 10




### Exemple pour continue ###

s = 0

for i in range(100):
    #@ invariant i <= 42 -> s == i*(i-1)//2
    #@ invariant i > 42 -> s + 42 == i*(i-1)//2
    if i == 42:
        continue
    s += i

#@ assert s == 4908
