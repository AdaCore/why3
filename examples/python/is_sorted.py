def is_sorted(l):
    #@ ensures result == (forall j1,j2. 0 <= j1 <= j2 < len(l) -> l[j1] <= l[j2])
    #@ label L
    for i in range(len(l)-1):
        #@ invariant forall j.     0 <= j        < i -> l[j]  <= l[j+1]
        #@ invariant forall j.     0 <= j        < i -> l[j]  == at(l[j], L)
        #@ invariant forall j1,j2. 0 <= j1 <= j2 < i -> l[j1] <= l[j2]
        if l[i+1] < l[i]:
            return False
    return True

a = [2,3,4]
a.sort()
c = is_sorted(a)

#@ assert c
