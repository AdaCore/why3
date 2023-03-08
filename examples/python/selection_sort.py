def tri_selection(L):
    #@ ensures forall i. forall j. 0<=i<j<len(L) -> L[i]<=L[j]
    im = 0
    for i in range(len(L)):
        #@ invariant forall k. forall l. 0<=k<i<=l<len(L) -> L[k]<=L[l]
        #@ invariant forall k. forall l. 0<=k<=l<i -> L[k]<=L[l]
        im = i
        for j in range(i+1,len(L)):
            #@ invariant i<=im<j
            #@ invariant forall k. i<=k<j -> L[im]<=L[k]
            if L[j]<L[im]:
                im = j
        if im != i:
            L[im], L[i] = L[i], L[im]
        #@ assert forall k. 0<=k<i -> L[k]<=L[i]
