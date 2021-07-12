def concat(l1, l2):
    #@ ensures len(result) == len(l1) + len(l2)
    #@ ensures forall i. 0 <= i < len(l1) -> result[i] == l1[i]
    #@ ensures forall i. 0 <= i < len(l2) -> result[len(l1) + i] == l2[i]

    size1 = len(l1)
    size2 = len(l2)
    size = size1 + size2

    res = [-1] * size

    for i in range(size1):
        #@ invariant forall j. 0 <= j < i -> res[j] == l1[j]
        res[i] = l1[i]

    for i in range(size2):
        #@ invariant forall j. 0 <= j < i -> res[len(l1) + j] == l2[j]
        #@ invariant forall j. 0 <= j < len(l1) -> res[j] == l1[j]
        res[size1 + i] = l2[i]
    
    return res
