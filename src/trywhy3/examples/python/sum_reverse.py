def sum_reverse (l):
    #@ ensures result == 0
    l2 = l.copy()
    l2.reverse()
    t = 0
    for i in range (len(l)):
        #@ invariant t == 0
        t += l[i]
        t -= l2[-(i+1)]
    return t
