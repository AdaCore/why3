###################################################
#                 ...[expr] += ...                #
###################################################

def side_effect1(tab):
    #@ ensures result == 0
    #@ ensures len(tab) == len(old(tab)) + 1
    tab.append(1)
    return 0

a = [0]
tab = []

a[side_effect1(tab)] += 1

#@ assert a[0] == 1
#@ assert len(tab) == 1


###################################################
#                 expr[...] += ...                #
###################################################

def side_effect2(tab):
    #@ ensures result[0] == 0
    #@ ensures len(result) == 1
    #@ ensures len(tab) == len(old(tab)) + 1
    tab.append(1)
    return [0]

tab.clear()

side_effect2(tab)[0] += 1

#@ assert len(tab) == 1


###################################################
#                     expr[:]                     #
###################################################

def side_effect3(tab):
    #@ ensures len(result) == 3
    #@ ensures len(tab) == len(old(tab)) + 1
    tab.append(1)
    return [0, 1, 2]

tab.clear()

side_effect3(tab)[:]

#@ assert len(tab) == 1
