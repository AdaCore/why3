def check_duplicates(elt, tab):
    #@ ensures result == occurrence(elt, tab, 0, len(tab))
    nb = 0
    for e in tab:
        #@ invariant nb == occurrence(elt, tab, 0, e'index)
        if e == elt:
            nb += 1
    return nb
