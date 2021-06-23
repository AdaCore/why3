#@ predicate win(n)
#@ predicate lose(n)
#@ assume forall n. n >= 1 -> not lose(n) or not win(n)

#@ assume lose(1)
#@ assume forall n. n >= 1 and lose(n) -> win(n+1) \
#@   and win(n+2) and win(n+3)
#@ assume forall n. n >= 1 and win(n) and win(n+1) \
#@   and win(n+2) -> lose(n+3)

def lemma(n):
    #@ requires n >= 1
    #@ ensures  lose(n) <-> n % 4 == 1
    #@ variant  n
    if n >= 5:
        lemma(n-1)
        lemma(n-2)
        lemma(n-3)
        lemma(n-4)

start = int(input("start = "))
#@ assume start >= 1
n = start
while n >= 1:
    #@ invariant win(n) -> win(start)
    #@ variant n
    print(n, " matches")
    k = int(input("your turn: "))
    #@ assume k == 1 or k == 2 or k == 3
    #@ assume k <= n
    n = n - k
    if n == 0:
        print("you lose")
        break
    if n == 1:
        #@ assert win(start)
        print("you win")
        break
    m = n % 4
    if m == 1:
        k = 1
    elif m == 0:
        k = 3
    else:
        k = m - 1
    lemma(n)
    lemma(n-k)
    #@ assert win(n) -> lose(n - k)
    n -= k
