
from random import randint

m = randint(0, 100)
print("j'ai choisi un nombre entre 0 et 100")
print("vous devez le trouver")
tentatives = 0
while True:
    x = int(input("votre choix : "))
    tentatives = tentatives + 1
    print(x)
    if x < 0 or x > 100:
        print("j'ai dit entre 0 et 100")
    elif x < m:
        print("trop petit")
    elif x > m:
        print("trop grand")
    else:
        print("bravo !")
        print("en", tentatives, "tentatives")
        break

