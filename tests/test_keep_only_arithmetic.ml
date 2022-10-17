use int.Int

predicate is_toto (x:int)
predicate is_titi (x:int)
predicate is_tata (x:int)

constant x:int

axiom c : is_tata x -> is_titi x
axiom a: is_titi x -> x >= 3
axiom hello : is_toto x
axiom b: is_toto x -> is_tata x


goal g: x * x >= 9
