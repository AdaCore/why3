

(*********************

{1 A reduction engine for Why3 terms}

*************************)

(*
terms are normalized with respect to

1) built-in computation rules

 a) on propositional connectives, e.g.

   f /\ true -> f

 b) on integers, e.g.

   35 + 7 -> 42

 c) on projections of pairs and of other ADTs, e.g

  fst (x,y) -> x

  cdr (Cons x y) -> y

 d) on defined function symbols, e.g.

  function sqr (x:int) = x * x

  sqr 4 -> 4 * 4 -> 16

  sqr x -> x * x

 e) (TODO?) on booleans, e.g.

  True xor False -> True

 f) (TODO?) on reals, e.g.

  1.0 + 2.5 -> 3.5

2) axioms declared as rewrite rules, thanks to the "rewrite" metas, e.g. if

    function dot : t -> t -> t
    axiom assoc: forall x y z, dot (dot x y) z = dot x (dot y z)
    meta "rewrite" assoc

  then

  dot (dot a b) (dot c d) -> dot a (dot b (dot c d))

  axioms used as rewrite rules must be either of the form

    forall ... t1 = t2

  or

    forall ... f1 <-> f2

   where the root symbol of t1 (resp. f1) is a non-interpreted function
   symbol (resp. non-interpreted predicate symbol)

  rewriting is done from left to right


*)

type engine

val normalize : engine -> Term.term -> Term.term

val create : unit -> engine

exception NotARewriteRule of string

val add_rule : Term.term -> engine -> engine

