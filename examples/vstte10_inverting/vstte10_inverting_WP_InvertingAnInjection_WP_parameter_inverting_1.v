(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require map.Map.
Require map.Occ.
Require map.MapInjection.

Axiom array : forall (a:Type), Type.
Parameter array_WhyType :
  forall (a:Type) {a_WT:WhyType a}, WhyType (array a).
Existing Instance array_WhyType.

Parameter elts:
  forall {a:Type} {a_WT:WhyType a}, array a -> Numbers.BinNums.Z -> a.

Parameter length:
  forall {a:Type} {a_WT:WhyType a}, array a -> Numbers.BinNums.Z.

Axiom array'invariant :
  forall {a:Type} {a_WT:WhyType a},
  forall (self:array a), (0%Z <= (length self))%Z.

(* Why3 assumption *)
Definition mixfix_lbrb {a:Type} {a_WT:WhyType a} (a1:array a)
    (i:Numbers.BinNums.Z) : a :=
  elts a1 i.

Parameter mixfix_lblsmnrb:
  forall {a:Type} {a_WT:WhyType a}, array a -> Numbers.BinNums.Z -> a ->
  array a.

Axiom mixfix_lblsmnrb'spec'0 :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:array a) (i:Numbers.BinNums.Z) (v:a),
  ((length (mixfix_lblsmnrb a1 i v)) = (length a1)).

Axiom mixfix_lblsmnrb'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:array a) (i:Numbers.BinNums.Z) (v:a),
  ((elts (mixfix_lblsmnrb a1 i v)) = (map.Map.set (elts a1) i v)).

Parameter make:
  forall {a:Type} {a_WT:WhyType a}, Numbers.BinNums.Z -> a -> array a.

Axiom make_spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (n:Numbers.BinNums.Z) (v:a), (0%Z <= n)%Z ->
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < n)%Z ->
   ((mixfix_lbrb (make n v) i) = v)) /\
  ((length (make n v)) = n).

(* Why3 assumption *)
Definition injective (a:array Numbers.BinNums.Z) (n:Numbers.BinNums.Z) : Prop :=
  map.MapInjection.injective (elts a) n.

(* Why3 assumption *)
Definition surjective (a:array Numbers.BinNums.Z) (n:Numbers.BinNums.Z) :
    Prop :=
  map.MapInjection.surjective (elts a) n.

(* Why3 assumption *)
Definition range (a:array Numbers.BinNums.Z) (n:Numbers.BinNums.Z) : Prop :=
  map.MapInjection.range (elts a) n.

(* Why3 goal *)
Theorem inverting'vc :
  forall (a:array Numbers.BinNums.Z) (b:array Numbers.BinNums.Z)
    (n:Numbers.BinNums.Z),
  ((n = (length a)) /\ ((length a) = (length b))) /\
  injective a n /\ range a n ->
  let o := (n - 1%Z)%Z in
  (0%Z <= (o + 1%Z)%Z)%Z -> forall (b1:array Numbers.BinNums.Z),
  ((length b1) = (length b)) ->
  (forall (j:Numbers.BinNums.Z), (0%Z <= j)%Z /\ (j < (o + 1%Z)%Z)%Z ->
   ((mixfix_lbrb b1 (mixfix_lbrb a j)) = j)) ->
  injective b1 n.
(* Why3 intros a b n ((h1,h2),(h3,h4)) o h5 b1 h6 h7. *)
Proof.
intros a b n ((h1,h2),(h3,h4)) o h5 b1 h6 h7.
assert (MapInjection.surjective (elts a) n).
now apply MapInjection.injective_surjective.
intros i j h8 h9.
destruct (H i h8) as (i1,(Hi1,<-)).
destruct (H j h9) as (j1,(Hj1,<-)).
unfold o, mixfix_lbrb in h7.
rewrite h7 by auto with zarith.
rewrite h7 by auto with zarith.
intro h10.
contradict h10.
now rewrite h10.
Qed.

