Require Import Why3.

Inductive Why3Unhabited : Prop := .
Axiom letUsTrustWhy3 : Why3Unhabited.

Ltac ae := why3 "alt-ergo" timelimit 5 ; case letUsTrustWhy3.
Ltac z3 := why3 "z3" timelimit 5; case letUsTrustWhy3.

Require Export ZArith.
Open Scope Z_scope.
Require Export Lists.List.

Section S0.
  Variable a:Set->Set.

  Goal forall b:Set->Set, forall x:a nat, x=x.
    intros; ae.
  Qed.

Goal
  forall f: (nat->nat)->nat, f S = O -> True.
intros; ae.
Qed.

End S0.

(* Mutually inductive types *)

Inductive tree : Set :=
  | Leaf : tree
  | Node : Z -> forest -> tree
with forest : Set :=
  | Nil : forest
  | Cons : tree -> forest -> forest.

Fixpoint tree_size (t:tree) : Z := match t with
  | Leaf => 0
  | Node _ f => 1 + forest_size f end
with forest_size (f:forest) : Z := match f with
  | Nil => 0
  | Cons t f => tree_size t + forest_size f end.


Goal tree_size (Node 42 (Cons Leaf Nil)) = 1.
ae.
Qed.

Goal (match Leaf with Leaf => 1 | Node z f => 2 end)=1.
ae.
Qed.

Inductive foo : Set :=
  | OO : foo
  | SS : forall x:nat, p x -> foo
with p : nat -> Prop :=
  | cc : p O.

Goal p O.
(* not a first order goal *)
try ae.
exact cc.
Qed.

Inductive fooo : nat -> Prop :=
  c : bar O -> fooo O
with bar : nat -> Prop :=
  d : forall f:nat->nat, bar (f O).

Goal fooo O.
(* Don't know *)
try ae.
exact (c (d (fun x => O))).
Qed.

Inductive tree' : Set :=
  | Empty' : tree'
  | Node' : forest' -> tree'
with forest' : Set :=
  | Forest' : (nat -> tree') -> forest'.

Goal forall f: nat ->tree, True.
intros.
ae.
Qed.

Parameter f : (nat -> nat) -> nat.

Goal f (plus O) = f (plus O).
(* not a first order goal *)
try ae.
trivial.
Qed.

Parameter f' : nat -> nat.

Axiom f'_def: f' O = O.

Goal f' (f' O) = O.
ae.
Qed.

Variable b:Set.

Section S.

Variable b:Set->Set.

Variable a:Set.

Inductive sorted : list a -> Prop :=
  ccc: sorted (@nil a)
| ddd: forall x: a, sorted (cons x nil).

Variable f : a -> a.

Goal True.
ae.
Qed.

Goal forall x: a, f (f x) = f x -> f (f (f x)) = f x.
intros.
ae.
Qed.

Goal forall l: list a, l=l.
ae.
Qed.

End S.

Goal True.
ae.
Qed.

Parameter par: Z -> Prop.

(* let in *)
Goal
  let t := Z in
  let f := par 0 in
  (forall x:t, par x -> par (let y := x+1 in y)) ->
  f -> par 1.
ae.
Qed.

(* cast *)
Goal
  (
  (forall x:Z, par x -> par (x+1)) -> par (0 : Z) -> par 1 : Prop).
ae.
Qed.

(* type definitions *)

Parameter t : Set -> Set.

Inductive foobar : Set :=
  C : t nat -> foobar.

Goal forall x:foobar, x=x.
intros.
ae.
Qed.

(* predicate definition *)

Definition p' (x:nat) := x=O.

Goal p' O.
ae.
Qed.

Goal plus O O = O.
ae.
Qed.


Definition eq' (A:Set) (x y : A) := x=y.

Goal
  eq' nat O O.
ae.
Qed.

Definition pred (n:nat) := match n with 
  | O => O
  | S p => p
  end.

Goal pred (S O) = O.
ae.
Qed.

(* function definition *)

Definition ff (x:Z) (y:Z) := x+y.

Goal ff 1 2 = 3.
ae.
Qed.

Definition id A (x:A) := x.

Goal id nat O = O.
ae.
Qed.

(* recursive function definition *)

Goal length (cons 1 (cons 2 nil)) = S (S O).
ae.
Qed.

(* recursive predicate definition *)

Goal In 0 (cons 1 (cons 0 nil)).
ae.
Qed.

(* inductive types *)

Parameter P : (nat -> nat) -> Prop.

Goal forall (a:Set), forall x:nat, x=S O -> P S -> 
  let y := (S (S O)) in S x=y.
intros.
ae.
Qed.

Goal  forall (a:Set), forall x:Z, x=1 -> P S -> let y := 2 in x+1=y.
intros.
ae.
Qed.

Goal  forall x: list nat, x=x.
intros.
ae.
Qed.

Goal (match (S (S (S O))) with (S (S _)) => True | _ => False end).
ae.
Qed.


Goal
  forall a, forall (x: list (list a)), 
  1<=2 -> match x with nil => 1 | x :: r => 2 end <= 2.
intros a x.
assert (x=nil \/ exists y: list a, exists z:list (list a),
                 x = cons y z).
destruct x; ae.
ae.
Qed.


(* Polymorphic, Mutually inductive types *)

Inductive ptree {a:Set} : Set :=
  | PLeaf : ptree
  | PNode : a -> pforest -> ptree

with pforest {a:Set} : Set :=
  | PNil : pforest
  | PCons : ptree -> pforest -> pforest.

Goal forall x : @ptree Z, x=x.
ae.
Qed.

Definition a := 0+0.
Definition bb := a.

Goal bb=0.
ae.
Qed.

Goal bb=0.
ae.
Qed.

Fixpoint ptree_size {a:Set} (t:@ptree a) : Z := match t with
  | PLeaf => 0
  | PNode _ f => 1 + pforest_size f end
with pforest_size {a:Set} (f:@pforest a) : Z := match f with
  | PNil => 0
  | PCons t f => ptree_size t + pforest_size f end.

Goal ptree_size (@PLeaf Z) = 0.
ae.
Qed.

Goal forall (a:Set), ptree_size (@PLeaf a) = 0.
intros.
ae.
Qed.

(* the same, without parameters *)

Inductive ptree' : Type -> Type :=
  | PLeaf' : forall (a:Type), ptree' a
  | PNode' : forall (a:Type), a -> pforest' a -> ptree' a

with pforest' : Type -> Type :=
  | PNil' : forall  (a:Type), pforest' a
  | PCons' : forall (a:Type), ptree' a -> pforest' a -> pforest' a.

Goal forall x : ptree' Z, x=x.
ae.
Qed.

(* order of type parameters matters *)

Definition wgt (k:(nat * Z)%type) := match k with
  | (_, p) => p
  end.
Implicit Arguments wgt.

Goal wgt (S O, 3) = 3.
ae.
Qed.

Require Import Rbase.
Require Import R_sqrt.
Require Import Rfunctions.
Require Import Rbasic_fun.

Goal forall (x:R), (0 <= x * x)%R.
ae.
Qed.
