Require Import Why3.
Require Export ZArith.
Open Scope Z_scope.
Require Export List.

Ltac ae := why3 "alt-ergo".

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

Print plus.

Print tree_rect.


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


Definition t (a:Type) := list a.

(*
Inductive foo : Set :=
  | OO : foo
  | SS : forall x:nat, p x -> foo
with p : nat -> Prop :=
  | cc : p O.

Goal p O.
ae.
*)

Inductive foo : nat -> Prop :=
  c : bar O -> foo O
with bar : nat -> Prop :=
  d : forall f:nat->nat, bar (f O).

(*
Goal foo O.
ae.
*)

Inductive tree' : Set :=
  | Empty' : tree'
  | Node' : forest' -> tree'
with forest' : Set :=
  | Forest' : (nat -> tree') -> forest'.

(*
Goal forall f: nat ->tree, True.
intros.
ae.
*)

(*
Parameter f : (nat -> nat) -> nat.

Goal f (plus O) = f (plus O).
ae.
Qed.*)

Parameter f: nat -> nat.

Axiom f_def: f O = O.

Goal f (f O) = O.
ae.
Qed.

Variable b:Set.

Section S.

Variable b:Set->Set.

Variable a:Set.

Inductive sorted : list a -> Prop :=
  cc: sorted (@nil a)
| dd: forall x: a, sorted (cons x nil).

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

Print All.

Goal True.
ae.
Qed.

Print sorted.

Goal sorted _ (@nil nat).
ae.
Qed.

Parameter p: Z -> Prop.

(* let in *)
Goal
  let t := Z in
  let f := p 0 in
  (forall x:t, p x -> p (let y := x+1 in y)) ->
  f -> p 1.
ae.
Qed.

(* cast *)
Goal
  (
  (forall x:Z, p x -> p (x+1)) -> p (0 : Z) -> p 1 : Prop).
ae.
Qed.


(* type definitions *)

Inductive foobar : Set :=
  C : list nat -> foobar.

Goal forall x:foobar, x=x.
intros.
ae.
Qed.

(* predicate definition *)

Definition p' (x:nat) := x=O.

Goal p' O.
ae.
Qed.

Print plus.

Goal plus O O = O.
ae.
Qed.


Definition eq' (A:Set) (x y : A) := x=y.

Goal
  eq' nat O O.
ae.
(*
why "z3".  (* BUG encoding decorate ici ? *)
Qed.
*)
Admitted.

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

Print In.

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

Inductive ptree (a:Set) : Set :=
  | PLeaf : ptree a
  | PNode : a -> pforest a -> ptree a

with pforest (a:Set) : Set :=
  | PNil : pforest a
  | PCons : ptree a -> pforest a -> pforest a.

Goal forall x : ptree Z, x=x.
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

Fixpoint ptree_size (a:Set) (t:ptree a) : Z := match t with
  | PLeaf => 0
  | PNode _ f => 1 + pforest_size _ f end
with pforest_size (a:Set) (f:pforest a) : Z := match f with
  | PNil => 0
  | PCons t f => ptree_size _ t + pforest_size _ f end.

Goal ptree_size _ (@PLeaf Z) = 0.
ae.
Qed.

Goal forall (a:Set), ptree_size a (PLeaf a) = 0.
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

