Declare ML Module "whytac".
Require Export ZArith.
Open Scope Z_scope.
Require Export List.

Ltac ae := why3 "alt-ergo".
Ltac Z3 := why3 "z3-2".
Ltac spass := why3 "spass".

Inductive sorted (a:Set) : list a -> Prop :=
  c: sorted _ (@nil a)
| d: forall x: a, sorted _ (cons x nil).


Goal sorted _ (@nil Z).
ae.


Parameter p: Z -> Prop.

(* let in *)
Goal
  let t := Z in
  let f := p 0 in
  (forall x:t, p x -> p (let y := x+1 in y)) ->
  f -> p 1.
ae.

(* cast *)
Goal
  (
  (forall x:Z, p x -> p (x+1)) -> p (0 : Z) -> p 1 : Prop).
ae.
Qed.


(* type definitions *)

Definition t := list.

Inductive foo : Set :=
  C : t nat -> foo.

Goal forall x:foo, x=x.
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

Definition f (x:Z) (y:Z) := x+y.

Goal f 1 2 = 3.
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


Goal tree_size Leaf = 0.
ae.
Qed.

Goal (match Leaf with Leaf => 1 | Node z f => 2 end)=1.
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
Definition b := a.

Goal b=0.
ae.
Qed.

Goal b=0.
ae.


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

