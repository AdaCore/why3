(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require map.Map.
Require map.Const.

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Implicit Arguments mk_ref [[a]].

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:(ref a)): a :=
  match v with
  | (mk_ref x) => x
  end.

Axiom set : forall (a:Type), Type.
Parameter set_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (set a).
Existing Instance set_WhyType.

Parameter mem: forall {a:Type} {a_WT:WhyType a}, a -> (set a) -> Prop.

Parameter infix_eqeq: forall {a:Type} {a_WT:WhyType a}, (set a) -> (set a) ->
  Prop.

Axiom infix_eqeq_spec : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (infix_eqeq s1 s2) <-> forall (x:a), (mem x s1) <-> (mem x
  s2).

Axiom extensionality : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (infix_eqeq s1 s2) -> (s1 = s2).

Parameter subset: forall {a:Type} {a_WT:WhyType a}, (set a) -> (set a) ->
  Prop.

Axiom subset_spec : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (subset s1 s2) <-> forall (x:a), (mem x s1) -> (mem x s2).

Axiom subset_refl : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  (subset s s).

Axiom subset_trans : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)) (s3:(set a)), (subset s1 s2) -> ((subset s2 s3) -> (subset s1
  s3)).

Parameter is_empty: forall {a:Type} {a_WT:WhyType a}, (set a) -> Prop.

Axiom is_empty_spec : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  (is_empty s) <-> forall (x:a), ~ (mem x s).

Parameter empty: forall {a:Type} {a_WT:WhyType a}, (set a).

Axiom empty_def : forall {a:Type} {a_WT:WhyType a}, (is_empty (empty : (set
  a))).

Parameter add: forall {a:Type} {a_WT:WhyType a}, a -> (set a) -> (set a).

Axiom add_spec : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (s:(set a)),
  forall (y:a), (mem y (add x s)) <-> ((y = x) \/ (mem y s)).

Parameter remove: forall {a:Type} {a_WT:WhyType a}, a -> (set a) -> (set a).

Axiom remove_spec : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (s:(set
  a)), forall (y:a), (mem y (remove x s)) <-> ((~ (y = x)) /\ (mem y s)).

Axiom add_remove : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (s:(set
  a)), (mem x s) -> ((add x (remove x s)) = s).

Axiom remove_add : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (s:(set
  a)), ((remove x (add x s)) = (remove x s)).

Axiom subset_remove : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (s:(set
  a)), (subset (remove x s) s).

Parameter union: forall {a:Type} {a_WT:WhyType a}, (set a) -> (set a) -> (set
  a).

Axiom union_spec : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), forall (x:a), (mem x (union s1 s2)) <-> ((mem x s1) \/ (mem x
  s2)).

Parameter inter: forall {a:Type} {a_WT:WhyType a}, (set a) -> (set a) -> (set
  a).

Axiom inter_spec : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), forall (x:a), (mem x (inter s1 s2)) <-> ((mem x s1) /\ (mem x
  s2)).

Parameter diff: forall {a:Type} {a_WT:WhyType a}, (set a) -> (set a) -> (set
  a).

Axiom diff_spec : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), forall (x:a), (mem x (diff s1 s2)) <-> ((mem x s1) /\ ~ (mem
  x s2)).

Axiom subset_diff : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (subset (diff s1 s2) s1).

Parameter choose: forall {a:Type} {a_WT:WhyType a}, (set a) -> a.

Axiom choose_spec : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  (~ (is_empty s)) -> (mem (choose s) s).

Parameter cardinal: forall {a:Type} {a_WT:WhyType a}, (set a) -> Z.

Axiom cardinal_nonneg : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  (0%Z <= (cardinal s))%Z.

Axiom cardinal_empty : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  ((cardinal s) = 0%Z) <-> (is_empty s).

Axiom cardinal_add : forall {a:Type} {a_WT:WhyType a}, forall (x:a),
  forall (s:(set a)), (~ (mem x s)) -> ((cardinal (add x
  s)) = (1%Z + (cardinal s))%Z).

Axiom cardinal_remove : forall {a:Type} {a_WT:WhyType a}, forall (x:a),
  forall (s:(set a)), (mem x s) -> ((cardinal s) = (1%Z + (cardinal (remove x
  s)))%Z).

Axiom cardinal_subset : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (subset s1 s2) -> ((cardinal s1) <= (cardinal s2))%Z.

Axiom subset_eq : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (subset s1 s2) -> (((cardinal s1) = (cardinal s2)) ->
  (infix_eqeq s1 s2)).

Axiom cardinal1 : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  ((cardinal s) = 1%Z) -> forall (x:a), (mem x s) -> (x = (choose s)).

Axiom vertex : Type.
Parameter vertex_WhyType : WhyType vertex.
Existing Instance vertex_WhyType.

Axiom t : Type.
Parameter t_WhyType : WhyType t.
Existing Instance t_WhyType.

Parameter contents1: t -> (set vertex).

Parameter is_empty1: t -> Prop.

Axiom is_empty_spec1 : forall (s:t), (is_empty1 s) <-> (is_empty
  (contents1 s)).

Parameter mem1: vertex -> t -> Prop.

Axiom mem_spec : forall (x:vertex) (s:t), (mem1 x s) <-> (mem x
  (contents1 s)).

Parameter cardinal2: t -> Z.

Axiom cardinal_spec : forall (s:t),
  ((cardinal2 s) = (cardinal (contents1 s))).

Axiom t1 : forall (a:Type), Type.
Parameter t1_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (t1 a).
Existing Instance t1_WhyType.

Parameter contents2: forall {a:Type} {a_WT:WhyType a}, (t1 a) -> (vertex ->
  a).

Parameter create: forall {a:Type} {a_WT:WhyType a}, a -> (t1 a).

Axiom create_spec : forall {a:Type} {a_WT:WhyType a}, forall (x:a),
  ((contents2 (create x)) = (map.Const.const x: (vertex -> a))).

Parameter mixfix_lbrb: forall {a:Type} {a_WT:WhyType a}, (t1 a) -> vertex ->
  a.

Axiom mixfix_lbrb_spec : forall {a:Type} {a_WT:WhyType a}, forall (m:(t1 a))
  (k:vertex), ((mixfix_lbrb m k) = ((contents2 m) k)).

Parameter mixfix_lblsmnrb: forall {a:Type} {a_WT:WhyType a}, (t1 a) ->
  vertex -> a -> (t1 a).

Axiom mixfix_lblsmnrb_spec : forall {a:Type} {a_WT:WhyType a}, forall (m:(t1
  a)) (k:vertex) (v:a), ((contents2 (mixfix_lblsmnrb m k
  v)) = (map.Map.set (contents2 m) k v)).

Parameter v: (set vertex).

Parameter g_succ: vertex -> (set vertex).

Axiom g_succ_spec : forall (x:vertex), (subset (g_succ x) v).

Parameter weight: vertex -> vertex -> Z.

Axiom weight_spec : forall (us:vertex) (us1:vertex), (0%Z <= (weight us
  us1))%Z.

(* Why3 assumption *)
Definition min (m:vertex) (q:t) (d:(t1 Z)): Prop := (mem1 m q) /\
  forall (x:vertex), (mem1 x q) -> ((mixfix_lbrb d m) <= (mixfix_lbrb d
  x))%Z.

(* Why3 assumption *)
Inductive path: vertex -> vertex -> Z -> Prop :=
  | Path_nil : forall (x:vertex), (path x x 0%Z)
  | Path_cons : forall (x:vertex) (y:vertex) (z:vertex), forall (d:Z), (path
      x y d) -> ((mem z (g_succ y)) -> (path x z (d + (weight y z))%Z)).

Axiom Length_nonneg : forall (x:vertex) (y:vertex), forall (d:Z), (path x y
  d) -> (0%Z <= d)%Z.

(* Why3 assumption *)
Definition shortest_path (x:vertex) (y:vertex) (d:Z): Prop := (path x y d) /\
  forall (d':Z), (path x y d') -> (d <= d')%Z.

Axiom Path_inversion : forall (src:vertex) (v1:vertex), forall (d:Z), (path
  src v1 d) -> (((v1 = src) /\ (d = 0%Z)) \/ exists v':vertex, (path src v'
  (d - (weight v' v1))%Z) /\ (mem v1 (g_succ v'))).

Axiom Path_shortest_path : forall (src:vertex) (v1:vertex), forall (d:Z),
  (path src v1 d) -> exists d':Z, (shortest_path src v1 d') /\ (d' <= d)%Z.

Axiom Main_lemma : forall (src:vertex) (v1:vertex), forall (d:Z), (path src
  v1 d) -> ((~ (shortest_path src v1 d)) -> (((v1 = src) /\ (0%Z < d)%Z) \/
  exists v':vertex, exists d':Z, (shortest_path src v' d') /\ ((mem v1
  (g_succ v')) /\ ((d' + (weight v' v1))%Z < d)%Z))).

Axiom Completeness_lemma : forall (s:t), (forall (v1:vertex), (mem1 v1 s) ->
  forall (w:vertex), (mem w (g_succ v1)) -> (mem1 w s)) ->
  forall (src:vertex), (mem1 src s) -> forall (dst:vertex), forall (d:Z),
  (path src dst d) -> (mem1 dst s).

(* Why3 assumption *)
Definition inv_src (src:vertex) (s:t) (q:t): Prop := (mem1 src s) \/ (mem1
  src q).

(* Why3 assumption *)
Definition inv (src:vertex) (s:t) (q:t) (d:(t1 Z)): Prop := (inv_src src s
  q) /\ (((mixfix_lbrb d src) = 0%Z) /\ ((subset (contents1 s) v) /\ ((subset
  (contents1 q) v) /\ ((forall (v1:vertex), (mem1 v1 q) -> ~ (mem1 v1 s)) /\
  ((forall (v1:vertex), (mem1 v1 s) -> (shortest_path src v1 (mixfix_lbrb d
  v1))) /\ forall (v1:vertex), (mem1 v1 q) -> (path src v1 (mixfix_lbrb d
  v1))))))).

(* Why3 assumption *)
Definition inv_succ (src:vertex) (s:t) (q:t) (d:(t1 Z)): Prop :=
  forall (x:vertex), (mem1 x s) -> forall (y:vertex), (mem y (g_succ x)) ->
  (((mem1 y s) \/ (mem1 y q)) /\ ((mixfix_lbrb d y) <= ((mixfix_lbrb d
  x) + (weight x y))%Z)%Z).

(* Why3 assumption *)
Definition inv_succ2 (src:vertex) (s:t) (q:t) (d:(t1 Z)) (u:vertex)
  (su:t): Prop := forall (x:vertex), (mem1 x s) -> forall (y:vertex), (mem y
  (g_succ x)) -> (((~ (x = u)) \/ ((x = u) /\ ~ (mem1 y su))) -> (((mem1 y
  s) \/ (mem1 y q)) /\ ((mixfix_lbrb d y) <= ((mixfix_lbrb d x) + (weight x
  y))%Z)%Z)).

(* Why3 goal *)
Theorem VC_shortest_path_code : forall (d:(t1 Z)), forall (src:vertex)
  (dst:vertex), ((mem src v) /\ (mem dst v)) -> forall (q:t) (d1:(t1 Z))
  (visited:t), ((is_empty1 visited) /\ (((contents1 q) = (add src
  (empty : (set vertex)))) /\ (d1 = (mixfix_lblsmnrb d src 0%Z)))) ->
  forall (q1:t) (d2:(t1 Z)) (visited1:t), ((inv src visited1 q1 d2) /\
  ((inv_succ src visited1 q1 d2) /\ forall (m:vertex), (min m q1 d2) ->
  forall (x:vertex), forall (dx:Z), (path src x dx) -> ((dx < (mixfix_lbrb d2
  m))%Z -> (mem1 x visited1)))) -> (((is_empty1 q1) <-> (is_empty
  (contents1 q1))) -> ((~ (is_empty1 q1)) -> forall (q2:t),
  forall (u:vertex), ((min u q1 d2) /\ ((contents1 q2) = (remove u
  (contents1 q1)))) -> ((shortest_path src u (mixfix_lbrb d2 u)) ->
  forall (visited2:t), ((contents1 visited2) = (add u
  (contents1 visited1))) -> forall (su:t), ((contents1 su) = (g_succ u)) ->
  forall (su1:t) (q3:t) (d3:(t1 Z)), ((subset (contents1 su1) (g_succ u)) /\
  ((inv src visited2 q3 d3) /\ (inv_succ2 src visited2 q3 d3 u su1))) ->
  (((is_empty1 su1) <-> (is_empty (contents1 su1))) -> ((is_empty1 su1) ->
  ((inv src visited2 q3 d3) -> ((inv_succ src visited2 q3 d3) ->
  forall (m:vertex), (min m q3 d3) -> forall (x:vertex), forall (dx:Z), (path
  src x dx) -> ((dx < (mixfix_lbrb d3 m))%Z -> (mem1 x visited2))))))))).
(* Why3 intros d src dst (h1,h2) q d1 visited (h3,(h4,h5)) q1 d2 visited1
        (h6,(h7,h8)) h9 h10 q2 u (h11,h12) h13 visited2 h14 su h15 su1 q3 d3
        (h16,(h17,h18)) h19 h20 h21 h22 m h23 x dx h24 h25. *)
intros d src dst (h1,h2) q d1 visited (h3,(h4,h5)) q1 d2 visited1
(h6,(h7,h8)) h9 h10 q2 u (h11,h12) h13 visited2 h14 su h15 su1 q3 d3
(h16,(h17,h18)) h19 h20 h21 h22 m h23 x dx h24 h25.

Qed.

Require Import Why3.
Ltac ae := why3 "Alt-Ergo,0.99.1," timelimit 10; admit.
Require Import Classical.

Lemma inside_or_exit:
  forall s src v d, mem src s -> path src v d ->
  mem v s
  \/
  exists y, exists z, exists dy,
    mem y s /\ not (mem z s) /\ mem z (g_succ y) /\ path src y dy /\ (dy + weight y z <= d)%Z.
induction 2.
auto.
rename x into src.
destruct (classic (mem z s)).
auto.
destruct (IHpath H).
destruct (classic (mem z s)).
auto.
right.
exists y; exists z.
exists d; intuition.
ae.
Admitted.


(* Unused content named WP_parameter_shortest_path_code
intros src dst d (h1,h2) q d1 visited (h3,(h4,h5)) q1 d2 visited1
        (h6,(h7,h8)) o h9 h10 h11 q2 u (h12,h13) h14 visited2 h15 su q3 d3
        (h16,(h17,h18)) result h19 h20 m h21 x dx h22 h23.

assert (is_empty su) by ae.
clear  result h19 h20.
assert (inv_succ src visited2 q3 d3).
  unfold inv_succ. split; ae.
assert (mem src visited2) by ae.

destruct (inside_or_exit visited2 src x dx); auto.
destruct H2 as (y, (z, (dy, (a1, (a2, (a3, (a4, a5))))))).
unfold min in h21.
assert (mem z q3) by ae.
assert (Map.get d3 z <= Map.get d3 y + weight y z)%Z 
 by ae.
assert (dy = Map.get d3 y) by ae.
ae.
Admitted.
 *)