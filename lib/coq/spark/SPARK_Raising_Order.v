Require Import BuiltIn.
Require Import Relation_Definitions.

Open Scope Z_scope.

(* Idea of the proof: by induction on (range := max_index - min_index)
The general proof of raising_order statement is in several steps:
- change the lemmas in order to get min_index and range instead of min_index and max_index
- prove raising_order_induction via trivial induction on range and use of transitive property
  lt_trans
- adapt this result to our use case *)

(* First proving a general lemma proving that a simple raising order is true for
   all types having a transitive relation *)
Lemma raising_order_induction:
  forall (T: Type) (f: int -> T) (lt_T: relation T) (lt_trans: transitive T lt_T)
    range min_index
    (* Raising Order hypothesis *)
    (Harr: forall k : int, min_index <= k <= min_index + Z.of_nat range ->
      k + 1 <= min_index + Z.of_nat range -> lt_T (f k) (f (k + 1))),
  (* New raising order conclusion *)
  forall (i j: int)
    (Hij: i < j)
    (Hjrange: min_index <= j <= min_index + Z.of_nat range)
    (Hirange: min_index <= i <= min_index + Z.of_nat range),
      lt_T (f i) (f j).
Proof.
induction range; intros.

(* Base case *)
{
 assert (i = min_index) by (rewrite Nat2Z.inj_0 in Hirange; omega).
 assert (j = min_index) by (rewrite Nat2Z.inj_0 in Hjrange; omega).
 subst. destruct (Z.lt_irrefl _ Hij).
}

(* Induction case *)
{
 (* There are 2 cases:
  - we can use the induction hypothesis directly because j <= min_index + range
  - we cannot because j = min_index + range + 1 *)
 assert (Hcase: j <= min_index + Z_of_nat range \/ j = min_index + Z_of_nat (S range)).
 {
  rewrite Nat2Z.inj_succ in Hjrange.
  rewrite <- Zplus_succ_r_reverse in Hjrange.
  destruct Hjrange. eapply Z.le_succ_r in H0. intuition. right. subst. simpl.
  rewrite Zpos_P_of_succ_nat. omega.
 }

 destruct Hcase as [Hjless | Hjeq].
 (* First case is easily proved *)
 {
  eapply IHrange; destruct Hjrange; eauto; try omega.
  intros. eapply Harr; simpl; intuition. rewrite Zpos_P_of_succ_nat. omega.
  rewrite Zpos_P_of_succ_nat. omega.
 }

 {
  assert (lt_T (f (j - 1)) (f j)).
  (* Some ugly transformation to get the property we need *)
  {
   pose (a := j-1). replace j with (a + 1).
   replace (a + 1 - 1) with a.
   eapply Harr; unfold a; eauto; try omega. omega.
   unfold a. omega.
  }

  (* Again we need two cases *)
  assert (j = i + 1 \/ i < (j - 1)) by omega.

  destruct H0.
  (* First case is easy *)
  { rewrite H0. eapply (Harr i); eauto. rewrite <- Hjeq. rewrite H0. omega. }

  {
   eapply lt_trans with (f (j - 1)); eauto.

   (* Adapted Harr_rec to use the induction hyptohesis *)
   assert (Harr_rec: forall k : int,
           min_index <= k <= min_index + Z.of_nat range ->
           k + 1 <= min_index + Z.of_nat range -> lt_T (f k) (f (k + 1))).
   {
    intros. eapply Harr.
    intuition. eapply Z.le_trans; eauto. simpl. rewrite Zpos_P_of_succ_nat. omega.
    eapply Z.le_trans; eauto. simpl. rewrite Zpos_P_of_succ_nat. omega.
   }

   (* Use induction hypothesis and prove last details *)
   eapply (IHrange min_index Harr_rec i (j-1)); try eapply H0; eauto; try omega.
   replace (Z.of_nat range) with (Z.of_nat (S range) - 1). omega.
   simpl Z.of_nat. rewrite Zpos_P_of_succ_nat. omega.
   replace (Z.of_nat range) with (Z.of_nat (S range) - 1). omega.
   simpl Z.of_nat. rewrite Zpos_P_of_succ_nat. omega.
  }
 }
}
Qed.

(* This is just adapting raising_order_induction to remove range from the statement *)
Lemma generic_raising_order:
  forall (T: Type) (lt_T: relation T) (lt_trans: transitive T lt_T) (f : int -> T) max_int min_int
    (Harr: forall i (Hirange: min_int <= i <= max_int), i + 1 <= max_int ->
      lt_T (f i) (f (i + 1))),
    forall i (Hirange: min_int <= i <= max_int) j (Hjrange: min_int <= j <= max_int),
      i < j -> lt_T (f i) (f j).
Proof.
intros.
pose (range := max_int - min_int).
assert (max_int = min_int + range). unfold range. omega.
rewrite H0 in *.
assert (Hrange: 0 <= range) by (unfold range in *; omega).
generalize (IZN range Hrange). intros Hex. destruct Hex as (n, Hn).
rewrite Hn in *. eapply raising_order_induction; eauto.
Qed.

(* This is just replacing the raising order hypothesis with the
   exact right one. (Should be about (i-1) and i not i and (i + 1) *)
Lemma generic_raising_order_minus:
  forall (T: Type) (lt_T: relation T) (lt_trans: transitive T lt_T) (f : int -> T) max_int min_int
    (Harr: forall i (Hirange: min_int <= i <= max_int), i - 1 >= min_int ->
      lt_T (f (i - 1)) (f i)),
    forall i (Hirange: min_int <= i <= max_int) j (Hjrange: min_int <= j <= max_int),
      i < j -> lt_T (f i) (f j).
Proof.
intros.
pose (range := max_int - min_int).
assert (max_int = min_int + range). unfold range. omega.
rewrite H0 in *.
assert (Hrange: 0 <= range) by (unfold range in *; omega).
generalize (IZN range Hrange). intros Hex. destruct Hex as (n, Hn).
rewrite Hn in *. eapply raising_order_induction; eauto.
intros. assert (k = (k + 1) - 1). ring.
rewrite H3. replace  (k + 1 - 1 + 1) with (k + 1) by ring.
eapply Harr; intuition.
Qed.
