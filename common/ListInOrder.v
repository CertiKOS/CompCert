(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Oct 28, 2019 *)
(* *******************  *)

(** * Definition of a relation between elements in lists *)
Require Import Coqlib.
Require Import RelationClasses.
Import ListNotations.

Set Implicit Arguments.

(** This is useful in describing the relation that internal definitions are 
    in two lists are ordered in the same way and they one-to-one match with each other *)
Class PERWithFun (A:Type) (aeq:A -> A -> Prop) `{PER A aeq} (f:A -> bool) :=
{
  eq_imply_fun_true: forall e1 e2, aeq e1 e2 -> f e1 = true /\ f e2 = true;
  (** Equality between elements in a restricted domain *)
  fun_true_imply_eq: forall e, f e = true -> aeq e e;
}.

Section WithEquivAndFun.

Context `{PERWithFun}.

Inductive list_in_order : list A -> list A -> Prop :=
| lorder_nil : list_in_order nil nil
| lorder_left_false : forall e l1 l2, 
    f e = false -> list_in_order l1 l2 -> list_in_order (e :: l1) l2
| lorder_right_false : forall e l1 l2,
    f e = false -> list_in_order l1 l2 -> list_in_order l1 (e :: l2)
| lorder_true : forall e1 e2 l1 l2,
    aeq e1 e2 -> list_in_order l1 l2 -> list_in_order (e1::l1) (e2::l2).

Lemma list_in_order_false_inv : forall (l1' l1 l2: list A) e,
    f e = false -> l1' = (e :: l1) -> list_in_order l1' l2 -> list_in_order l1 l2.
Proof.
  induction 3. 
  - inv H2.
  - inv H2. auto.
  - apply lorder_right_false; auto.
  - subst. inv H2. apply eq_imply_fun_true in H3. destruct H3.
    congruence.
Qed.

Lemma list_in_order_true_inv : forall (l1' l1 l2: list A)  e1,
    f e1 = true -> l1' = (e1 :: l1) -> list_in_order l1' l2 -> 
    exists l3 l4 e2, l2 = l3 ++ (e2 :: l4) /\ 
             aeq e1 e2 /\
             Forall (fun e' => f e' = false) l3 /\
             list_in_order l1 l4.
Proof.
  induction 3.
  - inv H2.
  - inv H2. congruence.
  - subst. 
    generalize (IHlist_in_order eq_refl).
    destruct 1 as (l3 & l4 & e2 & EQ & EEQ & FP & ORDER). subst.
    exists (e :: l3), l4, e2. split.
    rewrite <- app_comm_cons. auto. split; auto.
  - inv H2. exists nil, l2, e2. split. auto.
    split; auto.
Qed.

Lemma list_in_order_right_false_list : forall (l2' l1 l2: list A),
    Forall (fun e : A => f e = false) l2' ->
    list_in_order l1 l2 -> 
    list_in_order l1 (l2' ++ l2).
Proof.
  induction l2'.
  - intros l1 l2 FALL ORDER. simpl. auto.
  - intros l1 l2 FALL ORDER. simpl. 
    generalize (Forall_inv FALL).
    intros FLS.
    apply lorder_right_false; auto.
    apply IHl2'; auto.
    rewrite Forall_forall in *.
    intros. apply FALL. apply in_cons. auto.
Qed.

Lemma list_in_order_symm : forall (l1 l2: list A),
    list_in_order l1 l2 -> list_in_order l2 l1.
Proof.
  intros l1 l2 ORDER. 
  induction ORDER.
  - constructor.
  - apply lorder_right_false; auto.
  - apply lorder_left_false; auto.
  - apply lorder_true; auto.
    apply PER_Symmetric. auto.
Qed.

Lemma list_in_order_trans : forall (l1 l2 l3: list A),
    list_in_order l1 l2 -> list_in_order l2 l3 -> list_in_order l1 l3.
Proof.
  intros l1 l2 l3 ORDER.
  generalize l3.
  induction ORDER.
  - auto.
  - intros l0 ORDER1. constructor; auto.
  - intros l0 ORDER1. 
    generalize (list_in_order_false_inv H1 (eq_refl (e::l2)) ORDER1). auto.
  - intros l0 ORDER1.
    generalize (eq_imply_fun_true _ _ H1). destruct 1 as (FEQ1 & FEQ2).
    generalize (list_in_order_true_inv FEQ2 (eq_refl (e2::l2)) ORDER1).
    destruct 1 as (l2' & l2'' & e3 & EQ & EEQ & ALL & ORDER2).
    subst.
    apply IHORDER in ORDER2.
    apply list_in_order_right_false_list; auto.
    apply lorder_true; auto.
    apply PER_Transitive with e2; auto.
Qed.    

Lemma list_in_order_cons : forall (l1 l2:list A) e,
    list_in_order l1 l2 -> list_in_order (e::l1) (e::l2).
Proof.
  intros l1 l2 e ORDER.
  destruct (f e) eqn:EQ.
  - apply lorder_true; auto.
    apply fun_true_imply_eq. auto.
  - apply lorder_left_false; auto.
    apply lorder_right_false; auto.
Qed.

Lemma list_in_order_refl: forall (l:list A),
    list_in_order l l.
Proof.
  induction l; intros.
  - apply lorder_nil.
  - apply list_in_order_cons. auto.
Qed.

Lemma list_in_order_app: forall (l1 l2 l1' l2': list A),
    list_in_order l1 l1' -> list_in_order l2 l2' -> 
    list_in_order (l1 ++ l2) (l1' ++ l2').
Proof.
  intros l1 l2 l1' l2' INORDER.
  generalize l2 l2'. induction INORDER.
  - intros. cbn. auto.
  - intros l3 l4 INORDER1. cbn.
    apply lorder_left_false; eauto.
  - intros l3 l4 INORDER1. cbn.
    apply lorder_right_false; eauto.
  - intros l3 l4 INORDER1. cbn.
    apply lorder_true; eauto.
Qed.

Lemma list_in_order_app_inv: forall (l1 l2 l: list A),
        list_in_order (l1 ++ l2) l ->
        exists l1' l2', l = l1' ++ l2' /\ 
                   list_in_order l1 l1' /\
                   list_in_order l2 l2'.
Proof.
  intros l1 l2 l IO.
  remember (l1 ++ l2) as l3.
  generalize dependent l2.
  generalize dependent l1.
  induction IO; cbn; intros.
  - symmetry in Heql3. apply app_eq_nil in Heql3. 
    destruct Heql3; subst; cbn.
    exists nil, nil. split; auto.
    split; constructor.
  - destruct l0; cbn in *; inv Heql3.
    + generalize (IHIO nil l1 eq_refl).
      intros (l1'' & l2'' & EQ & IO1 & IO2).
      subst.
      exists l1'', l2''. split; auto. split; auto.
      apply lorder_left_false; auto.
    + generalize (IHIO _ _ eq_refl).
      intros (l1'' & l2'' & EQ & IO1 & IO2).
      subst.
      exists l1'', l2''. split; auto. split; auto.
      apply lorder_left_false; auto.
  - subst.
    edestruct IHIO as (l1'' & l2'' & EQ & IO1 & IO2); eauto.
    subst.
    exists (e:: l1''), l2''. split; auto. split; auto.
    apply lorder_right_false; auto.
  - destruct l0; cbn in *; inv Heql3.
    + edestruct (IHIO nil l1 eq_refl) as (l1'' & l2'' & EQ & IO1 & IO2); eauto.
      subst.
      exists nil. eexists; cbn; split; eauto.
      split. constructor.
      apply lorder_true; auto.
    + edestruct IHIO as (l1'' & l2'' & EQ & IO1 & IO2); eauto.
      subst.
      exists (e2::l1''). eexists; cbn; split; eauto.
      split; auto.
      apply lorder_true; auto.
Qed.

Lemma partition_pres_list_in_order: forall pf (l l1 l2: list A),
    partition pf l = (l1, l2) ->
    Forall (fun e => f e = false) l1 ->
    list_in_order l l2.
Proof.
  induction l.
  - intros l1 l2 PART ALL. simpl in *. inv PART. constructor.
  - intros l1 l2 PART ALL. simpl in *.
    destruct (pf a).
    + destruct (partition pf l) eqn:PART1. inv PART.
      apply lorder_left_false. 
      apply Forall_inv in ALL. auto.
      apply IHl with l0; auto.
      rewrite Forall_forall in *. intros. 
      apply ALL; auto. apply in_cons. auto.
    + destruct (partition pf l) eqn:PART1. inv PART.
      apply list_in_order_cons. 
      apply IHl with l1; auto.
Qed.

End WithEquivAndFun.

Arguments list_in_order [A] _ _ _ _.