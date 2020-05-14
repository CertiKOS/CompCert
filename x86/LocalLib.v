(* ********************* *)
(* Author: Author A   *)
(* Date:   Feb 31, 2020   *)
(* ********************* *)
Require Import Coqlib Integers AST Maps.
Require Import Permutation.
Import ListNotations.


(** Properties about basic data structures *)

Lemma Z_max_0 : forall z, z >= 0 -> Z.max z 0 = z.
Proof.
  intros. apply Zmax_left. auto.
Qed.

Lemma not_in_app: forall {A} a (l1 l2: list A),
    ~In a (l1 ++ l2) <-> ~In a l1 /\ ~ In a l2.
Proof.
  intros. rewrite in_app_iff. split; tauto.
Qed.

Lemma in_map_filter: forall {A B} x (f: A -> B) g (l:list A),
    In x (map f (filter g l)) -> In x (map f l).
Proof.
  induction l as [|y l].
  - cbn. auto.
  - cbn. destr. cbn. tauto.
Qed.

Lemma length_S_inv : forall A n (l: list A),
    length l = S n ->
    exists l' a, l = l' ++ [a] /\ length l' = n.
Proof.
  induction n.
  - intros. destruct l. cbn in *.
    congruence.
    cbn in H. inv H.
    rewrite length_zero_iff_nil in H1.
    subst. exists nil. cbn. eauto.
  - intros. simpl in *. 
    destruct l. cbn in H. congruence.
    cbn in H. inv H.
    generalize (IHn _ H1).
    destruct 1 as (l' & a0 & eq & LEN). subst.
    exists (a :: l'). cbn. eexists; split; eauto.
Qed.

Lemma rev_nil_inv_len : forall A n (l:list A),
    length l = n -> rev l = [] -> l = nil.
Proof.
  induction n.
  - intros. 
    rewrite length_zero_iff_nil in H. subst. auto.
  - intros.
    generalize (length_S_inv _ _ _ H).
    destruct 1 as (l' & a & EQ & LEN).
    subst. rewrite rev_unit in H0.
    inv H0.
Qed.

Lemma rev_nil_inv : forall A (l:list A),
    rev l = [] -> l = nil.
Proof.
  intros. eapply rev_nil_inv_len; eauto.
Qed.

Lemma rev_single : forall A (l:list A) a,
    rev l = [a] -> l = [a].
Proof.
  induction l.
  - cbn in *. congruence.
  - intros. simpl in H.
    replace [a0] with (nil ++ [a0]) in H by auto.
    apply app_inj_tail in H.
    destruct H; subst. 
    generalize (rev_nil_inv _ _ H).
    intros. subst. auto.
Qed.

Lemma app_cons_comm : forall (A:Type) (l1 l2: list A) a,
    l1 ++ (a :: l2) = (l1 ++ [a]) ++ l2.
Proof.
  induction l1.
  - intros. auto.
  - simpl. intros. rewrite IHl1. auto.
Qed.

(* Lemma list_norepet_app: forall A (l1 l2: list A), *)
(*     list_norepet l1 -> list_norepet l2  *)
(*     -> (forall a, In a l1 -> ~ In a l2) *)
(*     -> list_norepet (l1 ++ l2). *)
(* Proof. *)
(*   induction l1; intros until l2; intros NORPT1 NORPT2 EXCL. *)
(*   - cbn. auto. *)
(*   - cbn in *. inv NORPT1. *)
(*     constructor.  *)
(*     + rewrite in_app. *)
(*       intro IN. destruct IN as [IN|IN]; auto. *)
(*       eapply EXCL; eauto. *)
(*     + eapply IHl1; eauto. *)
(* Qed. *)

Lemma partition_inv_nil1 : forall (A:Type) f (l1 l2:list A),
    partition f l1 = ([], l2) -> l1 = l2.
Proof.
  induction l1; intros; simpl in *.
  - inv H. auto.
  - destr_in H. destr_in H. inv H.
    f_equal. apply IHl1; auto.
Qed.


Lemma Forall2_in_map: 
  forall {A B} (l:list B) (a:B) (R: A -> B -> Prop) (f:B -> A),
    In a l -> Forall2 R (map f l) l -> R (f a) a.
Proof.
  induction l as [|e l].
  - intros a R f IN FA.
    inv IN.
  - intros a R f IN FA. cbn in *.
    inv IN. subst.
    + inv FA. auto.
    + inv FA. apply IHl; auto.
Qed.

Lemma Forall2_invl:
  forall {A B : Type} (R : A -> B -> Prop) a1 (l1: list A) (l2 : list B),
  In a1 l1 -> Forall2 R l1 l2 -> exists a2, In a2 l2 /\ R a1 a2.
Proof.
  induction l1 as [| e1 l1].
  - cbn. intros. contradiction.
  - cbn. intros l2 [EQ|IN] ALL.
    + subst. inv ALL. exists y. split. constructor; auto. auto.
    + inv ALL.
      eapply IHl1 in H3; eauto.
      destruct H3 as (a2 & IN' & R').
      exists a2. split. apply in_cons. auto. auto.
Qed.

Lemma in_map_incl: forall A B a (l l': list A) (f: A -> B),
    In a (map f l) -> incl l l' -> In a (map f l').
Proof.
  induction l as [|b l].
  - cbn. intros. contradiction.
  - cbn. intros l' f [EQ | IN] INCL.
    + subst. apply in_map. red in INCL. 
      apply INCL. apply in_eq.
    + apply IHl; auto.
      eapply incl_cons_inv; eauto.
Qed.

Lemma filter_incl: forall A f (l: list A), incl (filter f l) l.
Proof. 
  induction l as [|a l]; cbn; intros.
  - red. auto.
  - red. red in IHl.
    intros b H. destruct (f a).
    + inv H. apply in_eq.
      intuition.
    + intuition.
Qed.

Lemma list_norepet_filter_fst_pres: forall A B (l:list (A * B)) f,
    list_norepet (map fst l) -> list_norepet (map fst (filter f l)).
Proof.
  induction l as [|a l].
  - intros. cbn. constructor.
  - intros. cbn in *.
    destruct (f a).
    + cbn. inv H. constructor; auto.
      intros IN. apply H2.         
      eapply in_map_incl; eauto.
      eapply filter_incl; eauto.
    + apply IHl.
      inv H. auto.
Qed.

(** Bunch of properties about Permutation and PTree *)
Lemma NoDup_list_norepet_equiv : forall A (l: list A),
    NoDup l <-> list_norepet l.
Proof.
  induction l as [|a l].
  - split; intros. constructor. constructor.
  - split; intros. 
    + inv H. constructor; auto. rewrite <- IHl. auto.
    + inv H. constructor; auto. rewrite IHl. auto.
Qed.

Lemma Permutation_pres_list_norepet: forall A (l1 l2: list A),
  list_norepet l1 -> Permutation l1 l2 -> list_norepet l2.
Proof.
  intros. rewrite <- NoDup_list_norepet_equiv in *.
  eapply Permutation_NoDup; eauto.
Qed.

Lemma Permutation_NoDup_map: forall A B (f: A -> B) (l1 l2: list A),
    Permutation l1 l2 -> NoDup (map f l1) -> NoDup (map f l2).
Proof.
  intros A B f l1 l2 PERM NODUP.
  apply Permutation_NoDup with (l:= map f l1); eauto.
  apply Permutation_map; auto.
Qed.

Lemma Permutation_list_norepet_map: forall A B (f: A -> B) (l1 l2: list A),
    Permutation l1 l2 -> list_norepet (map f l1) -> list_norepet (map f l2).
Proof.
  intros A B f l1 l2 PERM NORPT.
  rewrite <- NoDup_list_norepet_equiv in *.
  eapply Permutation_NoDup_map; eauto.
Qed.


(** PTree Properties *)

Lemma PTree_Properties_of_list_iter_inv_some': forall {A} n defs (t:PTree.t A) id def f,
    length defs = n ->
    f = (fun (m : PTree.t A) (k_v : PTree.elt * A) => PTree.set (fst k_v) (snd k_v) m) ->
    (fold_left f defs t) ! id = Some def ->
    (fold_left f defs (PTree.empty A)) ! id = Some def \/
    t ! id = Some def.
Proof.
  induction n as [|n'].
  - intros defs t id def f LEN EQ FL.
    rewrite length_zero_iff_nil in LEN. subst.
    cbn in *. auto.
  - intros defs t id def f LEN EQ FL.
    apply length_S_inv in LEN.
    destruct LEN as (defs' & a & EQ' & LEN). 
    subst defs n'.
    destruct a as (id', def').
    rewrite fold_left_app in *.
    subst. cbn in *. 
    destruct (ident_eq id id').
    + subst. rewrite PTree.gss in *. auto.
    + rewrite PTree.gso in *; eauto.
Qed.


Lemma PTree_Properties_of_list_iter_inv_some: forall {A} defs (t:PTree.t A) id def f,
    f = (fun (m : PTree.t A) (k_v : PTree.elt * A) => PTree.set (fst k_v) (snd k_v) m) ->
    (fold_left f defs t) ! id = Some def ->
    (fold_left f defs (PTree.empty A)) ! id = Some def \/
    t ! id = Some def.
Proof.
  intros. eapply PTree_Properties_of_list_iter_inv_some'; eauto.
Qed.


Lemma PTree_Properties_of_list_tail_some: 
  forall {A} (defs: list (ident * A)) id id' def' def,
    id <> id' ->
    (PTree_Properties.of_list ((id', def') :: defs)) ! id = Some def ->
    (PTree_Properties.of_list defs) ! id = Some def.
Proof.
  unfold PTree_Properties.of_list. cbn.
  intros.
  generalize (PTree_Properties_of_list_iter_inv_some _ _ _ _ _ eq_refl H0).
  intros [FL | EQ]; auto.
  erewrite PTree.gso in EQ; eauto.
  rewrite PTree.gempty in EQ. congruence.
Qed.

Lemma PTree_Properties_of_list_iter_inv_none': forall {A} n defs (t:PTree.t A) id f,
    length defs = n ->
    f = (fun (m : PTree.t A) (k_v : PTree.elt * A) => PTree.set (fst k_v) (snd k_v) m) ->
    (fold_left f defs t) ! id = None ->
    (fold_left f defs (PTree.empty A)) ! id = None.
Proof.
  induction n as [|n'].
  - intros defs t id f LEN EQ FL.
    rewrite length_zero_iff_nil in LEN. subst.
    cbn in *. rewrite PTree.gempty. auto.
  - intros defs t id f LEN EQ FL.
    apply length_S_inv in LEN.
    destruct LEN as (defs' & a & EQ' & LEN).
    subst defs n'.
    destruct a as (id', def').
    rewrite fold_left_app in *.
    subst. cbn in *.
    destruct (ident_eq id id').
    + subst. rewrite PTree.gss in *. auto.
    + rewrite PTree.gso in *; eauto.
Qed.

Lemma PTree_Properties_of_list_iter_inv_none: forall {A} defs (t:PTree.t A) id f,
    f = (fun (m : PTree.t A) (k_v : PTree.elt * A) => PTree.set (fst k_v) (snd k_v) m) ->
    (fold_left f defs t) ! id = None ->
    (fold_left f defs (PTree.empty A)) ! id = None.
Proof.
  intros. eapply PTree_Properties_of_list_iter_inv_none'; eauto.
Qed.


Lemma PTree_Properties_of_list_tail_none: 
  forall {A} (defs: list (ident * A)) id id' def',
    (PTree_Properties.of_list ((id', def') :: defs)) ! id = None ->
    (PTree_Properties.of_list defs) ! id = None.
Proof.
  unfold PTree_Properties.of_list. cbn.
  intros.
  generalize (PTree_Properties_of_list_iter_inv_none _ _ _ _ eq_refl H).
  intros FL.
  congruence.
Qed.

Lemma PTree_Properties_of_list_tail: 
  forall {A} (defs: list (ident * A)) id id' def',
    id <> id' ->
    (PTree_Properties.of_list ((id', def') :: defs)) ! id = 
    (PTree_Properties.of_list defs) ! id.
Proof.
  intros A defs id id' def' NEQ.
  match goal with 
  | [ |- ?a = _ ] =>
    destruct a eqn:EQ
  end.
  - symmetry.
    erewrite PTree_Properties_of_list_tail_some; eauto.
  - symmetry.
    erewrite PTree_Properties_of_list_tail_none; eauto.
Qed.

Lemma PTree_elements_eq: forall {A B} (t1: PTree.t A) (t2: PTree.t B),
    (forall i x, t1!i = Some x -> exists y, t2!i = Some y) ->
    (forall i x, t2!i = Some x -> exists y, t1!i = Some y) ->
    map fst (PTree.elements t1) = map fst (PTree.elements t2).
Proof.
  intros A B t1 t2 GE1 GE2.
  assert (forall i x, t1 ! i = Some x -> exists y, t2 ! i = Some y /\ True) as GE1'.
  { intuition. apply GE1 in H. destruct H; eauto. }
  assert (forall i x, t2 ! i = Some x -> exists y, t1 ! i = Some y /\ True) as GE2'.
  { intuition. apply GE2 in H. destruct H; eauto. }
  generalize (PTree.elements_canonical_order _ _ _ GE1' GE2').
  intros ALL.
  apply list_forall2_ind with 
      (l:= PTree.elements t1) (l0:= PTree.elements t2)
      (P:=fun e1 e2 => fst e1 = fst e2 /\ True); auto.
  intros a1 al b1 bl (FL & T) ALL' EQ.
  cbn. rewrite FL. f_equal.
  eauto.
Qed.

Lemma Permutation_pres_ptree_get_some: forall A (l1 l2: list (ident * A)) a e,
    list_norepet (map fst l1) ->
    Permutation l1 l2 -> (PTree_Properties.of_list l1) ! a = Some e -> 
    (PTree_Properties.of_list l2) ! a = Some e.
Proof. 
  intros A l1 l2 a e NORPT PERM GET.
  apply PTree_Properties.of_list_norepet; auto.
  eapply Permutation_list_norepet_map; eauto.
  eapply Permutation_in; eauto.
  apply PTree_Properties.in_of_list; auto.
Qed.

Lemma Permutation_pres_ptree_get: forall A (l1 l2: list (ident * A)) a,
    list_norepet (map fst l1) -> 
    Permutation l1 l2 -> 
    (PTree_Properties.of_list l1) ! a = (PTree_Properties.of_list l2) ! a.
Proof. 
  intros A l1 l2 a NORPT1 PERM.
  destruct ((PTree_Properties.of_list l1) ! a) eqn:GET1.
  - symmetry. 
    eapply Permutation_pres_ptree_get_some; eauto.
  - destruct ((PTree_Properties.of_list l2) ! a) eqn:GET2; auto.
    assert (list_norepet (map fst l2)) as NORPT2.
    { eapply Permutation_list_norepet_map; eauto. }
    apply Permutation_sym in PERM.
    generalize (@Permutation_pres_ptree_get_some _ _ _ a a0 NORPT2 PERM GET2).    intros. congruence.
Qed.


Lemma PTree_combine_permutation: forall A B C (f: option A -> option B -> option C) l1 l1' l2 l2',
    f None None = None ->
    Permutation l1 l1' -> Permutation l2 l2' ->
    list_norepet (map fst l1) -> list_norepet (map fst l2) ->
    Permutation
      (PTree.elements
         (PTree.combine f (PTree_Properties.of_list l1) (PTree_Properties.of_list l2)))
      (PTree.elements
         (PTree.combine f (PTree_Properties.of_list l1') (PTree_Properties.of_list l2'))).
Proof.
  intros until l2'.
  intros F PERM1 PERM2 NORPT1 NORPT2.
  apply NoDup_Permutation.
  apply NoDup_map_inv with (f:=fst); auto.
  rewrite NoDup_list_norepet_equiv.
  apply PTree.elements_keys_norepet.
  apply NoDup_map_inv with (f:=fst); auto.
  rewrite NoDup_list_norepet_equiv.
  apply PTree.elements_keys_norepet.
  intros (id, a).
  split; intros IN.
  - apply PTree.elements_complete in IN.
    apply PTree.elements_correct.
    rewrite PTree.gcombine in *; auto.
    rewrite <- (Permutation_pres_ptree_get _ l1 l1'); auto.
    rewrite <- (Permutation_pres_ptree_get _ l2 l2'); auto.
  - apply PTree.elements_complete in IN.
    apply PTree.elements_correct.
    rewrite PTree.gcombine in *; auto.
    rewrite (Permutation_pres_ptree_get _ l1 l1'); auto.
    rewrite (Permutation_pres_ptree_get _ l2 l2'); auto.
Qed.

Lemma PTree_remove_pres_in:
  forall (A : Type) i j (t : PTree.t A) v,
    i <> j -> In (i, v) (PTree.elements t) ->
    In (i, v) (PTree.elements (PTree.remove j t)).
Proof.
  intros A i j t v NEQ IN.
  apply PTree.elements_correct.
  rewrite PTree.gro; eauto.
  apply PTree.elements_complete; auto.
Qed.

Lemma PTree_remove_pres_in':
  forall (A : Type) i j (t : PTree.t A) v,
    In (i, v) (PTree.elements (PTree.remove j t)) ->
    In (i, v) (PTree.elements t).
Proof.
  intros A i j t v IN.
  apply PTree.elements_correct.
  apply PTree.elements_complete in IN.
  destruct (ident_eq i j). subst.
  generalize (PTree.grs j t). intros. congruence.
  erewrite <- PTree.gro; eauto.
Qed.

Lemma PTree_remove_list_pres_incl: forall {A:Type} ids (t:PTree.t A),
    incl (PTree.elements (fold_right (@PTree.remove A) t ids)) (PTree.elements t).
Proof.
  induction ids as [|id ids].
  - cbn [fold_right]. intros. apply incl_refl.
  - cbn [fold_right]. intros.
    eapply incl_tran. 2: eauto.
    red. intros a IN.
    destruct a. apply PTree_remove_pres_in' with id; auto.
Qed.

Lemma PTree_remove_permutation: forall A id (t: PTree.t A) a l,
    list_norepet (map fst ((id, a) :: l)) ->
    t ! id = Some a ->
    Permutation (PTree.elements (PTree.remove id t)) l ->
    Permutation (PTree.elements t) ((id, a) :: l).
Proof.
  intros A id t a l NORPT GET PERM.
  apply NoDup_Permutation.
  apply NoDup_map_inv with (f:=fst).
  rewrite NoDup_list_norepet_equiv.
  apply PTree.elements_keys_norepet.
  apply NoDup_map_inv with (f:=fst).
  rewrite NoDup_list_norepet_equiv. auto.
  intros (id', a').
  split; intros IN.
  - destruct (ident_eq id id').
    + subst.
      apply PTree.elements_complete in IN.
      assert (a = a') by congruence. subst.
      apply in_eq.
    + apply in_cons.
      eapply Permutation_in; eauto.      
      apply PTree_remove_pres_in; auto.
  - destruct (ident_eq id id').
    + subst. inv IN. 
      * inv H. apply PTree.elements_correct; auto.
      * cbn in NORPT. inv NORPT.
        apply (in_map fst) in H. cbn in H.
        contradiction.
    + inv IN. inv H. congruence.
      apply PTree.elements_correct.
      rewrite <- PTree.gro with (j := id); auto.
      apply PTree.elements_complete.
      apply Permutation_sym in PERM.
      eapply Permutation_in; eauto.
Qed.      

Lemma NoDup_ptree_elements: forall A (t: PTree.t A), NoDup (PTree.elements t).
Proof.
  intros.
  apply NoDup_map_inv with (f:=fst).
  rewrite NoDup_list_norepet_equiv.
  apply PTree.elements_keys_norepet.
Qed.

Lemma PTree_remove_in_absurd: forall A id (a:A) (t:PTree.t A),
    ~ In (id, a) (PTree.elements (PTree.remove id t)).
Proof.
  intros.
  intro IN.
  apply PTree.elements_complete in IN.
  generalize (PTree.grs id t). intros. congruence.
Qed. 

Lemma PTree_remove_permutation': forall A id (t: PTree.t A) a,
    t ! id = Some a ->
    Permutation (PTree.elements t) ((id, a) :: (PTree.elements (PTree.remove id t))).
Proof.
  intros.
  apply NoDup_Permutation.
  - apply NoDup_ptree_elements.
  - constructor.
    apply PTree_remove_in_absurd.
    apply NoDup_ptree_elements.
  - intros (id', a').
    split; intros IN.
    + destruct (ident_eq id id').
      * subst.
        apply PTree.elements_complete in IN.
        assert (a = a') by congruence. subst.
        apply in_eq.
      * apply in_cons.
        eapply Permutation_in; eauto.      
        apply PTree_remove_pres_in; auto.
    + inv IN. inv H0. apply PTree.elements_correct; auto.
      eapply PTree_remove_pres_in'; eauto.
Qed.    

Lemma PTree_remove_ids_not_in : forall {A} ids t id a,
  (fold_right (@PTree.remove A) t ids) ! id = Some a -> ~In id ids.
Proof.
  induction ids as [| id' ids].
  - cbn. auto.
  - cbn. intros t id a RM.
    assert (id <> id') as NEQ.
    { intros EQ. subst. rewrite PTree.grs in RM. congruence. }
    intros H. destruct H; subst.
    congruence.
    erewrite PTree.gro in RM; eauto.
    eapply IHids; eauto.
Qed.

Lemma PTree_get_remove_not_in: forall {A:Type} ids id (t:PTree.t A) a,
    (fold_right (@PTree.remove A) t ids) ! id = Some a ->
    t ! id = Some a.
Proof.
  induction ids as [|id' ids].
  - intros id t a RM.
    cbn in RM. auto.
  - intros id t a RM.
    generalize (PTree_remove_ids_not_in _ _ _ _ RM); eauto.
    intros IN.
    cbn in RM.
    assert (id <> id').
    { intros EQ. subst. apply IN. apply in_eq. }
    erewrite PTree.gro in RM; auto.
Qed.

Lemma PTree_get_remove_not_in_eq: forall {A:Type} ids id (t:PTree.t A),
    ~In id ids ->
    (fold_right (@PTree.remove A) t ids) ! id = t !id.
Proof.
  induction ids as [|id' ids].
  - intros id t IN.
    cbn. auto.
  - intros id t IN.
    assert (id <> id').
    { intros EQ. subst. apply IN. apply in_eq. }
    cbn. erewrite PTree.gro; eauto.
    eapply IHids; eauto.
    intros IN'. apply IN. apply in_cons. auto.
Qed.
