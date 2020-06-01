(* ********************* *)
(* Author: Yuting Wang   *)
(* Date:   Feb 31, 2020   *)
(* ********************* *)
Require Import Coqlib Integers AST Maps.
Require Import Permutation.
Require Import Values Events Memtype Memory.
Import ListNotations.

Ltac destr_if := 
  match goal with 
  | [ |- context [if ?b then _ else _] ] => 
    let eq := fresh "EQ" in
    (destruct b eqn:eq)
  end.

Ltac destr_match := 
  match goal with 
  | [ |- context [match ?b with _ => _ end] ] => 
    let eq := fresh "EQ" in
    (destruct b eqn:eq)
  end.

Ltac destr_match_in H := 
  match type of H with 
  | context [match ?b with _ => _ end] => 
    let eq := fresh "EQ" in
    (destruct b eqn:eq)
  end.

(** ** Properties about basic data structures *)

Lemma map_pres_subset_rel: forall A B (l1 l2:list A) (f: A -> B),
    (forall x, In x l1 -> In x l2)
    -> (forall y, In y (map f l1) -> In y (map f l2)).
Proof.
  intros A B l1 l2 f SUB y IN.
  rewrite in_map_iff in *.
  destruct IN as (x & EQ & IN). subst.
  eauto.
Qed.

Lemma Forall_app_distr: forall A f (l1 l2 : list A),
    Forall f (l1 ++ l2) 
    <-> Forall f l1 /\ Forall f l2.
Proof.
  induction l1 as [|e l1].
  - intros l2. cbn. split; auto.
    tauto.
  - cbn. intros. generalize (IHl1 l2).
    destruct 1 as [F1 F2].
    split.
    + intros F3. inv F3.
      generalize (F1 H2). 
      destruct 1. split; auto.
    + intros F3. destruct F3 as [F4 F5]. inv F4.
      auto.
Qed.


Fixpoint pos_advance_N (p:positive) (n:nat) : positive :=
  match n with
  | O => p
  | Datatypes.S n' => pos_advance_N (Psucc p) n'
  end.

Lemma psucc_advance_Nsucc_eq : forall n p,
  pos_advance_N (Pos.succ p) n = Pos.succ (pos_advance_N p n).
Proof.
  induction n; intros.
  - simpl. auto.
  - simpl. rewrite IHn. auto.
Qed.

Lemma pos_advance_N_ple : forall p n,
  Ple p (pos_advance_N p n).
Proof.
  induction n; intros.
  - simpl. apply Ple_refl.
  - simpl.
    rewrite psucc_advance_Nsucc_eq.
    apply Ple_trans with (pos_advance_N p n); auto. apply Ple_succ.
Qed.

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


(** ** Bunch of properties about Permutation and PTree *)
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


Lemma list_norepet_rev: forall A (l:list A),
    list_norepet l <->
    list_norepet (rev l).
Proof.
  intros. split.
  - intros H. apply Permutation_pres_list_norepet with l; auto.
    apply Permutation_rev.
  - intros H. apply Permutation_pres_list_norepet with (rev l); auto.
    apply Permutation_sym. apply Permutation_rev.
Qed.

(** PTree Properties *)

Lemma PTree_Properties_of_list_cons:
  forall {A : Type} (k : PTree.elt) (v : A) (l : list (PTree.elt * A)),
  ~ In k (map fst l) -> (PTree_Properties.of_list ((k, v) :: l)) ! k = Some v.
Proof.
  intros.
  replace ((k, v) :: l) with ([] ++ (k, v) :: l) by auto.
  apply PTree_Properties.of_list_unique; auto.
Qed.

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

Lemma Permutation_pres_ptree_get_none: forall A (l1 l2: list (ident * A)) a,
    Permutation l1 l2 -> (PTree_Properties.of_list l1) ! a = None -> 
    (PTree_Properties.of_list l2) ! a = None.
Proof. 
  intros A l1 l2 a PERM GET1.
  destruct ((PTree_Properties.of_list l2) ! a) eqn:GET2; auto.
  apply PTree_Properties.in_of_list in GET2.
  apply Permutation_sym in PERM.
  generalize (Permutation_in _ PERM GET2). intros IN.
  generalize (in_map fst _ _ IN).
  intros IN'. cbn in IN'.
  apply PTree_Properties.of_list_dom in IN'.
  destruct IN' as (v & GET'). congruence.
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
  - symmetry.
    eapply Permutation_pres_ptree_get_none; eauto.
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


(** ** Properties about injections of values *)

Lemma vinject_pres_not_vundef : forall j v1 v2,
  Val.inject j v1 v2 -> v1 <> Vundef -> v2 <> Vundef.
Proof.
  intros. destruct v1; inversion H; subst; auto.
  congruence.
Qed.

Lemma vinject_pres_has_type : forall j v1 v2 t,
    Val.inject j v1 v2 -> v1 <> Vundef ->
    Val.has_type v1 t -> Val.has_type v2 t.
Proof.
  intros. destruct v1; inversion H; subst; simpl in H; auto. 
  congruence.
Qed.

Lemma val_of_optbool_lessdef : forall j v1 v2,
    Val.opt_lessdef v1 v2 -> Val.inject j (Val.of_optbool v1) (Val.of_optbool v2).
Proof.
  intros. destruct v1; auto.
  simpl. inv H. destruct b; constructor.
Qed.

Lemma val_negative_inject: forall j v1 v2,
  Val.inject j v1 v2 -> Val.inject j (Val.negative v1) (Val.negative v2).
Proof.
  intros. unfold Val.negative. destruct v1; auto.
  inv H. auto.
Qed.

Lemma val_negativel_inject: forall j v1 v2,
  Val.inject j v1 v2 -> Val.inject j (Val.negativel v1) (Val.negativel v2).
Proof.
  intros. unfold Val.negativel. destruct v1; auto.
  inv H. auto.
Qed.

Lemma sub_overflow_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> 
    Val.inject j (Val.sub_overflow v1 v1') (Val.sub_overflow v2 v2').
Proof.
  intros. unfold Val.sub_overflow. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma subl_overflow_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> 
    Val.inject j (Val.subl_overflow v1 v1') (Val.subl_overflow v2 v2').
Proof.
  intros. unfold Val.subl_overflow. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

(** ** Properties about Programs *)
Lemma init_data_eq_dec: forall (i1 i2: init_data),
    {i1 = i2} + {i1 <> i2}.
Proof.
  decide equality; try apply Int.eq_dec.
  apply Int64.eq_dec.
  apply Floats.Float32.eq_dec.
  apply Floats.Float.eq_dec.
  apply Z.eq_dec.
  apply Ptrofs.eq_dec.
  apply ident_eq.
Qed.

(* Definition list_init_data_external (il: list init_data) := *)
(*   il = nil. *)

(* Definition list_init_data_common (il: list init_data) := *)
(*   exists sz, il = [Init_space sz]. *)

(* Definition list_init_data_internal (il: list init_data) := *)
(*   il <> nil /\ (forall sz, il <> [Init_space sz]). *)

(* Lemma init_data_list_cases: forall (il:list init_data), *)
(*     list_init_data_external il \/ *)
(*     list_init_data_common il \/ *)
(*     list_init_data_internal il. *)
(* Proof. *)
(*   intros. *)
(*   edestruct (list_eq_dec init_data_eq_dec il nil); auto. *)
(*   destruct il; try congruence. *)
(*   destruct i; cbn; auto. *)
(*   right. right. red. split; auto. intros. congruence. *)
(*   right. right. red. split; auto. intros. congruence. *)
(*   right. right. red. split; auto. intros. congruence. *)
(*   right. right. red. split; auto. intros. congruence. *)
(*   right. right. red. split; auto. intros. congruence. *)
(*   right. right. red. split; auto. intros. congruence. *)
(*   destruct il. *)
(*     right. left. red. eauto. *)
(*     right. right. red. split; auto. intros. congruence. *)
(*   right. right. red. split; auto. intros. congruence. *)
(* Qed.   *)

Lemma init_data_list_size_app : forall l1 l2,
    init_data_list_size (l1 ++ l2) = (init_data_list_size l1) + (init_data_list_size l2).
Proof.
  induction l1 as [| e l2'].
  - intros l2. simpl. auto.
  - intros l2. simpl in *.
    rewrite IHl2'; omega.
Qed.

(** ** Propreties about injection of memories *)

Section WITHMEMORYMODEL.
  
Context `{memory_model: Mem.MemoryModel }.
Existing Instance inject_perm_all.

(** Default frame injection *)
Definition def_frame_inj m := (flat_frameinj (length (Mem.stack m))).

Lemma store_pres_def_frame_inj : forall chunk m1 b ofs v m1',
    Mem.store chunk m1 b ofs v = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  repeat erewrite Mem.push_new_stage_stack. simpl.
  exploit Mem.store_stack_blocks; eauto. intros. rewrite H0.
  auto.
Qed.

Lemma storev_pres_def_frame_inj : forall chunk m1 v1 v2 m1',
    Mem.storev chunk m1 v1 v2 = Some m1' ->
    def_frame_inj m1= def_frame_inj m1'.
Proof.
  intros until m1'. unfold Mem.storev.
  destruct v1; try congruence.
  intros STORE.
  eapply store_pres_def_frame_inj; eauto.
Qed.

Lemma push_new_stage_def_frame_inj : forall m,
    def_frame_inj (Mem.push_new_stage m) = (1%nat :: def_frame_inj m).
Proof.
  unfold def_frame_inj. intros.
  erewrite Mem.push_new_stage_stack. simpl. auto.
Qed.

Lemma alloc_pres_def_frame_inj : forall m1 lo hi m1' b,
    Mem.alloc m1 lo hi = (m1', b) ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  apply Mem.alloc_stack_blocks in H. rewrite H. auto.
Qed.


Lemma store_mapped_inject' : 
  forall (f : meminj) (chunk : memory_chunk) 
    (m1 : mem) (b1 : block) (ofs : Z) (v1 : val) 
    (n1 m2 : mem) (b2 : block) (delta : Z) (v2 : val),
    Mem.inject f (def_frame_inj m1) m1 m2 ->
    Mem.store chunk m1 b1 ofs v1 = Some n1 ->
    f b1 = Some (b2, delta) ->
    Val.inject f v1 v2 ->
    exists n2 : mem,
      Mem.store chunk m2 b2 (ofs + delta) v2 = Some n2 /\
      Mem.inject f (def_frame_inj n1) n1 n2.
Proof.
  intros. exploit Mem.store_mapped_inject; eauto. 
  intros (n2 & STORE & MINJ).
  eexists. split. eauto.
  erewrite <- store_pres_def_frame_inj; eauto.
Qed.

Lemma drop_perm_pres_def_frame_inj : forall m1 lo hi m1' b p,
    Mem.drop_perm m1 b lo hi p = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  apply Mem.drop_perm_stack in H. rewrite H. auto.
Qed.

Theorem storev_mapped_inject':
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  Mem.inject f (def_frame_inj m1) m1 m2 ->
  Mem.storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    Mem.storev chunk m2 a2 v2 = Some n2 /\ Mem.inject f (def_frame_inj n1) n1 n2.
Proof.
  intros. exploit Mem.storev_mapped_inject; eauto. 
  intros (n2 & STORE & MINJ).
  eexists. split. eauto.
  erewrite <- storev_pres_def_frame_inj; eauto.
Qed.

Lemma inject_decr : forall b j j' m1 m2 b' ofs,
  Mem.valid_block m1 b -> inject_incr j j' -> inject_separated j j' m1 m2 ->
  j' b = Some (b', ofs) -> j b = Some (b', ofs).
Proof.
  intros. destruct (j b) eqn:JB.
  - unfold inject_incr in *. destruct p. exploit H0; eauto.
    intros. congruence.
  - unfold inject_separated in *. exploit H1; eauto.
    intros (NVALID1 & NVALID2). congruence.
Qed.


(** Injection for cmpu_bool and cmplu_bool *)
Lemma valid_ptr_inj : forall j m m',
    Mem.inject j (def_frame_inj m) m m' ->
    forall b i b' delta,                                  
      j b = Some (b', delta) ->
      Mem.valid_pointer m b (Ptrofs.unsigned i) = true ->
      Mem.valid_pointer m' b' (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply Mem.valid_pointer_inject'; eauto.
Qed.


Lemma weak_valid_ptr_inj: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject'; eauto.
Qed.

Lemma weak_valid_ptr_no_overflow: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
Qed.

Lemma valid_different_ptrs_inj: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  j b1 = Some (b1', delta1) ->
  j b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros. eapply Mem.different_pointers_inject; eauto.
Qed.

Definition cmpu_bool_inject := fun j m m' (MINJ: Mem.inject j (def_frame_inj m) m m') =>
                     Val.cmpu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                          (valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_no_overflow j m m' MINJ)
                                          (valid_different_ptrs_inj j m m' MINJ).

Lemma cmpu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.opt_lessdef (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmpu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmpu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Definition cmplu_bool_inject := fun j m m' (MINJ: Mem.inject j (def_frame_inj m) m m') =>
                     Val.cmplu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                           (valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_no_overflow j m m' MINJ)
                                           (valid_different_ptrs_inj j m m' MINJ).


Lemma cmplu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.opt_lessdef (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmplu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmplu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Lemma cmpu_inject : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.inject j (Val.cmpu (Mem.valid_pointer m) c v1 v2)
               (Val.cmpu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmpu.
  exploit (cmpu_bool_lessdef j v1 v2); eauto. intros. 
  exploit val_of_optbool_lessdef; eauto.
Qed.

Lemma cmplu_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.opt_val_inject j (Val.cmplu (Mem.valid_pointer m) c v1 v2)
                     (Val.cmplu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmplu.
  exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' c); eauto. intros.
  inversion H2; subst; simpl; constructor.
  apply Val.vofbool_inject.
Qed.


End WITHMEMORYMODEL.
