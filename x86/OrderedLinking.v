(* ********************* *)
(* Author: Yuting Wang   *)
(* Date:   Oct 2, 2019   *)
(* ********************* *)

Require Import Coqlib Integers Values Maps AST.
Require Import Linking Errors.
Require Import Permutation.


(** * Linking of Asm program such that the order of internal definitions is preserved **)


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

Lemma Permutation_pres_ptree_get_some: forall A (l1 l2: list (ident * A)) a e,
    list_norepet (map fst l2) ->
    Permutation l1 l2 -> (PTree_Properties.of_list l1) ! a = Some e -> 
    (PTree_Properties.of_list l2) ! a = Some e.
Proof. 
  intros A l1 l2 a e NORPT PERM GET.
  apply PTree_Properties.of_list_norepet; auto.
  eapply Permutation_in; eauto.
  apply PTree_Properties.in_of_list; auto.
Qed.

Lemma Permutation_pres_ptree_get: forall A (l1 l2: list (ident * A)) a,
    list_norepet (map fst l1) -> 
    list_norepet (map fst l2) -> 
    Permutation l1 l2 -> 
    (PTree_Properties.of_list l1) ! a = (PTree_Properties.of_list l2) ! a.
Proof. 
  intros A l1 l2 a NORPT1 NORPT2 PERM.
  destruct ((PTree_Properties.of_list l1) ! a) eqn:GET1.
  - symmetry. 
    eapply Permutation_pres_ptree_get_some; eauto.
  - destruct ((PTree_Properties.of_list l2) ! a) eqn:GET2; auto.
    apply Permutation_sym in PERM.
    generalize (@Permutation_pres_ptree_get_some _ _ _ a a0 NORPT1 PERM GET2).
    intros. congruence.
Qed.

Lemma Permutation_list_norepet_map: forall A B (f: A -> B) (l1 l2: list A),
    Permutation l1 l2 -> list_norepet (map f l1) -> list_norepet (map f l2).
Proof.
  intros A B f l1 l2 PERM NORPT.
  rewrite <- NoDup_list_norepet_equiv in *.
  eapply Permutation_NoDup_map; eauto.
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
    eapply Permutation_list_norepet_map; eauto.
    eapply Permutation_list_norepet_map; eauto.
  - apply PTree.elements_complete in IN.
    apply PTree.elements_correct.
    rewrite PTree.gcombine in *; auto.
    rewrite (Permutation_pres_ptree_get _ l1 l1'); auto.
    rewrite (Permutation_pres_ptree_get _ l2 l2'); auto.
    eapply Permutation_list_norepet_map; eauto.
    eapply Permutation_list_norepet_map; eauto.
Qed.

Fixpoint PTree_extract_elements {A:Type} (ids: list ident) (t: PTree.t A) :=
  match ids with 
  | nil => Some (nil, t)
  | id :: ids' =>
    match PTree_extract_elements ids' t with
    | None => None
    | Some (vals, t') => 
      match t'!id with
      | None => None
      | Some val => 
        Some ((id, val) :: vals, (PTree.remove id t'))
      end
    end
  end.

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


Lemma PTree_extract_elements_permutation : forall {A:Type} (ids: list ident) (t t':PTree.t A) vals,
  PTree_extract_elements ids t = Some (vals, t') ->
  Permutation (PTree.elements t) (vals ++ (PTree.elements t')).
Proof.
  induction ids as [|id ids].
  - cbn. inversion 1. subst. inv H. auto.
  - cbn. intros t t' vals H.
    destr_in H. destruct p. destr_in H. inv H. cbn.
    generalize (IHids _ _ _ Heqo). intros PERM.
    eapply Permutation_trans; eauto.
    assert (Permutation (PTree.elements t0) ((id, a) :: PTree.elements (PTree.remove id t0))).
    { apply PTree_remove_permutation'; auto. }
    eapply Permutation_trans.
    apply Permutation_app_head. exact H.
    apply Permutation_sym. 
    apply Permutation_middle.
Qed.



(** The main proof begins *)

Section WITHFV.

Context {F V: Type}.
Context {LF: Linker F}.
Context {LV: Linker V}.
Variable is_fun_internal: F -> bool.

Definition is_var_internal (v: globvar V) :=
  match classify_init (gvar_init v) with
  | Init_definitive _ => true
  | _ => false
  end.

Definition is_def_internal (def: option (globdef F V)) : bool :=
  match def with
  | None => false
  | Some g =>
    match g with
    | Gvar v => is_var_internal v
    | Gfun f => is_fun_internal f
    end
  end.

Definition filter_internal_defs (idgs: list (ident * option (globdef F V))) :=
  filter (fun '(id,def) => is_def_internal def) idgs.

Definition collect_internal_def_ids (p: program F V) :=
  let int_defs := filter_internal_defs (prog_defs p) in
  map fst int_defs.



Definition link_prog_ordered p1 p2 :=
  let dm1 := prog_option_defmap p1 in
  let dm2 := prog_option_defmap p2 in
  if ident_eq p1.(prog_main) p2.(prog_main) 
     && list_norepet_dec ident_eq (map fst (prog_defs p1))
     && list_norepet_dec ident_eq (map fst (prog_defs p2)) then
    let t := PTree.combine link_prog_merge dm1 dm2 in
    let ids1 := collect_internal_def_ids p1 in
    let ids2 := collect_internal_def_ids p2 in
    match PTree_extract_elements (ids1 ++ ids2) t with
    | None => None
    | Some (defs, t') => 
      Some {| prog_main := p1.(prog_main);
              prog_public := p1.(prog_public) ++ p2.(prog_public);
              prog_defs := PTree.elements t' ++ defs |}
    end
  else
    None.

End WITHFV.

Definition is_fundef_internal {A:Type} (fd: fundef A) : bool :=
  match fd with
  | Internal _ => true
  | External _ => false
  end.

Instance Linker_prog_ordered (F V: Type) {LV: Linker V} : Linker (program (fundef F) V) := {
  link a b := link_prog_ordered is_fundef_internal a b;
  linkorder a b := True;
}.
Proof.
  auto.
  auto.
  auto.
Defined.

(** matching modulo the permutation of definitions *)

Definition match_prog {F V} (p tp: program F V) :=
  Permutation (prog_defs p) (prog_defs tp) 
  /\ prog_main p = prog_main tp
  /\ prog_public p = prog_public tp.

Lemma transf_program_match:
  forall F V (p: program F V), match_prog p p.
Proof.
  intros. red. 
  repeat (split; auto).
Qed.


Lemma extract_defs_exists: 
  forall {F V: Type} {LV:Linker V} 
    (p1 p2: program (fundef F) V) t ids1 ids2,
    ids1 = collect_internal_def_ids is_fundef_internal p1 ->
    ids2 = collect_internal_def_ids is_fundef_internal p2 ->
    t = PTree.combine link_prog_merge 
                      (prog_option_defmap p1) 
                      (prog_option_defmap p2) ->
    exists defs t',
      PTree_extract_elements (ids1 ++ ids2) t = Some (defs, t').
Proof.
  intros F V LV p1 p2 t ids1 ids2 IDS1 IDS2 T. subst.
  

  Lemma link_prog_merge_internal_exists: 
    forall {F V} {LV: Linker V} 
      (defs1: list (ident * option (globdef (fundef F) V))) ids1 t t2 id,
      ids1 = map fst (filter_internal_defs is_fundef_internal defs1) ->
      t = PTree.combine link_prog_merge (PTree_Properties.of_list defs1) t2 ->
      In id ids1 -> 
      exists def, t!id = def.
  Admitted.
  
  unfold collect_internal_def_ids. 
  unfold prog_option_defmap.
  
Admitted.



(** Commutativity between permutation and linking *)
Instance TransfPermuteLink {F V} {LV: Linker V}
  : @TransfLink _ _ (Linker_prog (fundef F) V) (Linker_prog_ordered F V) match_prog.
Proof.
  Local Transparent Linker_prog.
  red. unfold match_prog. cbn. 
  intros until p.
  intros LINK (PERM1 & MAINEQ1 & PUBEQ1) (PERM2 & MAINEQ2 & PUBEQ2).
  unfold link_prog in LINK.
  destr_in LINK. inv LINK. cbn.
  repeat (rewrite andb_true_iff in Heqb). 
  destruct Heqb as (((MAINEQ & NORPT1) & NORPT2) & CHECK).
  destruct ident_eq; try discriminate.
  destruct list_norepet_dec; try discriminate.
  destruct list_norepet_dec; try discriminate.
  unfold link_prog_ordered.
  assert (prog_main tp1 = prog_main tp2) as MAINEQ3 by congruence.
  rewrite MAINEQ3.
  destruct ident_eq; try congruence. cbn.
  assert (list_norepet (map fst (prog_defs tp1))) as NORPT3.
  { eapply Permutation_list_norepet_map; eauto. }
  destruct list_norepet_dec; try contradiction. cbn.
  assert (list_norepet (map fst (prog_defs tp2))) as NORPT4.
  { eapply Permutation_list_norepet_map; eauto. }
  destruct list_norepet_dec; try contradiction. cbn.  
  edestruct (@extract_defs_exists F V _ tp1 tp2) as (defs1 & t1 & EXTR); eauto.
  rewrite EXTR. 
  eexists; split; eauto.
  cbn.
  repeat (split; auto).
  generalize (PTree_extract_elements_permutation _ _ _ _ EXTR).
  intros PERM3. 
  apply Permutation_trans with (defs1 ++ PTree.elements t1).
  eapply Permutation_trans; [| exact PERM3].
  unfold prog_option_defmap.
  eapply PTree_combine_permutation; eauto.
  apply Permutation_app_comm.
  congruence.
  congruence.
Qed.
