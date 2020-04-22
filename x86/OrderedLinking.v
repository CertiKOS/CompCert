(* ********************* *)
(* Author: Yuting Wang   *)
(* Date:   Oct 2, 2019   *)
(* ********************* *)

Require Import Coqlib Integers Values Maps AST.
Require Import Linking Errors LinkingProp.
Require Import Permutation.
Require Import LocalLib.


(** * Linking of Asm program such that the order of internal definitions is preserved **)


(** Extract elements from PTrees in order *)
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
    

Lemma PTree_extract_elements_app : forall {A} (ids1 ids2: list ident) (t t': PTree.t A) defs,
    PTree_extract_elements (ids1 ++ ids2) t = Some (defs, t') ->
    exists t1 defs1 defs2, PTree_extract_elements ids2 t = Some (defs2, t1) /\
                      PTree_extract_elements ids1 t1 = Some (defs1, t') /\
                      defs = defs1 ++ defs2.
Proof.
  induction ids1 as [|id1 ids1]; cbn.
  - intros ids2 t t' defs EXT.
    do 3 eexists. split; eauto.
  - intros ids2 t t' defs EXT.
    destr_in EXT. destruct p. destr_in EXT. inv EXT.
    edestruct IHids1 as (t1' & defs1' & defs2' &  EXT1 & EXT2 & EQ); eauto. subst.
    do 3 eexists; split; eauto.
    rewrite EXT2. rewrite Heqo0. split; eauto.
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

Lemma PTree_extract_elements_permutation' : forall {A:Type} (ids: list ident) (t t':PTree.t A) vals,
  PTree_extract_elements ids t = Some (vals, t') ->
  Permutation (PTree.elements t) ((PTree.elements t') ++ vals).
Proof.
  intros A ids t t' vals H.
  eapply Permutation_trans.
  eapply PTree_extract_elements_permutation; eauto.
  apply Permutation_app_comm.
Qed.

Lemma PTree_extract_elements_remain: 
  forall {A:Type} ids defs (t t': PTree.t A),
    PTree_extract_elements ids t = Some (defs, t') ->
    t' = fold_right (@PTree.remove A) t ids.
Proof.
  induction ids as [|id ids].
  - cbn. inversion 1. subst. auto.
  - cbn. intros defs t t' EXTR.
    destr_in EXTR. destruct p.
    destr_in EXTR. inv EXTR.
    f_equal. 
    eapply IHids; eauto.
Qed.


Lemma PTree_extract_elements_domain_norepet: forall {A:Type} ids (t:PTree.t A) r,
  PTree_extract_elements ids t = Some r -> list_norepet ids.
Proof.
  induction ids as [|id ids].
  - cbn. intros. inv H. constructor.
  - cbn. intros t r EXT. destr_in EXT. destruct p.
    destr_in EXT. inv EXT. constructor.
    apply PTree_extract_elements_remain in Heqo. subst.
    eapply PTree_remove_ids_not_in; eauto.
    eauto.
Qed.


Definition PTree_combine_ids_defs_match {A B C} 
           (t1:PTree.t A) (t2: PTree.t B) 
           (f: option A -> option B -> option C)
           (ids: list ident) (defs: list (ident * C)) :=
  Forall2 (fun (id : positive) '(id', def) => id = id' /\ f t1 ! id t2 ! id = Some def)
    ids defs.
  
Lemma PTree_combine_ids_defs_match_inv1: 
  forall {A B C} t1 t2 (f:option A -> option B -> option C) id ids l,
      In id ids ->
      PTree_combine_ids_defs_match t1 t2 f ids l ->
      exists e, In e l /\ id = fst e /\ f t1!id t2!id = Some (snd e).
Proof.
  intros A B C t1 t2 f id ids l IN MATCH.
  red in MATCH.
  eapply Forall2_invl in MATCH; eauto.
  destruct MATCH as ((id', def) & IN' & EQ & MG).
  subst. rewrite MG. eauto.
Qed.

Lemma PTree_combine_ids_defs_match_det: 
  forall {A B C} (t1:PTree.t A) (t2:PTree.t B) 
    (f:option A -> option B -> option C) ids l1 l2,
    PTree_combine_ids_defs_match t1 t2 f ids l1 ->
    PTree_combine_ids_defs_match t1 t2 f ids l2 ->
    l1 = l2.
Proof.
  induction ids as [|id ids].
  - intros l1 l2 MATCH1 MATCH2.
    inv MATCH1. inv MATCH2. auto.
  - intros l1 l2 MATCH1 MATCH2.
    inv MATCH1. inv MATCH2.
    destruct y, y0. inv H1. inv H2.
    f_equal. congruence.
    eauto.
Qed.

Lemma PTree_elements_combine_incl:
  forall {A B C: Type} l
    (f : option A -> option B -> option C)
    (t1: PTree.t A)
    (t2: PTree.t B),
  f None None = None ->
  incl l (PTree.elements (PTree.combine f t1 t2)) ->
  PTree_combine_ids_defs_match t1 t2 f (map fst l) l.
Proof.
  induction l as [|d l].
  - cbn. intros. red. auto.
  - cbn. 
    intros f t1 t2 FN EQ.
    destruct d as [id def].
    red. cbn. constructor.
    + split; auto.
      erewrite <- PTree.gcombine; eauto.
      apply PTree.elements_complete. 
      red in EQ. apply EQ. apply in_eq.
    + apply IHl; auto.
      eapply incl_cons_inv; eauto.
Qed.

Lemma PTree_elements_combine:
  forall {A B C: Type} 
    (f : option A -> option B -> option C)
    (t1: PTree.t A)
    (t2: PTree.t B),
  f None None = None ->
  PTree_combine_ids_defs_match t1 t2 f 
     (map fst (PTree.elements (PTree.combine f t1 t2))) 
     (PTree.elements (PTree.combine f t1 t2)).
Proof.
  intros. eapply PTree_elements_combine_incl; eauto.
  apply incl_refl.
Qed.

Lemma PTree_combine_ids_defs_match_incl_ids: 
  forall {A B C} t1 t2 (f:option A -> option B -> option C) ids l,
    f None None = None ->
    PTree_combine_ids_defs_match t1 t2 f ids l ->
    incl ids (map fst (PTree.elements (PTree.combine f t1 t2))).
Proof.
  intros A B C t1 t2 f ids l FN MATCH.
  red. intros a IN.
  apply in_map_iff.
  assert (exists e, (PTree.combine f t1 t2)! a = Some e) as CE.
  { rewrite PTree.gcombine.
    eapply PTree_combine_ids_defs_match_inv1 in MATCH; eauto.
    destruct MATCH as (e & IN' & EQ & LINK). eauto. 
    auto. 
  }
  destruct CE as (e, CE).
  apply PTree.elements_correct in CE.
  exists (a,e). split; eauto.
Qed.


Lemma PTree_extract_elements_combine_match: 
  forall {A:Type} ids defs f (t1 t2 t': PTree.t A),
    f None None = None ->
    PTree_extract_elements ids (PTree.combine f t1 t2) = Some (defs, t') ->
    PTree_combine_ids_defs_match t1 t2 f ids defs.
Proof.
  induction ids as [|id ids].
  - inversion 2. subst.
    constructor.
  - intros defs f t1 t2 t' FN EXT.
    generalize (PTree_extract_elements_domain_norepet _ _ _ EXT).
    intros NORPT. cbn in *.
    destr_in EXT. destruct p as (vals & t'').
    destr_in EXT. inv EXT. constructor.
    + split; auto.
      inv NORPT.
      generalize (PTree_extract_elements_remain _ _ _ _ Heqo).
      intros. subst.
      assert ((PTree.combine f t1 t2)!id = Some a). 
      { eapply PTree_get_remove_not_in; eauto. }
      erewrite PTree.gcombine in H; eauto.
    + inv NORPT.
      eapply IHids; eauto.
Qed.

Lemma PTree_combine_ids_defs_match_ids_eq: 
  forall {A B C:Type} ids defs (f:option A -> option B -> option C) t1 t2,
    PTree_combine_ids_defs_match t1 t2 f ids defs ->
    ids = map fst defs.
Proof.
  induction ids as [|id ids].
  - intros. inv H. auto.
  - intros. inv H. destruct y. inv H2.
    cbn. f_equal. eauto.
Qed.

Lemma PTree_extract_elements_ids_eq: 
  forall {A:Type} ids defs (t1 t2: PTree.t A),
    PTree_extract_elements ids t1 = Some (defs, t2) ->
    ids = map fst defs.
Proof.
  induction ids as [|id ids].
  - inversion 1. subst.
    auto.
  - intros defs t1 t2 EXT.
    inv EXT. destr_in H0. destruct p. destr_in H0.
    inv H0. cbn. f_equal.
    eauto.
Qed.

Lemma PTree_extract_elements_range_norepet: 
  forall {A:Type} ids defs (t1 t2: PTree.t A),
    PTree_extract_elements ids t1 = Some (defs, t2) ->
    list_norepet (map fst defs).
Proof.
  intros.
  erewrite <- PTree_extract_elements_ids_eq; eauto.
  eapply PTree_extract_elements_domain_norepet; eauto.
Qed.


Lemma PTree_extract_elements_remove_not_in: forall {A} ids (t:PTree.t A) id r,
  PTree_extract_elements ids (PTree.remove id t) = Some r ->
  ~In id ids.
Proof.
  induction ids as [| id' ids].
  - cbn. auto.
  - cbn. intros t id r EXT.
    destr_in EXT. destruct p. destr_in EXT. inv EXT.
    generalize (IHids _ _ _ Heqo). intros NIN.
    intros H. destruct H; auto.
    subst.
    apply PTree_extract_elements_remain in Heqo. subst.
    erewrite PTree_get_remove_not_in_eq in Heqo0; eauto.
    rewrite PTree.grs in Heqo0. congruence.
Qed.
  

Lemma PTree_extract_elements_remove_pres: forall {A} id ids (t t':PTree.t A) defs,
  PTree_extract_elements ids (PTree.remove id t) = Some (defs, t') ->
  exists t'', PTree_extract_elements ids t = Some (defs, t'').
Proof.
  induction ids as [| id' ids].
  - intros t t' defs EXT.
    cbn in EXT. inv EXT. cbn. eauto.
  - intros t t' defs EXT.
    generalize (PTree_extract_elements_remove_not_in _ _ _ _ EXT).
    intros NIN.
    generalize (PTree_extract_elements_domain_norepet _ _ _ EXT).
    intros NORPT.
    assert (~In id ids) as NIN'.
    { intros IN. apply NIN. apply in_cons. auto. }
    cbn in EXT. destr_in EXT. destruct p.
    destr_in EXT. inv EXT. inv NORPT.
    generalize (IHids _ _ _  Heqo).
    intros (t'' & EXT').
    cbn. rewrite EXT'.
    apply PTree_extract_elements_remain in EXT'.
    subst.
    erewrite PTree_get_remove_not_in_eq; eauto.
    apply PTree_extract_elements_remain in Heqo.
    subst. 
    erewrite PTree_get_remove_not_in_eq in Heqo0; eauto.
    assert (id <> id').
    { intros EQ. subst. apply NIN. apply in_eq. }
    erewrite <- PTree.gro; eauto.
    rewrite Heqo0. eauto.
Qed.


Lemma PTree_extract_elements_remove_list_pres: forall {A} ids' ids (t t':PTree.t A) defs,
  PTree_extract_elements ids (fold_right (@PTree.remove A) t ids') = Some (defs, t') ->
  exists t'', PTree_extract_elements ids t = Some (defs, t'').
Proof.
  induction ids' as [|id' ids'].
  - cbn. intros ids t t' defs EXT. eauto.
  - cbn. intros ids t t' defs EXT.
    apply PTree_extract_elements_remove_pres in EXT.
    destruct EXT as (t'' & EXT).
    eauto.
Qed.


  
Lemma PTree_combine_ids_defs_match_incl : 
  forall {A B C} (t1:PTree.t A) (t2:PTree.t B) f (l1 l2: list (ident * C)),
    PTree_combine_ids_defs_match t1 t2 f (map fst l1) l1 ->
    incl l2 l1 ->
    PTree_combine_ids_defs_match t1 t2 f (map fst l2) l2.
Proof.
  induction l2 as [|e l2].
  - cbn. intros. red. auto.
  - cbn. intros MATCH INCL.
    generalize (incl_cons_inv INCL). intros INCL'.
    apply Forall2_cons.
    + destruct e. cbn. split; auto.
      red in MATCH. 
      red in INCL.
      assert (In (i,c) l1) as IN.
      { apply INCL. apply in_eq. }
      generalize (Forall2_in_map l1 (i,c) _ fst IN MATCH).
      cbn. intros (EQ & RS). auto.
    + apply IHl2; auto.
Qed.


Lemma PTree_extract_elements_combine_remain_match: 
  forall {A:Type} ids defs f (t1 t2 t': PTree.t A),
    f None None = None ->
    PTree_extract_elements ids (PTree.combine f t1 t2) = Some (defs, t') ->
    PTree_combine_ids_defs_match t1 t2 f 
                                 (map fst (PTree.elements t'))
                                 (PTree.elements t').
Proof.
  intros A ids defs f t1 t2 t' FN EXT.
  generalize (PTree_extract_elements_remain _ _ _ _ EXT); eauto.
  intros EQ. subst.
  generalize (PTree_elements_combine _ t1 t2 FN); eauto.
  intros MATCH.
  eapply PTree_combine_ids_defs_match_incl; eauto.
  apply PTree_remove_list_pres_incl.
Qed.

Lemma PTree_combine_ids_defs_match_app: 
  forall {A B C} (t1: PTree.t A) (t2: PTree.t B) 
    (f:option A -> option B -> option C) ids1 defs1 ids2 defs2,
    PTree_combine_ids_defs_match t1 t2 f ids1 defs1 ->
    PTree_combine_ids_defs_match t1 t2 f ids2 defs2 ->
    PTree_combine_ids_defs_match t1 t2 f (ids1 ++ ids2) (defs1 ++ defs2).
Proof.
  induction ids1 as [|id1 ids1].
  - cbn. inversion 1. subst. cbn. auto.
  - cbn. inversion 1. subst. destruct y. 
    inv H2. inv H. inv H5. 
    intros MATCH.
    cbn. red. constructor.
    split; auto.
    eapply IHids1; eauto.
Qed.

Lemma PTree_combine_ids_defs_match_app_inv: 
  forall {A B C} (t1: PTree.t A) (t2: PTree.t B) 
    (f:option A -> option B -> option C) ids1 ids2 defs,
    PTree_combine_ids_defs_match t1 t2 f (ids1 ++ ids2) defs ->
    exists defs1 defs2,
      defs = defs1 ++ defs2 /\ 
      PTree_combine_ids_defs_match t1 t2 f ids1 defs1 /\
      PTree_combine_ids_defs_match t1 t2 f ids2 defs2.
Proof.
  induction ids1 as [|id1 ids1].
  - cbn. intros ids2 defs MATCH.
    exists nil, defs. split; auto. split; auto.
    red. apply Forall2_nil.
  - cbn. intros ids2 defs MATCH.
    inv MATCH. destruct y. destruct H1; subst.
    apply IHids1 in H3. 
    destruct H3 as (defs1 & defs2 & EQ & MATCH1 & MATCH2). subst.
    eexists ((p, c) :: defs1), defs2.
    split; auto. split; auto.
    apply Forall2_cons; auto.
Qed.


Lemma PTree_combine_ids_defs_match_symm: 
  forall {A B} (t1 t2: PTree.t A) (f: option A -> option A -> option B) ids entries,
    (forall a b, f a b = f b a) ->
    PTree_combine_ids_defs_match t1 t2 f ids entries ->
    PTree_combine_ids_defs_match t2 t1 f ids entries.
Proof.
  induction ids as [|id ids].
  - intros. inv H0. red. auto.
  - intros. inv H0. destruct y. destruct H3; subst.
    red. constructor.
    split; auto. rewrite H. auto.
    eapply IHids; eauto.
Qed.

(** The main proof begins *)

Section WITHFV.

Context {F V: Type}.
Context {LF: Linker F}.
Context {LV: Linker V}.

Variable is_fun_internal: F -> bool.

Lemma list_norepet_internal_ids: forall (p: program F V) ,
    list_norepet (map fst (prog_defs p)) ->
    list_norepet (collect_internal_def_ids is_fun_internal p).
Proof.
  intros. 
  unfold collect_internal_def_ids.
  unfold filter_internal_defs.
  apply list_norepet_filter_fst_pres; auto.
Qed.


Definition link_prog_ordered p1 p2 :=
  let dm1 := prog_option_defmap p1 in
  let dm2 := prog_option_defmap p2 in
  if ident_eq p1.(prog_main) p2.(prog_main) 
     && list_norepet_dec ident_eq (map fst (prog_defs p1))
     && list_norepet_dec ident_eq (map fst (prog_defs p2)) 
     && PTree_Properties.for_all dm1 (link_prog_check p1 p2) then
    let t := PTree.combine link_prog_merge dm1 dm2 in
    let ids1 := collect_internal_def_ids is_fun_internal p1 in
    let ids2 := collect_internal_def_ids is_fun_internal p2 in
    match PTree_extract_elements (ids1 ++ ids2) t with
    | None => None
    | Some (defs, t') => 
      Some {| prog_main := p1.(prog_main);
              prog_public := p1.(prog_public) ++ p2.(prog_public);
              prog_defs := PTree.elements t' ++ defs |}
    end
  else
    None.

Lemma link_prog_ordered_inv: forall(p1 p2 p:program F V),
    link_prog_ordered p1 p2 = Some p ->
    list_norepet (map fst (AST.prog_defs p1)) /\
    list_norepet (map fst (AST.prog_defs p2)).
Proof.
  intros p1 p2 p LINK.
  unfold link_prog_ordered in LINK.
  destr_in LINK; try congruence.
  repeat rewrite andb_true_iff in Heqb.
  destruct Heqb as [[[IDEQ NRPT1] NRPT2] CHK].
  destruct list_norepet_dec; try discriminate.
  destruct list_norepet_dec; try discriminate.
  auto.
Qed.

End WITHFV.

Instance Linker_prog_ordered (F V: Type) {LV: Linker V} : Linker (program (fundef F) V) := {
  link a b := link_prog_ordered is_fundef_internal a b;
  linkorder a b := True;
}.
Proof.
  auto.
  auto.
  auto.
Defined.

Global Opaque Linker_prog_ordered.



Lemma PTree_extract_elements_pres_get : forall A id ids defs (t t':PTree.t A),
    ~In id ids ->
    PTree_extract_elements ids t = Some (defs, t') ->
    t ! id = t' ! id.
Proof.
  induction ids as [|id1 ids].
  - cbn. intros. inv H0. auto.
  - cbn. intros defs t t' NIN MATCH.
    apply Decidable.not_or in NIN. destruct NIN as [NEQ NIN].
    destr_in MATCH. destruct p. destr_in MATCH.
    inv MATCH.
    erewrite PTree.gro; eauto.
Qed.

Lemma PTree_extract_elements_exists: forall A ids (t: PTree.t A),
    list_norepet ids ->
    incl ids (map fst (PTree.elements t)) ->
    exists defs t', PTree_extract_elements ids t = Some (defs, t').
Proof.
  induction ids as [|id ids].
  - cbn. intros. eauto.
  - cbn. 
    intros t NORPT INCL. inv NORPT.
    red in INCL.
    edestruct IHids as (defs1 & t1' & EXT); eauto.
    red. intuition.
    rewrite EXT.
    assert (In id (map fst (PTree.elements t))) as IN by intuition.
    edestruct PTree_Properties.of_list_dom as (v & GET); eauto.
    rewrite PTree_Properties.of_list_elements in GET.
    erewrite <- PTree_extract_elements_pres_get; eauto.
    rewrite GET. eauto.
Qed.

Lemma collect_internal_def_ids_inv: forall {F V} (p: program (fundef F) V) id,
    list_norepet (map fst (prog_defs p)) ->
    In id (collect_internal_def_ids is_fundef_internal p) ->
    exists def, (prog_option_defmap p)!id = Some def /\ 
           is_def_internal is_fundef_internal def = true.
Proof.
  intros F V p id NORPT IN.
  unfold prog_option_defmap.
  unfold collect_internal_def_ids in IN.
  apply list_in_map_inv in IN.
  destruct IN as ((id', def) & EQ & IN). subst.
  unfold filter_internal_defs in IN.
  rewrite filter_In in IN.
  destruct IN as (IN & DEF).
  eexists; split; eauto.
  cbn.
  apply PTree_Properties.of_list_norepet; eauto.
Qed.

Existing Instance Linker_option.
Definition prog_linkable {F V} {LF: Linker F} {LV: Linker V} (p1 p2: program F V) :=
  forall (id : positive) (gd1 gd2 : option (globdef F V)),
    (prog_option_defmap p1) ! id = Some gd1 ->
    (prog_option_defmap p2) ! id = Some gd2 ->
    In id (prog_public p1) /\ In id (prog_public p2) /\ (exists gd, link gd1 gd2 = Some gd).


Lemma link_prog_linkable:
  forall {F V} {LF: Linker F} {LV: Linker V} (p1 p2 p:program F V),
    link_prog p1 p2 = Some p ->
    prog_linkable p1 p2.
Proof.
  intros.
  generalize (link_prog_inv _ _ _ H).
  intros (MAINEQ & NORPT1 & NORPT2 & PROP & P).
  red. auto.
Qed.


Lemma link_prog_merge_some1: 
  forall {F V} {LF: Linker F} {LV: Linker V} a (def: option (globdef F V)) (p1 p2: program F V),
    prog_linkable p1 p2 ->
    (prog_option_defmap p1)!a = Some def ->
    exists def', link_prog_merge (Some def) ((PTree_Properties.of_list (prog_defs p2)) ! a) = Some def'.
Proof.
  intros F V LF LV a def p1 p2 LINKABLE GET.
  cbn. unfold link_option.
  destr; eauto.
  red in LINKABLE.
  generalize (LINKABLE _ _ _ GET Heqo).
  intros (IN1 & IN2 & (gd & LINK)). 
  destr; eauto.
Qed.


Lemma link_prog_merge_pres_get1: forall {F V} {LF: Linker F} {LV: Linker V} a (def: option (globdef F V)) (p1 p2: program F V),
    prog_linkable p1 p2 ->
    (prog_option_defmap p1) ! a = Some def ->
    exists def', 
      (PTree.combine link_prog_merge (prog_option_defmap p1)
                     (prog_option_defmap p2)) ! a = Some def'.
Proof.
  intros F V LF LV a def p1 p2 CHECK GET.
  unfold prog_option_defmap in *.
  rewrite PTree.gcombine; auto.
  rewrite GET.
  eapply link_prog_merge_some1; eauto.
Qed.


Lemma link_prog_merge_some2: 
  forall {F V} {LF: Linker F} {LV: Linker V} a (def: option (globdef F V)) (p1 p2: program F V),
    prog_linkable p1 p2 ->
    (prog_option_defmap p2)!a = Some def ->
    exists def', link_prog_merge ((PTree_Properties.of_list (prog_defs p1)) ! a) (Some def) = Some def'.
Proof.
  intros F V LF LV a def p1 p2 LINKABLE GET.
  cbn. 
  red in LINKABLE.
  unfold link_prog_merge.
  destr; eauto.
  generalize (LINKABLE _ _ _ Heqo GET).
  intros (IN1 & IN2 & (gd & LINK)). 
  eauto.
Qed.

Lemma link_prog_merge_pres_get2: forall {F V} {LF: Linker F} {LV: Linker V} a (def: option (globdef F V)) (p1 p2: program F V),
    prog_linkable p1 p2 ->
    (prog_option_defmap p2) ! a = Some def ->
    exists def', 
      (PTree.combine link_prog_merge (prog_option_defmap p1)
                     (prog_option_defmap p2)) ! a = Some def'.
Proof.
  intros F V LF LV a def p1 p2 CHECK GET.
  unfold prog_option_defmap in *.
  rewrite PTree.gcombine; auto.
  rewrite GET.
  eapply link_prog_merge_some2; eauto.
Qed.  

Lemma extract_defs_exists: 
  forall {F V: Type} {LV:Linker V} 
    (p1 p2 p: program (fundef F) V) t ids1 ids2,
    prog_linkable p1 p2 ->
    list_norepet (map fst (prog_defs p1)) ->
    list_norepet (map fst (prog_defs p2)) ->
    ids1 = collect_internal_def_ids is_fundef_internal p1 ->
    ids2 = collect_internal_def_ids is_fundef_internal p2 ->
    t = PTree.combine link_prog_merge 
                      (prog_option_defmap p1) 
                      (prog_option_defmap p2) ->
    exists defs t',
      PTree_extract_elements (ids1 ++ ids2) t = Some (defs, t').
Proof.
  intros F V LV p1 p2 p t ids1 ids2 PROP NORPT1 NORPT2 IDS1 IDS2 T. subst.
  eapply PTree_extract_elements_exists; eauto.
  rewrite list_norepet_app.
  repeat split.
  eapply list_norepet_internal_ids; eauto.
  eapply list_norepet_internal_ids; eauto.
  - red.
    intros x y IN1 IN2 EQ. subst.
    generalize (collect_internal_def_ids_inv _ _ NORPT1 IN1).
    intros (def1 & GET1 & INT1).
    generalize (collect_internal_def_ids_inv _ _ NORPT2 IN2).
    intros (def2 & GET2 & INT2).
    edestruct PROP as (PUB1 & PUB2 & (gd & LINK')); eauto.        
    assert (link def1 def2 = None) by (apply link_int_defs_none; auto).
    congruence.
  - apply incl_app.
    + red. intros.
      generalize (collect_internal_def_ids_inv _ _ NORPT1 H).
      intros (def & GET & INT).
      rewrite in_map_iff.
      generalize (link_prog_merge_pres_get1 _ _ _ p2 PROP GET). 
      intros (def' & COMB).
      exists (a, def'). split; auto.
      apply PTree.elements_correct. auto. 
    + red. intros.
      generalize (collect_internal_def_ids_inv _ _ NORPT2 H).
      intros (def & GET & INT).
      rewrite in_map_iff.
      generalize (link_prog_merge_pres_get2 _ _ p1 p2 PROP GET). 
      intros (def' & COMB).
      exists (a, def'). split; auto.
      apply PTree.elements_correct. auto. 
Qed.    


Local Transparent Linker_prog_ordered.

Lemma prog_linkable_permutation: 
  forall {F V} {LF: Linker F} {LV: Linker V}
    (p1 p2 tp1 tp2 p: program F V),
    link p1 p2 = Some p ->
    prog_public p1 = prog_public tp1 ->
    prog_public p2 = prog_public tp2 ->
    Permutation (prog_defs p1) (prog_defs tp1) ->
    Permutation (prog_defs p2) (prog_defs tp2) ->
    prog_linkable tp1 tp2.
Proof.
  intros F V LF LV p1 p2 tp1 tp2 p LINK PUB1 PUB2 PERM1 PERM2.
  generalize (link_prog_inv _ _ _ LINK).
  intros (MAINEQ & NORPT1 & NORPT2 & LINKABLE & P). clear P.
  intros id gd1 gd2 GET1 GET2.
  unfold prog_option_defmap in *.
  rewrite <- (Permutation_pres_ptree_get _ _ _ _ NORPT1  PERM1) in GET1; eauto.
  rewrite <- (Permutation_pres_ptree_get _ _ _ _ NORPT2  PERM2) in GET2; eauto.
  edestruct LINKABLE as (IN1 & IN2 & (gd & LINK')); eauto.
  repeat (split; eauto).
  rewrite <- PUB1. auto.
  rewrite <- PUB2. auto.
Qed.

Lemma link_prog_ordered_inv': 
  forall {F V} {LV: Linker V} 
    (p1 p2 p: AST.program (AST.fundef F) V),
    link_prog_ordered is_fundef_internal p1 p2 = Some p ->
    exists p', 
      link_prog p1 p2 = Some p' /\
      Permutation (AST.prog_defs p) (AST.prog_defs p').
Proof.
  intros F V LV p1 p2 p LINK.
  unfold link_prog_ordered in LINK.
  destr_in LINK. 
  destr_in LINK.
  destruct p0 as (defs3 & t'). inv LINK. cbn.
  eexists. split.
  - unfold link_prog.
    rewrite Heqb. reflexivity.
  - cbn.
    apply Permutation_sym.
    eapply PTree_extract_elements_permutation'; eauto.
Qed.
