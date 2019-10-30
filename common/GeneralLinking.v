(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Oct 28, 2019 *)
(* *******************  *)

Require Import Coqlib Maps Errors AST Linking.
Require Import ListInOrder.
Require Import Sorting.
Require Import Permutation.
Require Import RelationClasses.
Import ListNotations.

Set Implicit Arguments.

(** * A generalized framework for syntatic linking *)

(** The type class for syntactic equality *)
Class SynEq (A: Type) := 
{
  syneq : A -> A -> Prop;
  syneq_refl: forall a, syneq a a;
  syneq_symm: forall a b, syneq a b -> syneq b a;
  syneq_trans: forall a b c, syneq a b -> syneq b c -> syneq a c;
}.

(** The type class for the relation between two modules that holds
    when their internal definitions matches and are in the same order *)
Class DefsMatch (A:Type) :=
{
  defs_match: nlist A -> nlist A -> Prop;
  defs_match_symm: forall a b, defs_match a b -> defs_match b a;
  defs_match_trans: forall a b c, defs_match a b -> defs_match b c -> defs_match a c;
  defs_match_cong: forall a1 a2 a3 b,
      defs_match (ncons a1 a2) b -> defs_match a2 a3 -> defs_match (ncons a1 a3) b;
}.

(** We define some type classes that capture the properties about linking,
    syntactic equality and the matching-order relation *)

Class LinkingSynEq {A: Type} {LA: Linker A} {SEQ: SynEq A} :=
  linking_syneq_comm: forall m1 m2 m1' m2' m, 
    link m1 m2 = Some m -> syneq m1 m1' -> syneq m2 m2' ->
    exists m', link m1' m2' = Some m' /\ syneq m m'.

Class TransfSynEq {A B: Type} {SEQA: SynEq A} {SEQB: SynEq B} (transf: A -> B -> Prop) :=
  transf_syneq_comm: forall m1 m2 m1', 
    transf m1 m1' -> syneq m1 m2 ->
    exists m2', transf m2 m2' /\ syneq m1' m2'.

Class TransfDefsMatch {A B: Type} {MDA: DefsMatch A} {MDB: DefsMatch B}
      (transf: A -> B -> Prop) :=
  transf_defs_match_comm: forall ms ms' tms tms',
    defs_match ms tms -> 
    nlist_forall2 transf ms ms' ->
    nlist_forall2 transf tms tms' ->
    defs_match ms' tms'.
    
Class DefsMatchExists {A:Type} {LA: Linker A} {MD: DefsMatch A} {EQ: SynEq A} :=
  defs_match_exists: forall ms m, 
    link_list ms = Some m -> exists m', syneq m m' /\ defs_match ms (nbase m').

(** Commutative property between linking and transformations *)

Class TransfLink {A B:Type} 
      {LA: Linker A} {LB: Linker B} 
      {SEQA: SynEq A} {SEQB: SynEq B}
      {MA: DefsMatch A} {MB: DefsMatch B}
      (transf: A -> B -> Prop) :=
  transf_link:
    forall m1 m2 m1' m2' m m',
      link m1 m2 = Some m -> transf m1 m1' -> transf m2 m2' ->
      syneq m m' -> defs_match (ncons m1 (nbase m2)) (nbase m') ->
      exists n n', transf m' n /\ link m1' m2' = Some n' /\ 
              syneq n' n /\ defs_match (ncons m1' (nbase m2')) (nbase n).


(** A generic language is a type of programs and a linker. *)

Structure Language := mklang
{ 
  lang_prog :> Type; 
  lang_link: Linker lang_prog;
  lang_syneq: SynEq lang_prog;
  lang_defs_match: DefsMatch lang_prog;
  lang_linking_syneq: LinkingSynEq;
}.

Canonical Structure Language_gen (A: Type) (L: Linker A) 
          (SEQ: SynEq A) (DM: DefsMatch A)
          (LSEQ: @LinkingSynEq _ L SEQ) : Language 
  := @mklang A L SEQ DM LSEQ.

Record Pass (S T: Language) := mkpass {
  pass_match :> lang_prog S -> lang_prog T -> Prop;
  pass_syneq : @TransfSynEq (lang_prog S) (lang_prog T) 
                            (lang_syneq S) (lang_syneq T)
                            pass_match;
  pass_defs_match: @TransfDefsMatch (lang_prog S) (lang_prog T) 
                                    (lang_defs_match S) (lang_defs_match T)
                                    pass_match;
  pass_match_link: @TransfLink (lang_prog S) (lang_prog T) 
                               (lang_link S) (lang_link T) 
                               (lang_syneq S) (lang_syneq T)
                               (lang_defs_match S) (lang_defs_match T)
                               pass_match
}.

Arguments mkpass {S} {T} (pass_match) {pass_syneq} {pass_defs_match} {pass_match_link}.

(* Lemma list_forall2_eq : forall A (l l': list A), *)
(*     list_forall2 (fun a b => a = b) l l' -> l = l'. *)
(* Proof. *)
(*   induction l as [|h l]. *)
(*   - intros. inv H. auto. *)
(*   - intros. inv H. f_equal. auto. *)
(* Qed. *)

Program Definition pass_identity (l: Language): Pass l l :=
  {| pass_match := fun p1 p2 => p1 = p2;
     pass_match_link := _ |}.
Next Obligation.
  red; intros. subst. 
  exists m2. auto.
Defined.
Next Obligation.
  red; intros. 
  apply nlist_forall2_identity in H0.
  apply nlist_forall2_identity in H1.
  subst. auto.
Defined.
Next Obligation.
  red; intros. subst.
  exists m', m. auto.
Defined.

(* Lemma list_forall2_trans_rel_inv:  *)
(*   forall A B C (l1: list A) (l2: list C) *)
(*     (R1: A -> B -> Prop) (R2: B -> C -> Prop), *)
(*     list_forall2 (fun a b => exists c, R1 a c /\ R2 c b) l1 l2 -> *)
(*     exists l3, list_forall2 R1 l1 l3 /\ list_forall2 R2 l3 l2. *)
(* Proof. *)
(*   induction l1 as [| h1 l1]. *)
(*   - intros l2 R1 R2 REL. *)
(*     inv REL. exists nil. split; apply list_forall2_nil. *)
(*   - intros l2 R1 R2 REL. *)
(*     inv REL. destruct H1 as (c & REL1 & REL2). *)
(*     generalize (IHl1 _ _ _ H3). *)
(*     intros (l3' & REL3 & REL4). *)
(*     exists (c :: l3'). split; apply list_forall2_cons; auto. *)
(* Qed. *)

Program Definition pass_compose {l1 l2 l3: Language} (pass: Pass l1 l2) (pass': Pass l2 l3) : Pass l1 l3 :=
  {| pass_match := fun p1 p3 => exists p2, pass_match pass p1 p2 /\ pass_match pass' p2 p3;
     pass_match_link := _ |}.
Next Obligation.
  red. intros m1 m2 m1' (m1'' & TR1 & TR2) SEQ.
  generalize (pass_syneq pass). intro TSEQ1.
  generalize (pass_syneq pass'). intro TSEQ2.
  red in TSEQ1, TSEQ2.
  generalize (TSEQ1 _ _ _ TR1 SEQ).
  intros (m2'' & TR3 & SEQ1).
  generalize (TSEQ2 _ _ _ TR2 SEQ1).
  intros (m2''' & TR4 & SEQ2).
  exists m2'''; split; eauto.
Defined.  
Next Obligation.
  red. intros ms ms' tms tms' DM TR1 TR2.
  generalize (pass_defs_match pass). intros DMC1.
  generalize (pass_defs_match pass'). intros DMC2.
  red in DMC1, DMC2.  
  apply nlist_forall2_compose_inv in TR1.
  apply nlist_forall2_compose_inv in TR2.
  destruct TR1 as (ms'' & TR3 & TR4).
  destruct TR2 as (tms'' & TR5 & TR6).
  generalize (DMC1 _ _ _ _ DM TR3 TR5).
  intros DM1.
  eapply DMC2; eauto.
Defined.    
Next Obligation.
  red. intros until m'. 
  intros LINK (m1'' & TR1 & TR2) (m2'' & TR3 & TR4) SEQ DM.
  generalize (pass_match_link pass). intros TL1.
  generalize (pass_match_link pass'). intros TL2.
  red in TL1, TL2.
  generalize (TL1 _ _ _ _ _ _ LINK TR1 TR3 SEQ DM).
  destruct 1 as (n1 & n1' & TR5 & LINK1 & SEQ1 & DM1).
  generalize (TL2 _ _ _ _ _ _ LINK1 TR2 TR4 SEQ1 DM1).
  destruct 1 as (n2 & n2' & TR6 & LINK2 & SEQ2 & DM2).
  exists n2,n2'. split; eauto.
Defined.

(** A list of compilation passes that can be composed. *)

Inductive Passes: Language -> Language -> Type :=
  | pass_nil: forall l, Passes l l
  | pass_cons: forall l1 l2 l3, Pass l1 l2 -> Passes l2 l3 -> Passes l1 l3.

Infix ":::" := pass_cons (at level 60, right associativity) : linking_scope.

(** The pass corresponding to the composition of a list of passes. *)

Fixpoint compose_passes (l l': Language) (passes: Passes l l') : Pass l l' :=
  match passes in Passes l l' return Pass l l' with
  | pass_nil l => pass_identity l
  | pass_cons l1 l2 l3 pass1 passes => pass_compose pass1 (compose_passes passes)
  end.


(** List linking commutes with program transformations *)

Fixpoint nlist_to_list A (l: nlist A) : list A :=
  match l with
  | nbase a => [a]
  | ncons a l' => a :: (nlist_to_list l')
  end.

Lemma nlist_forall2_Forall : forall A B R (l1: nlist A) (l2: nlist B),
    nlist_forall2 R l1 l2 -> Forall2 R (nlist_to_list l1) (nlist_to_list l2).
Proof.
  induction l1 as [|a l1]; intros; inv H; cbn in *.
  - constructor; auto.
  - constructor; auto.
Qed.

Section LINK_LIST_MATCH.

Context (S T: Language).
Context (pass: Pass S T).
(* Context {A B: Type} {LA: Linker A} {LB: Linker B}  *)
(*         {SEQA: SynEq A} {SEQB: SynEq B} *)
(*         {DMA: DefsMatch A} {DMB: DefsMatch B} *)
(*         (prog_match: A -> B -> Prop)  *)
(*         {TL: TransfLink prog_match}. *)
Context (defs_match_exists: @DefsMatchExists _ (lang_link S) (lang_defs_match S) (lang_syneq S)).

Definition LS := lang_link S.
Definition LT := lang_link T.
Definition SEQS := lang_syneq S.
Definition SEQT := lang_syneq T.
Definition MATCHS := lang_defs_match S.
Definition MATCHT := lang_defs_match T.
Definition LINKSEQS := lang_linking_syneq S.
Definition LINKSEQT := lang_linking_syneq T.

Existing Instance LS.
Existing Instance LT.
Existing Instance SEQS.
Existing Instance SEQT.
Existing Instance MATCHS.
Existing Instance MATCHT.
Existing Instance LINKSEQS.
Existing Instance LINKSEQT.

Definition PASS_SYNEQ := pass_syneq pass.
Definition PASS_DEFS_MATCH := pass_defs_match pass.
Definition PASS_MATCH_LINK := pass_match_link pass.

Existing Instance PASS_SYNEQ.
Existing Instance PASS_DEFS_MATCH.
Existing Instance PASS_MATCH_LINK.


Theorem link_list_match: forall (ms: nlist (lang_prog S)) (tms: nlist (lang_prog T)), 
    nlist_forall2 (pass_match pass) ms tms ->
    forall m m', link_list ms = Some m ->
            syneq m m' ->
            defs_match ms (nbase m') ->
            exists n n', pass_match pass m' n /\
                    link_list tms = Some n' /\ 
                    syneq n' n /\ 
                    defs_match tms (nbase n).
Proof.
  induction 1; simpl.
  - intros m m' LINK SEQ DEFMATCH. inv LINK.
    generalize (transf_syneq_comm _ _ _ H SEQ).
    intros (m2' & PASS & SEQ1).
    assert (nlist_forall2 (pass_match pass) (nbase m) (nbase b)) as TR1.
    { constructor; auto. }
    assert (nlist_forall2 (pass_match pass) (nbase m') (nbase m2')) as TR2.
    { constructor; auto. }
    generalize (transf_defs_match_comm DEFMATCH TR1 TR2). intros DM1.
    exists m2', b. repeat split; eauto.
  - intros ms m' LINK SEQ DM. destr_in LINK.
    generalize (defs_match_exists _ Heqo).
    intros (m1 & SEQ1 & DM1).
    generalize (IHnlist_forall2 _ _ eq_refl SEQ1 DM1).
    intros (n & n' & TR & LINK1 & SEQ2 & DM2).
    generalize (linking_syneq_comm _ _ _ _ LINK (syneq_refl a) SEQ1).
    intros (m2 & LINK2 & SEQ3).
    assert (syneq m2 m').
    { apply syneq_trans with ms; auto. apply syneq_symm. auto. }
    generalize (defs_match_cong _ _ _ _ DM DM1).
    intros DM3.
    generalize (transf_link _ _ _ _ _ LINK2 H TR H1 DM3).
    intros (n2 & n2' & TR2 & LINK3 & SEQ4 & DM4).
    rewrite LINK1. 
    apply syneq_symm in SEQ2.
    generalize (linking_syneq_comm _ _ _ _ LINK3 (syneq_refl b) SEQ2).
    intros (n3 & LINK4 & SEQ5).
    exists n2, n3. repeat (split; eauto).
    apply syneq_trans with n2'; auto. apply syneq_symm; auto.
    apply defs_match_cong with (nbase n); auto.
    apply defs_match_symm. auto.
Qed.

End LINK_LIST_MATCH.


(** We now adapt the old linking theorems to the new framework *)

(** Define the syntactic equality as permutation of definitons *)
  
Instance ProgSynEq F V : SynEq (program F V) :=
{
  syneq a b := 
    Permutation (prog_defs a) (prog_defs b) /\ 
    (prog_main a) = (prog_main b) /\
    (prog_public a) = (prog_public b)
  ;
}.
Proof.
  - intros. repeat (split; auto). 
  - intros. destruct H as (H1 & H2 & H3).
    repeat (split; auto). 
    apply Permutation_sym; auto.
  - intros. destruct H as (H1 & H2 & H3).
    destruct H0 as (H10 & H20 & H30).
    repeat (split; auto).
    apply Permutation_trans with (prog_defs b); auto.
    eapply eq_trans; eauto.
    eapply eq_trans; eauto.
Defined.

(** Define checking of internal definitions *)
Definition is_var_internal {V} (v: globvar V) :=
  match classify_init (gvar_init v) with
  | Init_definitive _ => true
  | _ => false
  end.

Definition is_def_internal {F V} (is_fun_internal: F -> bool) (def: option (globdef F V)) : bool :=
  match def with
  | None => false
  | Some g =>
    match g with
    | Gvar v => is_var_internal v
    | Gfun f => is_fun_internal f
    end
  end.

(** The instance of the linking framework for CompCert programs *)

Section ProgLanguage.

Context {F V:Type}.

Context (is_fun_internal: F -> bool).

(** Equality between internal definitions *)
Definition def_internal (def: option (AST.globdef F V)) :=
  is_def_internal is_fun_internal def.

Inductive def_eq : 
  option (AST.globdef F V) -> option (AST.globdef F V) -> Prop :=
| fundef_eq : forall f, is_fun_internal f = true -> def_eq (Some (Gfun f)) (Some (Gfun f))
| vardef_eq : forall v1 v2, 
    is_var_internal v1 = true -> is_var_internal v2 = true ->
    gvar_init v1 = gvar_init v2 -> def_eq (Some (Gvar v1)) (Some (Gvar v2)).
  
Lemma def_eq_symm : forall f1 f2, def_eq f1 f2 -> def_eq f2 f1.
Proof.
  intros. inv H.
  - constructor. auto.
  - econstructor; eauto.
Qed.

Lemma def_eq_trans: forall f1 f2 f3, 
    def_eq f1 f2 -> def_eq f2 f3 -> def_eq f1 f3.
Proof.
  intros f1 f2 f3 EQ1 EQ2. inv EQ1. 
  - inv EQ2. constructor. auto.
  - inv EQ2. econstructor; eauto.
    eapply eq_trans; eauto.
Qed.

Lemma def_eq_imply_internal : forall f1 f2,
    def_eq f1 f2 -> def_internal f1 = true /\ def_internal f2 = true.
Proof.
  intros f1 f2 EQ.
  inv EQ.
  - simpl. auto.
  - simpl in *. auto.
Qed.

Lemma def_internal_imply_eq : 
  forall f, def_internal f = true -> def_eq f f.
Proof.
  intros f INT.
  destruct f. destruct g.
  - constructor; auto.
  - simpl in *. constructor; auto.
  - simpl in *. congruence.
Qed.

Instance PERDefEq : PER def_eq :=
{
  PER_Symmetric := def_eq_symm;
  PER_Transitive := def_eq_trans;
}.

Instance DefEq : PERWithFun def_internal :=
{
  eq_imply_fun_true := def_eq_imply_internal;
  fun_true_imply_eq := def_internal_imply_eq;
}.

(** Equality between id and internal definition pairs *)
Definition id_def_internal (iddef: ident * option (AST.globdef F V)) :=
  let '(id, def) := iddef in
  def_internal def.

Definition id_def_eq (iddef1 iddef2: ident * option (AST.globdef F V)) : Prop :=
  let '(id1, def1) := iddef1 in
  let '(id2, def2) := iddef2 in
  id1 = id2 /\ def_eq def1 def2.

Lemma id_def_eq_symm : forall f1 f2, id_def_eq f1 f2 -> id_def_eq f2 f1.
Proof.
  intros. unfold id_def_eq in *.
  destruct f1, f2. destruct H. split; auto.
  apply def_eq_symm; auto.
Qed.

Lemma id_def_eq_trans: forall f1 f2 f3, 
    id_def_eq f1 f2 -> id_def_eq f2 f3 -> id_def_eq f1 f3.
Proof.
  intros f1 f2 f3 EQ1 EQ2. 
  unfold id_def_eq in *. destruct f1, f2, f3.
  destruct EQ1, EQ2. split.
  eapply eq_trans; eauto.
  eapply def_eq_trans; eauto.
Qed.

Lemma id_def_eq_imply_internal : forall f1 f2,
    id_def_eq f1 f2 -> id_def_internal f1 = true /\ id_def_internal f2 = true.
Proof.
  intros f1 f2 EQ.
  unfold id_def_eq in EQ.
  destruct f1, f2. destruct EQ. subst.
  simpl. 
  apply def_eq_imply_internal; eauto.
Qed.

Lemma id_def_interal_imply_eq : 
  forall f, id_def_internal f = true -> id_def_eq f f.
Proof.
  intros f INT.
  destruct f. destruct o. destruct g.
  - simpl. split; auto. constructor; auto.
  - simpl in *. split; auto. constructor; auto.
  - simpl in *. split; auto. congruence.
Qed.

Instance PERIdDefEq : PER id_def_eq :=
{
  PER_Symmetric := id_def_eq_symm;
  PER_Transitive := id_def_eq_trans;
}.

Instance IdDefEq : PERWithFun id_def_internal :=
{
  eq_imply_fun_true := id_def_eq_imply_internal;
  fun_true_imply_eq := id_def_interal_imply_eq;
}.

Definition accum_prog_defs (progs: list (program F V)) := 
  fold_right (fun p l => (prog_defs p) ++ l) [] progs.

Instance ProgDefsMatch: DefsMatch (program F V) :=
{
  defs_match l1 l2 := 
    let l1' := nlist_to_list l1 in
    let l2' := nlist_to_list l2 in
    let defs1 := accum_prog_defs l1' in
    let defs2 := accum_prog_defs l2' in
    list_in_order id_def_eq id_def_internal defs1 defs2;
}.
Proof.
  - intros a b INORDER.
    cbn in *. 
    apply list_in_order_symm. auto.
  - intros a b c INORDER1 INORDER2.
    cbn in *. 
    eapply list_in_order_trans; eauto.
  - intros a1 a2 a3 b INORDER1 INORDER2.
    cbn in *.
    apply list_in_order_app_inv in INORDER1.
    destruct INORDER1 as (l1' & l2' & EQ & INORDER3 & INORDER4).
    rewrite EQ.
    apply list_in_order_app; auto.
    eapply list_in_order_trans; eauto.
    apply list_in_order_symm. auto.
Defined.
  

Lemma permutation_pres_ptree_get_some: forall A (l1 l2: list (ident * A)) a e,
    list_norepet (map fst l2) ->
    Permutation l1 l2 -> (PTree_Properties.of_list l1) ! a = Some e -> 
    (PTree_Properties.of_list l2) ! a = Some e.
Proof. 
  intros A l1 l2 a e NORPT PERM GET.
  apply PTree_Properties.of_list_norepet; auto.
  eapply Permutation_in; eauto.
  apply PTree_Properties.in_of_list; auto.
Qed.

Lemma permutation_pres_ptree_get: forall A (l1 l2: list (ident * A)) a,
    list_norepet (map fst l1) -> 
    list_norepet (map fst l2) -> 
    Permutation l1 l2 -> 
    (PTree_Properties.of_list l1) ! a = (PTree_Properties.of_list l2) ! a.
Proof. 
  intros A l1 l2 a NORPT1 NORPT2 PERM.
  destruct ((PTree_Properties.of_list l1) ! a) eqn:GET1.
  - symmetry. 
    eapply permutation_pres_ptree_get_some; eauto.
  - destruct ((PTree_Properties.of_list l2) ! a) eqn:GET2; auto.
    apply Permutation_sym in PERM.
    generalize (@permutation_pres_ptree_get_some _ _ _ a a0 NORPT1 PERM GET2).
    intros. congruence.
Qed.

Lemma NoDup_list_norepet_equiv : forall A (l: list A),
    NoDup l <-> list_norepet l.
Proof.
  induction l as [|a l].
  - split; intros. constructor. constructor.
  - split; intros. 
    + inv H. constructor; auto. rewrite <- IHl. auto.
    + inv H. constructor; auto. rewrite IHl. auto.
Qed.

Lemma permutation_pres_list_norepet: forall A (l1 l2: list A),
  list_norepet l1 -> Permutation l1 l2 -> list_norepet l2.
Proof.
  intros. rewrite <- NoDup_list_norepet_equiv in *.
  eapply Permutation_NoDup; eauto.
Qed.

Lemma permutation_map_pres_list_norepet: forall {A B} (l1 l2: list A) (f:A -> B),
  list_norepet (map f l1) -> Permutation l1 l2 -> list_norepet (map f l2).
Proof.
  intros. 
  apply permutation_pres_list_norepet with (map f l1); auto.
  apply Permutation_map; auto.
Qed.


Lemma prog_linking_syneq_comm {LF: Linker F} {LV: Linker V}: 
  forall m1 m2 m1' m2' m : (program F V),
    link m1 m2 = Some m -> syneq m1 m1' -> syneq m2 m2' -> 
    exists m', link m1' m2' = Some m' /\ syneq m m'.
Proof.
  cbn in *. 
  intros m1 m2 m1' m2' m LINK SEQ1 SEQ2.
  apply link_prog_inv in LINK.
  destruct LINK as (MINEQ & NORPT1 & NORPT2 & LK & EQ). subst.
  cbn.
  destruct SEQ1 as (PERM1 & MAINEQ1 & PUBEQ1).
  destruct SEQ2 as (PERM2 & MAINEQ2 & PUBEQ2).
  assert (prog_main m1' = prog_main m2') as MAINEQ' by congruence.
  Existing Instance Linker_option.
  assert (forall (id : positive) (gd1 gd2 : option (globdef F V)),
          (prog_option_defmap m1') ! id = Some gd1 ->
          (prog_option_defmap m2') ! id = Some gd2 ->
          In id (prog_public m1') /\ In id (prog_public m2') /\ link gd1 gd2 <> None)
    as PROP.
  { 
    intros id gd1 gd2 GD1 GD2.
    unfold prog_option_defmap in *.
    generalize (Permutation_sym PERM1). intros PERM1'.
    generalize (permutation_pres_ptree_get_some id NORPT1 PERM1' GD1).
    intros GD1'.
    generalize (Permutation_sym PERM2). intros PERM2'.
    generalize (permutation_pres_ptree_get_some id NORPT2 PERM2' GD2).
    intros GD2'.
    exploit LK; eauto.
    intros (PUB1 & PUB2 & gd & LKK).
    repeat (split; auto).
    congruence.
    congruence.
    congruence.
  }
  generalize (permutation_map_pres_list_norepet fst NORPT1 PERM1). 
  intros NORPT1'.
  generalize (permutation_map_pres_list_norepet fst NORPT2 PERM2). 
  intros NORPT2'.
  generalize (link_prog_succeeds _ _ MAINEQ' NORPT1' NORPT2' PROP).
  intros LINK'. setoid_rewrite LINK'.
  eexists; split; eauto. cbn.
  repeat (split; try congruence).
  apply NoDup_Permutation.
  - apply NoDup_map_inv with (f:=fst). 
    rewrite NoDup_list_norepet_equiv.
    apply PTree.elements_keys_norepet.
  - apply NoDup_map_inv with (f:=fst). 
    rewrite NoDup_list_norepet_equiv.
    apply PTree.elements_keys_norepet.
  - intros. destruct x as [id def].
    split.
    + intros IN. 
      apply PTree.elements_correct.
      rewrite PTree.gcombine; auto.
      unfold prog_option_defmap.
      rewrite <- (permutation_pres_ptree_get id NORPT1 NORPT1' PERM1).
      rewrite <- (permutation_pres_ptree_get id NORPT2 NORPT2' PERM2).
      rewrite <- PTree.gcombine; auto.
      apply PTree.elements_complete; auto.
    + intros IN.
      apply PTree.elements_correct.
      rewrite PTree.gcombine; auto.
      unfold prog_option_defmap.
      rewrite (permutation_pres_ptree_get id NORPT1 NORPT1' PERM1).
      rewrite (permutation_pres_ptree_get id NORPT2 NORPT2' PERM2).
      rewrite <- PTree.gcombine; auto.
      apply PTree.elements_complete; auto.
Qed.    


Instance ProgLinkingSynEq {LF: Linker F} {LV: Linker V}
  : @LinkingSynEq (program F V) _ _ :=
{
  linking_syneq_comm := prog_linking_syneq_comm;
}.

End ProgLanguage.


Lemma list_forall2_permutation: forall A B (f:A -> B -> Prop) (l1 l1': list A) l2,
    list_forall2 f l1 l2 -> Permutation l1 l1' -> 
    exists l2', list_forall2 f l1' l2' /\ Permutation l2 l2'.
Proof.
  intros. generalize dependent l2.
  induction H0; cbn; intros.
  - inv H. exists nil. split; auto. constructor.
  - inv H. generalize (IHPermutation _ H5).
    intros (l2'' & FA & PERM).
    exists (b1 :: l2''). split; auto.
    constructor; auto.
  - inv H. inv H4.
    exists (b0 :: b1 :: bl0). split; auto.
    repeat (constructor; auto).
    constructor.
  - edestruct IHPermutation1 as (l2' & FA1 & PERM1); eauto.
    edestruct IHPermutation2 as (l2'' & FA2 & PERM2); eauto.
    eexists; split; eauto.
    eapply perm_trans; eauto.
Qed.

(** More properties about match program *)

Lemma match_program_gen_permute: 
  forall {C F1 V1 F2 V2: Type} {LC: Linker C} 
    {LF: Linker F1} {LV: Linker V1}
    (match_fundef: C -> F1 -> F2 -> Prop)
    (match_varinfo: V1 -> V2 -> Prop)
    (ctx:C) (p1 p1': program F1 V1) (p2: program F2 V2), 
  match_program_gen match_fundef match_varinfo ctx p1 p2 -> syneq p1 p1' ->
  exists p2', match_program_gen match_fundef match_varinfo ctx p1' p2' /\ syneq p2 p2'.
Proof.
  cbn in *. 
  intros until p2.
  intros MATCH (PERM & MINEQ & PUBEQ).
  unfold match_program_gen in *.
  destruct MATCH as (MATCH & MAINEQ1 & PUBEQ1).
  generalize (list_forall2_permutation MATCH PERM).
  intros (defs2 & MATCH' & PERM').
  exists {| prog_defs := defs2; 
       prog_public := prog_public p1; 
       prog_main := prog_main p1 |}.
  cbn.
  repeat (split; try congruence).
Qed.

Lemma link_prog_order_permutation: 
  forall {F V} {LF: Linker F} {LV: Linker V}
    (p1 p2: program F V),
    prog_main p1 = prog_main p2 ->
    incl (prog_public p1) (prog_public p2) ->
    list_norepet (map fst (prog_defs p1)) ->
    list_norepet (map fst (prog_defs p2)) ->
    Permutation (prog_defs p1) (prog_defs p2) ->
    linkorder p1 p2.
Proof.
  Local Transparent Linker_prog.
  Local Transparent Linker_option.
  cbn.
  intros F V LF LV p1 p2 MAINEQ PUB NORPT1 NORPT2 PERM.
  repeat (split; auto).
  unfold prog_option_defmap.
  intros id gd1 GET.
  exists gd1.
  rewrite <- permutation_pres_ptree_get with (l1:=prog_defs p1); auto.
  split; auto. split; auto.
  apply Linking.Linker_option_obligation_1.
Qed.

Lemma match_program_gen_ctx_syneq: 
  forall {F1 V1} {LF: Linker F1} {LV: Linker V1}
    {F2 V2} {LF: Linker F2} {LV: Linker V2}
    (ctx1 ctx2: program F1 V1) (p1: program F1 V1) (p2: program F2 V2) mf mv,
    syneq ctx1 ctx2 ->
    list_norepet (map fst (prog_defs ctx1)) ->
    list_norepet (map fst (prog_defs ctx2)) ->
    match_program_gen mf mv ctx1 p1 p2 ->
    match_program_gen mf mv ctx2 p1 p2.
Proof.
  intros until mv. 
  intros SEQ NORPT1 NORPT2 MATCH. cbn in SEQ.
  destruct SEQ as (PERM & MAINEQ & PUBEQ).  
  eapply match_program_gen_extend_ctx; eauto.
  eapply link_prog_order_permutation; eauto.
  rewrite PUBEQ. red. auto.
Qed.  


(** We require matching programs to have unique definitions *)
Definition match_program' {F1 V1} {F2 V2}
           {LF: Linker F1} {LV: Linker V1}
           (match_fundef: program F1 V1 -> F1 -> F2 -> Prop)
           (match_varinfo: V1 -> V2 -> Prop) 
           p1 p2 :=
  list_norepet (map fst (prog_defs p1)) /\
  match_program match_fundef match_varinfo p1 p2.


(** Properties needed to define compiler passes *)

(** Commutativity betwen the translation and syntactic equality *)
Instance ProgTransfSynEq {C F1 V1 F2 V2: Type} 
         {LC: Linker C} 
         {LF1: Linker F1} {LV1: Linker V1}
         {LF2: Linker F2} {LV2: Linker V2}
         (match_fundef: program F1 V1 -> F1 -> F2 -> Prop)
         (match_varinfo: V1 -> V2 -> Prop):
         TransfSynEq (fun (p1: program F1 V1) (p2: program F2 V2) => match_program' match_fundef match_varinfo p1 p2).
Proof.
  red. intros m1 m2 m1' TR SEQ.
  unfold match_program in *. 
  red in TR. destruct TR as (NORPT & TR).
  edestruct (match_program_gen_permute TR SEQ) as (m2'' & MATCH & SEQ1); eauto.
  exists m2''. split; auto.
  red. split.
  apply permutation_map_pres_list_norepet with (l1:=(prog_defs m1)); auto.
  apply SEQ.
  eapply match_program_gen_ctx_syneq; eauto.
  apply permutation_map_pres_list_norepet with (l1:=(prog_defs m1)); auto.
  apply SEQ.
Qed.


(** Commutativity between the translation and matching of definitions *)

Definition match_fundef_pres_internal
           {C F1 F2:Type}
           (is_fun_internal: forall A:Type, A -> bool)
           (match_fundef: C -> F1 -> F2 -> Prop) :=
  forall ctx f1 f2, match_fundef ctx f1 f2 -> is_fun_internal F1 f1 = is_fun_internal F2 f2.

Instance ProgTransfDefsMatch {F1 F2 V1 V2:Type}
         {LV1: Linker V1} {LF1: Linker F1}
         {LV2: Linker V2} {LF2: Linker F2}
         (is_fun_internal: forall A:Type, A -> bool)
         (match_fundef: program F1 V1 -> F1 -> F2 -> Prop)
         (match_varinfo: V1 -> V2 -> Prop) 
         (match_fundef_internal: match_fundef_pres_internal is_fun_internal match_fundef):
         @TransfDefsMatch _ _
                          (@ProgDefsMatch _ V1 (@is_fun_internal F1))
                          (@ProgDefsMatch _ V2 (@is_fun_internal F2))
                          (fun (p1: program F1 V1) (p2: program F2 V2) => match_program' match_fundef match_varinfo p1 p2).
Proof.
  red. intros ms ms' tms tms' DM TR1 TR2.
  cbn in *.
  list_forall2 (match_ident_option_globdef match_fundef match_varinfo ctx) (prog_defs p1) (prog_defs p2) /\
  apply nlist_forall2_Forall in TR1.
  apply nlist_forall2_Forall in TR2.
  remember  as defs1.
  remember (fold_right (fun p l => prog_defs p ++ l) [] (nlist_to_list tms)) as defs2.
  (* remember (id_def_eq is_fun_internal) as defeq. *)
  (* remember (id_def_internal is_fun_internal) as defint. *)
  (* induction DM. *)
  clear.
  Admitted.


Instance ProgTransfDefsMatchVarEq {F1 F2 V: Type}
         {LV: Linker V}
         {LF1: Linker F1} {LF2: Linker F2}
         (is_fun_internal: forall A:Type, A -> bool)
         (match_fundef: program F1 V -> F1 -> F2 -> Prop):
         @TransfDefsMatch _ _ 
                          (@ProgDefsMatch _ V (is_fun_internal F1))
                          (@ProgDefsMatch _ V (is_fun_internal F2))
                          (fun (p1: program F1 V) (p2: program F2 V) => match_program match_fundef eq p1 p2).
Proof.
  red. apply (@transf_defs_match_comm _ _ _ _ _ 
                                      (@ProgTransfDefsMatch _ _ _ _ _ _ _ _ is_fun_internal match_fundef eq)).
Qed.

Definition is_fundef_internal {A:Type} (fd: fundef A) : bool :=
  match fd with
  | Internal _ => true
  | External _ => false
  end.

(** Commutativity between transformation and linking *)
Instance TransfPartialContextualLink
         {A B C V: Type} {LV: Linker V}
         (tr_fun: C -> A -> res B)
         (ctx_for: program (fundef A) V -> C):
         @TransfLink _ _ _ _ _ _ 
                     (ProgDefsMatch is_fundef_internal)
                     (ProgDefsMatch is_fundef_internal)
                     (fun (p1: program (fundef A) V) (p2: program (fundef B) V) =>
                        match_program
                          (fun cu f tf => AST.transf_partial_fundef (tr_fun (ctx_for cu)) f = OK tf)
                          eq p1 p2).
Proof.
  red. intros until m'.
  intros LINK TR1 TR2 SEQ DM.
  generalize (Linking.transf_link _ _ _ _ _ LINK TR1 TR2).
  intros (tp & LINK1 & TR3).
  generalize (transf_syneq_comm m m' tp TR3 SEQ).
  intros (tp1 & TR4 & SEQ2).
  exists tp1, tp. repeat (split; auto).
  apply (@transf_defs_match_comm _ _ _ _ _ with (ncons m1 (nbase m2)) (nbase m'); auto.
  - constructor; eauto.
    constructor; eauto.
  - constructor; eauto.
Defined.
  
