(* ********************* *)
(* Author: Yuting Wang   *)
(* Date:   Oct 31, 2019   *)
(* ********************* *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Asm RelocProgram.
Require Import Symbtablegen.
Require Import Linking LinkingProp OrderedLinking.
Require Import PermuteProgSep.
Require Import RelocLinking.
Require Import SeqTable.
Require Import RelationClasses.
Require Import RelocProgSyneq.
Require Import Permutation.
Require Import LocalLib.
Require Import Symbtablegenproof1.
Require Import AsmFacts.
Require Import SizeBoundAxioms.
Import ListNotations.

Set Implicit Arguments.

Local Transparent Linker_def.
Local Transparent Linker_fundef.
Local Transparent Linker_vardef.
Local Transparent Linker_varinit.
Local Transparent Linker_prog_ordered.

Hint Resolve link_prog_merge_symm.


Lemma elements_in_partition_prop: forall A f (l l1 l2: list A),
    partition f l = (l1, l2) -> 
    (forall x, In x l1 -> f x = true) /\ (forall x, In x l2 -> f x = false).
Proof.
  induction l; intros until l2; simpl.
  - inversion 1. subst. 
    split; intros; simpl in *; contradiction.
  - intros PART. destr_in PART. 
    generalize (IHl _ _ (@eq_refl _ (l0, l3))).
    destruct 1 as (IN1 & IN2).
    destr_in PART; inv PART; split; intros; auto.
    inv H; auto.
    inv H; auto.
Qed.

Lemma defs_in_partition_id_not_in : 
  forall F V (LV: Linker V)
    id (l l1 l2: list (ident * option (globdef (AST.fundef F) V))),
    partition (fun '(id', _) => ident_eq id' id) l = (l1, l2) 
    -> ~ In id (map fst l2).
Proof. 
  intros F V LV id l l1 l2 PART.
  apply elements_in_partition_prop in PART.
  destruct PART.
  rewrite in_map_iff. intro IN.
  destruct IN as (def & EQ & IN3).
  generalize (H0 _ IN3). destruct def. 
  inv EQ. cbn. 
  destruct peq; auto. intros. inv H1.
Qed.

Lemma part_not_in_nil : forall F V id (defs defs' l: list (ident * option (globdef (AST.fundef F) V))),
    partition (fun '(id', _) => ident_eq id' id) defs = (l, defs') ->
    ~ In id (map fst defs) ->
    l = nil.
Proof.
  induction defs. 
  - intros defs' l PART NIN.
    simpl in *. inv PART. auto.
  - intros defs' l PART NIN.
    simpl in *. destr_in PART. 
    destruct a, ident_eq; simpl in *; subst; inv PART.
    exfalso. apply NIN. auto.
    eapply IHdefs; eauto.
Qed.

Lemma lst_norepet_partition_inv : forall F V id (defs defs1 defs2: list (ident * option (globdef (AST.fundef F) V))),
    list_norepet (map fst defs) ->
    partition (fun '(id', _) => ident_eq id' id) defs = (defs1, defs2) ->
    defs1 = nil \/ exists def, defs1 = [def].
Proof.
  induction defs.
  - intros defs1 defs2 NORPT PART.
    simpl in *. inv PART. auto.
  - intros defs1 defs2 NORPT PART.
    simpl in *. inv NORPT.
    destr_in PART. destruct a.
    destruct ident_eq; simpl in *; inv PART.
    + generalize (part_not_in_nil _ _ Heqp H1).
      intros. subst.
      eauto.
    + eauto.
Qed.

Lemma partition_pres_list_norepet : forall F V f (l l1 l2: list (ident * option (globdef (AST.fundef F) V))),
    partition f l = (l1, l2) -> 
    list_norepet (map fst l) ->
    list_norepet (map fst l1) /\ list_norepet (map fst l2).
Proof.
  induction l.
  - intros l1 l2 PART NORPT.
    simpl in *. inv PART. auto.
  - intros l1 l2 PART NORPT.
    simpl in *. inv NORPT. destr_in PART.
    destr_in PART. 
    + inv PART.
      generalize (IHl _ _ (@eq_refl _ (l0, l2)) H2).
      destruct 1. split; auto. simpl. constructor; auto.
      intro IN. apply H1. 
      generalize (elements_in_partition _ _ Heqp).
      intros ELEM.
      apply list_in_map_inv in IN. 
      destruct IN as (b & EQ & IN). 
      rewrite in_map_iff.
      exists b.  split; auto.
      rewrite ELEM. auto.
    + inv PART.
      generalize (IHl _ _ (@eq_refl _ (l1, l3)) H2).
      destruct 1.
      split; auto.
      simpl. constructor; auto.
      intro IN. apply H1.
      generalize (elements_in_partition _ _ Heqp).
      intros ELEM.
      rewrite in_map_iff in *.
      destruct IN as (x & EQ & IN).
      eexists; split; eauto.
      rewrite ELEM. auto.
Qed.


Lemma get_internal_var_entry : forall dsec csec dsz csz id v,
    is_var_internal v = true ->
    get_symbentry dsec csec dsz csz id (Some (Gvar v)) =       
    {|symbentry_id := id;
      symbentry_bind := get_bind_ty id;
      symbentry_type := symb_data;
      symbentry_value := dsz;
      symbentry_secindex := secindex_normal dsec;
      symbentry_size := AST.init_data_list_size (AST.gvar_init v);
    |}.
Proof.
  intros dsec csec dsz csz id v INT.
  unfold is_var_internal in INT.
  cbn.
  destruct (gvar_init v); cbn in INT; try congruence.
  destruct i; cbn in INT; try congruence.
  destruct l; cbn in INT; try congruence.
Qed.

Lemma get_comm_var_entry : forall dsec csec dsz csz id v,
    is_var_comm v = true ->
    get_symbentry dsec csec dsz csz id (Some (Gvar v)) =       
    {|symbentry_id := id;
      symbentry_bind := get_bind_ty id;
      symbentry_type := symb_data;
      symbentry_value := 8 ; 
      symbentry_secindex := secindex_comm;
      symbentry_size := Z.max (AST.init_data_list_size (gvar_init v)) 0;
    |}.
Proof.
  intros dsec csec dsz csz id v INT.
  unfold is_var_comm in INT.
  cbn.
  destruct (gvar_init v); cbn in INT; try congruence.
  destruct i; cbn in INT; try congruence.
  destruct l; cbn in INT; try congruence.
  cbn. f_equal.
  rewrite Z.add_comm. cbn.
  rewrite (@Z_max_0 (Z.max z 0)). auto.
  apply Z.le_ge.
  apply Z.le_max_r.
Qed.

Lemma get_external_var_entry : forall dsec csec dsz csz id v,
    is_var_extern v = true ->
    get_symbentry dsec csec dsz csz id (Some (Gvar v)) =       
    {|symbentry_id := id;
      symbentry_bind := get_bind_ty id;
      symbentry_type := symb_data;
      symbentry_value := 0;
      symbentry_secindex := secindex_undef;
      symbentry_size := 0;
    |}.
Proof.
  intros dsec csec dsz csz id v INT.
  unfold is_var_extern in INT.
  cbn.
  destruct (gvar_init v); cbn in INT; try congruence.
  destruct i; cbn in INT; try congruence.
  destruct l; cbn in INT; try congruence.
Qed.



(** * Commutativity of linking and Symbtablgen *)

Definition match_prog (p: Asm.program) (tp: program) :=
  exists tp', transf_program p = OK tp' /\ reloc_prog_syneq tp' tp.


Lemma match_prog_pres_prog_defs : forall p tp,
  match_prog p tp -> Permutation (AST.prog_defs p) (prog_defs tp).
Proof.
  intros p tp MATCH. red in MATCH.
  destruct MATCH as (tp' & MATCH & SEQ).
  unfold transf_program in MATCH.
  destruct check_wellformedness; try monadInv MATCH.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p)) eqn:EQ.
  destruct p0.
  destruct zle; try monadInv MATCH.
  red in SEQ; cbn in SEQ. 
  tauto.
Qed.

Lemma match_prog_pres_prog_main : forall p tp,
  match_prog p tp -> AST.prog_main p = prog_main tp.
Proof.
  intros p tp MATCH. red in MATCH.
  destruct MATCH as (tp' & MATCH & SEQ).
  unfold transf_program in MATCH.
  destruct check_wellformedness; try monadInv MATCH.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p)) eqn:EQ.
  destruct p0.
  destruct zle; try monadInv MATCH. 
  red in SEQ; cbn in SEQ. 
  tauto.
Qed.

Lemma match_prog_pres_prog_public : forall p tp,
  match_prog p tp -> AST.prog_public p = prog_public tp.
Proof.
  intros p tp MATCH. red in MATCH.
  destruct MATCH as (tp' & MATCH & SEQ).
  unfold transf_program in MATCH.
  destruct check_wellformedness; try monadInv MATCH.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p)) eqn:EQ.
  destruct p0.
  destruct zle; try monadInv MATCH. 
  red in SEQ; cbn in SEQ.
  tauto.
Qed.

  
Lemma eq_gvar_init_pres_aligned : forall v1 v2,
    gvar_init v1 = gvar_init v2 
    -> def_aligned (Some (Gvar v1))
    -> def_aligned (Some (Gvar v2)).
Proof.
  intros. cbn in *. rewrite <- H.
  auto.
Qed.

Lemma link_varinit_internal_external_pres_aligned:
  forall (v1 v2: globvar unit) l inf rd vl,
    is_var_internal v2 = false
    -> def_aligned (Some (Gvar v1))
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some l
    -> def_aligned (Some (Gvar (mkglobvar inf l rd vl))).
Proof.
  intros v1 v2 l inf rd vl INT2 ALIGN LINK.
  destruct (is_var_internal v1) eqn:INT1.
  - generalize (link_internal_external_varinit _ _ _ INT1 INT2 LINK).
    destruct 1 as (EQ & CLS). subst.   
    apply eq_gvar_init_pres_aligned with v1; auto.
  - generalize (link_external_varinit _ _ _ INT1 INT2 LINK).
    intros CLS.
    destruct l. cbn. auto.
    cbn in *. destruct i; try congruence.
    destruct l; try congruence. auto.
Qed.


Lemma link_vardef_internal_external_pres_aligned:
  forall v1 v2 v,
    is_var_internal v2 = false
    -> def_aligned (Some (Gvar v1))
    -> link_vardef v1 v2 = Some v
    -> def_aligned (Some (Gvar v)).
Proof.
  intros v1 v2 v INT ALIGN LINK.
  unfold link_vardef in LINK. 
  destr_in LINK; try congruence.
  destr_in LINK; try congruence.
  destr_in LINK; try congruence.
  inv LINK. unfold is_var_internal in INT.
  eapply link_varinit_internal_external_pres_aligned; eauto.
Qed.
  

Lemma external_var_aligned: forall v,
    is_var_internal v = false -> def_aligned (Some (Gvar v)).
Proof.
  intros v INT.
  unfold is_var_internal in INT.
  cbn. destruct (gvar_init v); cbn in *; try congruence.
  auto.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
  auto.
Qed.


Lemma link_option_internal_external_pres_aligned: forall def1 def2 def,
    is_def_internal is_fundef_internal def2 = false
    -> def_aligned def1
    -> link_option def1 def2 = Some def
    -> def_aligned def.
Proof.
  intros def1 def2 def INT ALIGN LINK.
  destruct def2. destruct g. destruct f; cbn in *; try congruence.
  - destruct def1. destruct g. destruct f. 
    + cbn in LINK. destr_in LINK; try congruence. inv LINK.
      destr_in Heqo; try congruence; inv Heqo.
      destruct e; try congruence. inv Heqo0. auto.
    + cbn in LINK. destr_in LINK; try congruence. inv LINK.
      destr_in Heqo; try congruence; inv Heqo.
      destr_in Heqo0; try congruence. 
    + cbn in LINK. congruence.
    + cbn in LINK. inv LINK. auto.
  - destruct def1. destruct g.
    + cbn in *. congruence.
    + cbn in LINK. destr_in LINK; try congruence.
      destr_in Heqo; try congruence. inv Heqo. inv LINK.
      cbn in INT.
      eapply link_vardef_internal_external_pres_aligned; eauto.
    + cbn in *. inv LINK.       
      eapply external_var_aligned; eauto.
  - destruct def1. cbn in LINK. inv LINK. auto.
    cbn in *. inv LINK. auto.
Qed.

Hint Resolve link_unit_symm.

Lemma link_pres_aligned: forall def1 def2 def,
    def_aligned def1 ->
    def_aligned def2 ->
    link def1 def2 = Some def -> 
    def_aligned def.
Proof.
  intros def1 def2 def AL1 AL2 LINK.
  cbn in LINK.
  destruct (is_def_internal is_fundef_internal def1) eqn:INT1.
  - generalize (link_int_defs_some_inv _ _ INT1 LINK).
    intros INT2.
    apply link_option_internal_external_pres_aligned 
      with (def1 := def1) (def2 := def2); eauto.
  - setoid_rewrite link_option_symm in LINK; eauto.
    apply link_option_internal_external_pres_aligned 
      with (def1 := def2) (def2 := def1); eauto.
Qed.


(** ** Commutativity of linking and section generation *)

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


Section WithFunVar.

Context {F V:Type}.

(** Equality between internal definitions *)
Definition def_internal (def: option (AST.globdef (AST.fundef F) V)) :=
  is_def_internal is_fundef_internal def.

Inductive def_eq : 
  option (AST.globdef (AST.fundef F) V) -> option (AST.globdef (AST.fundef F) V) -> Prop :=
| fundef_eq : forall f, is_fundef_internal f = true -> def_eq (Some (Gfun f)) (Some (Gfun f))
| vardef_eq : forall v1 v2, 
    is_var_internal v1 = true -> is_var_internal v2 = true ->
    gvar_init v1 = gvar_init v2 -> def_eq (Some (Gvar v1)) (Some (Gvar v2)).
  
Lemma def_eq_pres_internal: forall (def1 def2: option (globdef (AST.fundef F) V)),
  def_eq def1 def2 -> def_internal def1 = def_internal def2.
Proof.
  inversion 1; cbn; subst.
  rewrite H0. auto.
  rewrite H0. auto.
Qed.

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
Definition id_def_internal (iddef: ident * option (AST.globdef (AST.fundef F) V)) :=
  let '(id, def) := iddef in
  def_internal def.

Definition id_def_eq (iddef1 iddef2: ident * option (AST.globdef (AST.fundef F) V)) : Prop :=
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

Lemma link_internal_external_defs : forall {LV: Linker V} (def1 def2 def: option (globdef (AST.fundef F) V)),
    def_internal def1 = true ->
    def_internal def2 = false ->
    link_option def1 def2 = Some def ->
    def_eq def def1.
Proof.
  intros LV def1 def2 def INT1 INT2 LINK.
  unfold link_option in LINK.
  destruct def1, def2.
  - destr_in LINK. inv LINK. simpl in *.
    destruct g, g0; simpl in *; try congruence.
    + destr_in Heqo. inv Heqo.
      generalize (link_extern_fundef_inv _ _ INT2 Heqo0). 
      intros. subst. constructor. auto.
    + destr_in Heqo. inv Heqo.
      generalize (link_internal_external_vars _ _ _ INT1 INT2 Heqo0).
      destruct 1.
      constructor; auto.
  - inv LINK. apply def_internal_imply_eq; auto.
  - simpl in *. congruence.
  - simpl in *. congruence.
Qed.  

Lemma link_internal_external_defs' : forall {LV: Linker V} (def1 def2 def: option (globdef (AST.fundef F) V)),
    def_internal def1 = true ->
    link_option def1 def2 = Some def ->
    def_eq def def1.
Proof.
  intros LV def1 def2 def INT1 LINK.
  eapply link_internal_external_defs; eauto.
  eapply link_int_defs_some_inv; eauto.
Qed.
  

End WithFunVar.
(** *)

(** Preparation for proofs of linking code and data sections *)

Lemma PTree_extract_elements_remain_ids_not_in: 
  forall {A:Type} ids defs (t t': PTree.t A),
    PTree_extract_elements ids t = Some (defs, t') ->
    Forall (fun id' => ~ In id' ids) (map fst (PTree.elements t')).
Proof.
  intros A ids defs t t' EXT. 
  generalize (PTree_extract_elements_remain _ _ _ _ EXT).
  intros subst.
  rewrite Forall_forall. intros id IN.
  apply list_in_map_inv in IN.
  destruct IN as ((id', def') & EQ & IN). subst. cbn.
  apply PTree.elements_complete in IN. cbn.
  apply PTree_remove_ids_not_in in IN; auto.
Qed.


Lemma filter_internal_defs_some_int: 
  forall {F V} {LV: Linker V} (defs: list(ident * option (globdef (AST.fundef F) V))) id,
    list_norepet (map fst defs) ->
    In id (map fst
               (filter (fun '(_, def) => is_def_internal is_fundef_internal def) defs)) ->
    def_some_int is_fundef_internal (PTree_Properties.of_list defs) ! id.
Proof.
  induction defs as [|def defs].
  - cbn. tauto.
  - intros id NORPT IN. cbn in IN.
    destruct def as (id', def').
    destr_in IN. 
    + cbn in IN. destruct IN as [EQ | IN]. 
      * subst.
        replace ((id, def') :: defs) with (nil ++ (id, def') :: defs) by auto.
        erewrite PTree_Properties.of_list_unique; eauto.
        red. eauto.
        inv NORPT. eauto.
      * inv NORPT.
        assert (id <> id'). 
        { intros H. subst. apply H1.
          eapply in_map_filter; eauto. }
        erewrite PTree_Properties_of_list_tail; eauto.
    + inv NORPT.
      assert (id <> id'). 
      { intros H. subst. apply H1.
        eapply in_map_filter; eauto. }
      erewrite PTree_Properties_of_list_tail; eauto.
Qed.

Lemma collect_defs_some_int: 
  forall {F V} {LV: Linker V} (p: AST.program (AST.fundef F) V),
    list_norepet (map fst (AST.prog_defs p)) ->
    defs_some_int (prog_option_defmap p)
                  (collect_internal_def_ids is_fundef_internal p).
Proof.
  intros. 
  unfold collect_internal_def_ids.
  unfold filter_internal_defs.
  unfold prog_option_defmap.
  red.
  intros.
  eapply filter_internal_defs_some_int; eauto.
Qed.


Lemma filter_internal_defs_none_ext: 
  forall {F V} {LV: Linker V} (defs: list(ident * option (globdef (AST.fundef F) V))) id,
    list_norepet (map fst defs) ->
    ~In id (map fst
                (filter (fun '(_, def) => is_def_internal is_fundef_internal def) defs)) ->
    def_none_or_ext is_fundef_internal (PTree_Properties.of_list defs) ! id.
Proof.
  induction defs as [|def defs].
  - cbn. 
    intros. rewrite PTree.gempty. red. auto.
  - intros id NORPT NIN. cbn in NIN. inv NORPT.
    destruct def as (id', def').
    destr_in NIN.
    + cbn in NIN. 
      apply Decidable.not_or in NIN.
      destruct NIN as [NEQ NIN].
      erewrite PTree_Properties_of_list_tail; eauto.
    + cbn in H1.
      destruct (ident_eq id id').
      * subst.
        replace ((id', def') :: defs) with (nil ++ ((id', def') :: defs)) by auto.
        erewrite PTree_Properties.of_list_unique; eauto.
        red. eauto.
      * erewrite PTree_Properties_of_list_tail; eauto.
Qed.

Lemma collect_defs_none_ext: 
  forall {F V} {LV: Linker V} ids (p: AST.program (AST.fundef F) V),
    list_norepet (map fst (AST.prog_defs p)) ->
    Forall (fun id => ~In id (collect_internal_def_ids is_fundef_internal p)) ids ->
    defs_none_or_ext (prog_option_defmap p) ids.
Proof.
  unfold collect_internal_def_ids.
  unfold filter_internal_defs.
  unfold prog_option_defmap.
  red.
  intros.
  eapply filter_internal_defs_none_ext; eauto.
  rewrite Forall_forall in H0.
  eauto.
Qed.


Lemma PTree_extract_elements_remain_external: 
  forall {F V} {LV: Linker V} (p1 p2: AST.program (AST.fundef F) V) defs3 t1,
    list_norepet (map fst (AST.prog_defs p1)) ->
    list_norepet (map fst (AST.prog_defs p2)) ->
    PTree_extract_elements
      (collect_internal_def_ids is_fundef_internal p1 ++
                                collect_internal_def_ids is_fundef_internal p2)
      (PTree.combine link_prog_merge 
                     (prog_option_defmap p1)
                     (prog_option_defmap p2)) = Some (defs3, t1) ->
    defs_none_or_ext (prog_option_defmap p1) (map fst (PTree.elements t1)) /\
    defs_none_or_ext (prog_option_defmap p2) (map fst (PTree.elements t1)).
Proof.
  intros F V LV p1 p2 defs3 t1 NORPT1 NORPT2 EXT.
  generalize (PTree_extract_elements_remain_ids_not_in _ _ EXT).
  intros NIN.
  split.
  - eapply collect_defs_none_ext; eauto.
    rewrite Forall_forall in *. intros. 
    apply NIN in H. intros IN. apply H.
    rewrite in_app. auto.
  - eapply collect_defs_none_ext; eauto.
    rewrite Forall_forall in *. intros. 
    apply NIN in H. intros IN. apply H.
    rewrite in_app. auto.
Qed.

Lemma combine_defs_none_or_ext: 
  forall {F V} {LV: Linker V} ids defs (t1 t2: PTree.t (option (globdef (AST.fundef F) V))),
    defs_none_or_ext t1 ids ->
    defs_none_or_ext t2 ids ->
    PTree_combine_ids_defs_match t1 t2 link_prog_merge ids defs ->
    Forall (fun '(id, def) => is_def_internal is_fundef_internal def = false) defs.
Proof.
  induction ids as [|id ids].
  - intros defs t1 t2 DEXT1 DEXT2 MATCH.
    inv MATCH. auto.
  - intros defs t1 t2 DEXT1 DEXT2 MATCH.
    generalize (defs_none_or_ext_head DEXT1).
    generalize (defs_none_or_ext_head DEXT2).
    intros DE1 DE2.
    inv MATCH. destruct y. destruct H1; subst.    
    apply Forall_cons.
    eapply (link_prog_merge_defs_none_or_ext DE2 DE1); eauto.
    eapply IHids; eauto.
    eapply defs_none_or_ext_tail; eauto.
    eapply defs_none_or_ext_tail; eauto.
Qed.

Lemma PTree_extract_elements_remain_external': 
  forall (F V : Type) (LV : Linker V) (p1 p2 : AST.program (AST.fundef F) V)
    (defs3 : list (ident * option (globdef (AST.fundef F) V)))
    (t1 : PTree.t (option (globdef (AST.fundef F) V))),
    list_norepet (map fst (AST.prog_defs p1)) ->
    list_norepet (map fst (AST.prog_defs p2)) ->
    PTree_extract_elements
      (collect_internal_def_ids is_fundef_internal p1 ++
                                collect_internal_def_ids is_fundef_internal p2)
      (PTree.combine link_prog_merge (prog_option_defmap p1) (prog_option_defmap p2)) =
    Some (defs3, t1) ->
    Forall (fun '(id, def) => is_def_internal is_fundef_internal def = false) (PTree.elements t1).
Proof.
  intros F V LV p1 p2 defs3 t1 NORPT1 NORPT2 EXTR.
  generalize (PTree_extract_elements_remain_external _ _ NORPT1 NORPT2 EXTR).
  intros (DNE1 & DNE2).
  eapply @combine_defs_none_or_ext with 
      (t1:=prog_option_defmap p1) (t2:=prog_option_defmap p2); eauto.
  eapply PTree_extract_elements_combine_remain_match; eauto.
Qed.


Lemma link_merge_internal_external_defs:
  forall (F V : Type) (LV : Linker V)
    def2 (def1 def : option (globdef (AST.fundef F) V)),
    def_internal def1 = true -> 
    link_prog_merge (Some def1) def2 = Some def -> 
    def_eq def def1.
Proof.
  intros F V LV def2 def1 def INT LINK.
  cbn in LINK. destr_in LINK.
  - subst. eapply link_internal_external_defs'; eauto.
  - inv LINK. eapply def_internal_imply_eq; eauto.
Qed.

Lemma get_def_init_data_eq : forall {F V} (d1 d2: option (globdef (AST.fundef F) V)),
      def_eq d1 d2 -> get_def_init_data d1 = get_def_init_data d2.
Proof.
  intros F V d1 d2 EQ. inv EQ.
  - simpl. auto.
  - simpl in *. rewrite H1. auto.
Qed.

Lemma get_def_instrs_eq : forall d1 d2,
      def_eq d1 d2 -> get_def_instrs d1 = get_def_instrs d2.
Proof.
  intros d1 d2 EQ. inv EQ.
  - auto.
  - simpl in *. auto.
Qed.

Lemma extern_var_init_data_nil : forall {F V} (v:globvar V),
    is_var_internal v = false ->
    @get_def_init_data F _ (Some (Gvar v)) = [].
Proof.
  intros F V v H. simpl in *.
  unfold is_var_internal in H.
  destruct (gvar_init v); try congruence.
  destruct i; simpl in *; try congruence.
  destruct l; simpl in *; try congruence.
Qed.

Lemma extern_init_data_nil : forall {F V} (def: option (globdef (AST.fundef F) V)),
    def_internal def = false -> get_def_init_data def = nil.
Proof.
  intros F V def H.
  destruct def. destruct g. 
  - simpl in *. auto.
  - simpl in H. apply extern_var_init_data_nil. auto.
  - simpl in *. auto.
Qed.

Lemma extern_fun_nil : forall def,
    def_internal def = false -> get_def_instrs def = nil.
Proof.
  intros def H.
  destruct def. destruct g; simpl in *.
  - unfold is_fundef_internal in H.
    destruct f; try congruence.
  - auto.
  - simpl in *. auto.
Qed.

Lemma PTree_combine_ids_defs_match_instrs_data_eq: 
  forall defs1 defs2 t1 t2,
    (forall id def, In (id, def) defs1 -> t1 ! id = Some def) ->
    PTree_combine_ids_defs_match 
      t1 t2 link_prog_merge
      (map fst (filter_internal_defs is_fundef_internal defs1))
      defs2 ->
    fold_right acc_instrs [] defs1 = fold_right acc_instrs [] defs2 /\
    fold_right acc_init_data [] defs1 = fold_right acc_init_data [] defs2.
Proof.
  induction defs1 as [|def1 defs1].
  - cbn. intros defs2 t1 t2 IN MATCH.
    inv MATCH. cbn. auto.
  - intros defs2 t1 t2 IN MATCH.
    destruct def1 as (id, def1). cbn in MATCH.
    destr_in MATCH; cbn in MATCH.
    + inv MATCH.
      destruct y. destruct H1; subst.
      cbn.
      assert (t1 ! p = Some def1). 
      { eapply IN; eauto. apply in_eq. }
      rewrite H in H0. 
      generalize (link_merge_internal_external_defs _ _ _ Heqb H0).
      intros DEFEQ.
      assert (forall id def, In (id, def) defs1 -> t1 ! id = Some def) as IN'.
      { intros. eapply IN; eauto. apply in_cons. auto. }
      generalize (IHdefs1 _ _ _ IN' H3).
      intros (DEQ & CEQ). rewrite DEQ, CEQ. 
      setoid_rewrite (get_def_init_data_eq DEFEQ).
      rewrite (get_def_instrs_eq DEFEQ).
      auto.
    + cbn.
      setoid_rewrite extern_init_data_nil; auto. cbn.
      rewrite extern_fun_nil; auto. cbn.
      eapply IHdefs1; eauto.
      intros. eapply IN; eauto. apply in_cons. auto.
Qed.


(** Data section generation and linking *)

Lemma acc_init_data_eq: forall d1 d2 l,
    id_def_eq d1 d2 -> acc_init_data d1 l = acc_init_data d2 l.
Proof.
  intros d1 d2 l EQ.
  destruct d1, d2. simpl in *. destruct EQ. subst.
  f_equal. apply get_def_init_data_eq. auto.
Qed.

Lemma acc_init_data_in_order_eq : forall defs1 defs2,
    list_in_order id_def_eq id_def_internal defs1 defs2 ->
    fold_right acc_init_data [] defs1 = fold_right acc_init_data [] defs2.
Proof.
  induction 1.
  - simpl. auto.
  - destruct e as (id, def). simpl.     
    setoid_rewrite extern_init_data_nil; eauto.
  - destruct e as (id, def). simpl.
    setoid_rewrite extern_init_data_nil; eauto.
  - simpl.
    rewrite IHlist_in_order. auto.
    apply acc_init_data_eq; auto.
Qed.          

Lemma ext_defs_data_nil: forall (defs: list (ident * option gdef)),
    Forall (fun '(_, def) => is_def_internal is_fundef_internal def = false) defs ->
    fold_right acc_init_data [] defs = nil.
Proof.
  induction defs as [| def defs].
  - cbn. auto.
  - intros H. 
    cbn. unfold acc_init_data. destruct def.
    inv H.
    setoid_rewrite extern_init_data_nil; eauto. 
Qed.


(** Hint for Asm definitions *)                
Definition PERIdAsmDefEq := (@PERIdDefEq Asm.function unit).
Existing Instance PERIdAsmDefEq.
Definition IdAsmDefEq := (@IdDefEq Asm.function unit).
Existing Instance IdAsmDefEq.



(** Code section generation and linking *)

Lemma acc_instrs_eq: forall d1 d2 l,
    id_def_eq d1 d2 -> acc_instrs d1 l = acc_instrs d2 l.
Proof.
  intros d1 d2 l EQ.
  destruct d1, d2. simpl in *. destruct EQ. subst.
  f_equal. apply get_def_instrs_eq. auto.
Qed.

Lemma acc_instrs_in_order_eq : forall defs1 defs2,
    list_in_order id_def_eq id_def_internal defs1 defs2 ->
    fold_right acc_instrs [] defs1 = fold_right acc_instrs [] defs2.
Proof.
  induction 1.
  - simpl. auto.
  - destruct e as (id, def). simpl.     
    erewrite extern_fun_nil; eauto.
  - destruct e as (id, def). simpl.
    erewrite extern_fun_nil; eauto.
  - simpl.
    rewrite IHlist_in_order.
    apply acc_instrs_eq; auto.
Qed.

Lemma ext_defs_code_nil: forall (defs: list (ident * option gdef)),
    Forall (fun '(_, def) => is_def_internal is_fundef_internal def = false) defs ->
    fold_right acc_instrs [] defs = nil.
Proof.
  induction defs as [| def defs].
  - cbn. auto.
  - intros H.
    cbn. unfold acc_instrs. destruct def.
    inv H.
    erewrite extern_fun_nil; eauto. 
Qed.


Lemma link_acc_instrs_data_comm : forall p1 p2 p,
    link_prog_ordered is_fundef_internal p1 p2 = Some p ->
    fold_right acc_instrs [] (AST.prog_defs p) =
    fold_right acc_instrs [] (AST.prog_defs p1) ++ fold_right acc_instrs [] (AST.prog_defs p2) 
    /\
    fold_right acc_init_data [] (AST.prog_defs p) =
    fold_right acc_init_data [] (AST.prog_defs p1) ++ fold_right acc_init_data [] (AST.prog_defs p2).
Proof.
  intros p1 p2 p LINK.
  unfold link_prog_ordered in LINK.
  destr_in LINK. destr_in LINK. destruct p0. inv LINK.
  repeat rewrite andb_true_iff in Heqb.
  destruct Heqb as [[[MAINIDEQ NORPT1] NORPT2] CHK].
  apply proj_sumbool_true in MAINIDEQ.
  apply proj_sumbool_true in NORPT1.
  apply proj_sumbool_true in NORPT2.
  cbn.
  generalize (PTree_extract_elements_combine_match 
                _ _ _ _ _ _ 
                link_prog_merge_none
                Heqo).
  intros MATCH.
  eapply PTree_combine_ids_defs_match_app_inv in MATCH; eauto.
  destruct MATCH as (defs1 & defs2 & EQ & MATCH1 & MATCH2). subst.
  generalize (PTree_extract_elements_combine_match 
                _ _ _ _ _ _ 
                link_prog_merge_none
                Heqo).
  intros MATCH.
  generalize (PTree_extract_elements_remain_external' _ _ _ NORPT1 NORPT2 Heqo).
  intros EXTNS.
  generalize (ext_defs_code_nil EXTNS). intros CN.
  generalize (ext_defs_data_nil EXTNS). intros DN.
  rewrite fold_right_acc_instrs_app.
  rewrite fold_right_acc_instrs_app.
  rewrite fold_right_acc_init_data_app.
  rewrite fold_right_acc_init_data_app.
  rewrite CN, DN. cbn.

  assert (fold_right acc_instrs [] (AST.prog_defs p1) = 
          fold_right acc_instrs [] defs1 /\
          fold_right acc_init_data [] (AST.prog_defs p1) = 
          fold_right acc_init_data [] defs1) as EQ1.
  {
    eapply PTree_combine_ids_defs_match_instrs_data_eq; eauto.
    intros id def IN.
    eapply prog_option_defmap_norepet; eauto.
  }
  destruct EQ1 as (IEQ1 & DEQ1).
  rewrite IEQ1, DEQ1.

  apply PTree_combine_ids_defs_match_symm in MATCH2; auto.
  assert (fold_right acc_instrs [] (AST.prog_defs p2) = 
          fold_right acc_instrs [] defs2 /\
          fold_right acc_init_data [] (AST.prog_defs p2) = 
          fold_right acc_init_data [] defs2) as EQ2.
  { eapply PTree_combine_ids_defs_match_instrs_data_eq; eauto.
    intros id def IN.
    eapply prog_option_defmap_norepet; eauto.
  }
  destruct EQ2 as (IEQ2 & DEQ2).
  rewrite IEQ2, DEQ2.
  split; auto.
Qed.

Lemma link_acc_init_data_comm : forall p1 p2 p,
    link_prog_ordered is_fundef_internal p1 p2 = Some p ->
    fold_right acc_init_data [] (AST.prog_defs p) =
    fold_right acc_init_data [] (AST.prog_defs p1) ++ fold_right acc_init_data [] (AST.prog_defs p2).
Proof.
  intros.
  apply link_acc_instrs_data_comm in H. tauto.
Qed.

Lemma link_acc_instrs_comm : forall p1 p2 p,
    link_prog_ordered is_fundef_internal p1 p2 = Some p ->
    fold_right acc_instrs [] (AST.prog_defs p) =
    (fold_right acc_instrs [] (AST.prog_defs p1)) ++ (fold_right acc_instrs [] (AST.prog_defs p2)).
Proof.
  intros.
  apply link_acc_instrs_data_comm in H. tauto.
Qed.


(** ** Commutativity of linking and generation of the symbol table *)

Lemma reloc_symbentry_exists: forall e dsz csz,
  symbentry_index_in_range [sec_data_id; sec_code_id] e ->
  exists e', reloc_symbol (reloc_offset_fun dsz csz) e = Some e'.
Proof.
  intros e dsz csz IN.
  red in IN. unfold reloc_symbol.
  destruct (symbentry_secindex e); eauto.
  cbn in IN.
  unfold reloc_offset_fun.
  destruct IN as [IN|IN].
  - rewrite IN. destruct N.eq_dec; try congruence. subst.
    eauto.
  - destruct IN as [IN|IN]; try contradiction. subst.
    destruct N.eq_dec. inv e0.
    destruct N.eq_dec; try congruence. subst.
    eauto.
Qed.

Lemma reloc_symbtable_exists_aux : forall stbl f dsz csz,
    symbtable_indexes_in_range [sec_data_id; sec_code_id] stbl ->
    f = (reloc_offset_fun dsz csz) ->
    exists stbl', reloc_symbtable f stbl = Some stbl' /\
             Forall2 (fun e1 e2 => reloc_symbol f e1 = Some e2) stbl stbl'.
Proof.
  induction stbl as [|e stbl].
  - intros f dsz csz INRNG eq. subst.
    cbn. eexists; eauto.
  - intros f dsz csz INRNG eq. subst.
    inv INRNG.
    generalize (IHstbl _ dsz csz H2 eq_refl).
    destruct 1 as (stbl' & RELOC & INRNG').
    unfold reloc_symbtable.
    cbn. setoid_rewrite RELOC.
    unfold reloc_iter.
    generalize (reloc_symbentry_exists _ dsz csz H1).
    destruct 1 as (e' & RELOC').
    rewrite RELOC'. eexists; split; eauto.
Qed.

Lemma reloc_symbtable_exists: forall stbl f defs d c dsz csz,
    gen_symb_table sec_data_id sec_code_id defs = (stbl, d, c) ->
    f = (reloc_offset_fun dsz csz) ->
    exists stbl', reloc_symbtable f stbl = Some stbl' /\
             Forall2 (fun e1 e2 => reloc_symbol f e1 = Some e2) stbl stbl'.
Proof.
  intros. apply reloc_symbtable_exists_aux with dsz csz.
  eapply gen_symb_table_index_in_range; eauto.
  auto.
Qed.

Lemma update_code_data_size_external_size_inv : forall def1 dsz1 csz1 dsz1' csz1',
    is_def_internal is_fundef_internal def1 = false ->
    update_code_data_size dsz1 csz1 def1 = (dsz1', csz1') ->
    dsz1' = dsz1 /\ csz1' = csz1.
Proof.
  intros def1 dsz1 csz1 dsz1' csz1' INT UPDATE.
  destruct def1. destruct g. destruct f.
  - simpl in *. congruence.
  - simpl in *. inv UPDATE. auto.
  - simpl in INT.
    unfold is_var_internal in INT.
    unfold update_code_data_size in UPDATE.
    destruct (gvar_init v).
    + simpl in *. inv UPDATE. auto.
    + destruct i; try (simpl in INT; congruence).
      simpl in INT. destruct l.
      * inv UPDATE. auto.
      * congruence.
  - simpl in *. inv UPDATE. auto.
Qed.

Lemma update_code_data_size_external_ignore_size : forall def1 dsz1 csz1,
    is_def_internal is_fundef_internal def1 = false ->
    update_code_data_size dsz1 csz1 def1 = (dsz1, csz1).
Proof.
  intros def1 dsz1 csz1 INT.
  destruct def1. destruct g.
  destruct f; cbn in INT; try congruence.
  - cbn. auto.
  - cbn in INT.
    unfold update_code_data_size.
    unfold is_var_internal in INT.
    destruct (gvar_init v); cbn in INT; try congruence.
    destruct i; cbn in INT; try congruence.
    destruct l; cbn in INT; try congruence.
  - cbn. auto.
Qed.

Lemma get_extern_symbentry_ignore_size: forall did cid id def dsz1 csz1 dsz2 csz2,
    is_def_internal is_fundef_internal def = false ->
    get_symbentry did cid dsz1 csz1 id def =
    get_symbentry did cid dsz2 csz2 id def.
Proof.
  intros until csz2. intros INT.
  destruct def. destruct g. destruct f.
  - cbn in *. congruence.
  - cbn in *. auto.
  - cbn in *. unfold is_var_internal in INT.
    destruct (gvar_init v); cbn in *; auto.
    destruct i; try congruence.
    destruct l; auto.
    congruence.
  - cbn in *. auto.
Qed.


(* Lemma acc_symb_partition_extern_intern: forall asf id defs defs1 defs2 rstbl dsz1 csz1 dsz2 csz2, *)
(*     asf = acc_symb sec_data_id sec_code_id -> *)
(*     partition (fun '(id', _) => ident_eq id' id) defs = (defs1, defs2) -> *)
(*     fold_left asf defs ([], dsz1, csz1) = (rstbl, dsz2, csz2) -> *)
(*     Forall (fun '(id', def) => is_def_internal is_fundef_internal def = false) defs1 -> *)
(*     exists stbl1 stbl2, *)
(*       partition (symbentry_id_eq id) (rev rstbl) = (stbl1, stbl2) /\ *)
(*       fold_left asf defs1 ([], 0, 0) = (rev stbl1, 0, 0) /\ *)
(*       fold_left asf defs2 ([], dsz1, csz1) = (rev stbl2, dsz2, csz2). *)
(* Proof. *)
(*   induction defs as [|def defs]. *)
(*   - intros until csz2. *)
(*     intros ASF PART ACC EXT. *)
(*     simpl in *. inv PART. inv ACC. simpl. *)
(*     eauto. *)
(*   - intros until csz2. *)
(*     intros ASF PART ACC EXT. *)
(*     simpl in *. destr_in PART. destruct def as (id' & def). *)
(*     destruct ident_eq; subst. *)
(*     + simpl in *. destr_in ACC. inv PART. *)
(*       generalize (acc_symb_inv _ _ _ _ eq_refl ACC). *)
(*       destruct 1 as (rstbl' & EQ & ACC'). subst. *)
(*       inv EXT. *)
(*       generalize (IHdefs _ _ _ _ _ _ _ eq_refl eq_refl ACC' H2). *)
(*       destruct 1 as (stbl1' & stbl2' & PART' & ACC'' & ACC'''). *)
(*       rewrite rev_unit. simpl. *)
(*       rewrite PART'. *)
(*       unfold symbentry_id_eq. rewrite get_symbentry_id. *)
(*       rewrite dec_eq_true. *)
(*       do 2 eexists; split; auto.  *)
(*       generalize (update_code_data_size_external_size_inv _ _ _ H1 Heqp0). *)
(*       destruct 1; subst.  *)
(*       split; auto. *)
(*       generalize (update_code_data_size_external_ignore_size def 0 0 H1). *)
(*       intros UPDATE'. rewrite UPDATE'. *)
(*       simpl.  *)
(*       rewrite (get_extern_symbentry_ignore_size _ _ id def dsz1 csz1 0 0); auto. *)
(*       apply acc_symb_append_nil. auto. *)
(*     + simpl in *. destr_in ACC. inv PART. *)
(*       generalize (acc_symb_inv _ _ _ _ eq_refl ACC). *)
(*       destruct 1 as (rstbl' & EQ & ACC'). subst. *)
(*       generalize (IHdefs _ _ _ _ _ _ _ eq_refl eq_refl ACC' EXT). *)
(*       destruct 1 as (stbl1' & stbl2' & PART' & ACC'' & ACC'''). *)
(*       rewrite rev_unit. simpl. *)
(*       rewrite PART'. *)
(*       unfold symbentry_id_eq. rewrite get_symbentry_id. *)
(*       rewrite dec_eq_false; auto. *)
(*       do 2 eexists; split; auto. *)
(*       rewrite Heqp0.  *)
(*       split; auto. *)
(*       apply acc_symb_append_nil. auto. *)
(* Qed. *)
      
      
Definition match_def_symbentry (id_def: ident * option gdef) e :=
  let '(id, def) := id_def in
  exists dsz csz, e = get_symbentry sec_data_id sec_code_id dsz csz id def.
    
(* Lemma acc_symb_pres_partition: forall asf id defs defs1 defs2 rstbl dsz1 csz1 dsz2 csz2, *)
(*     asf = acc_symb sec_data_id sec_code_id -> *)
(*     partition (fun '(id', _) => ident_eq id' id) defs = (defs1, defs2) -> *)
(*     fold_left asf defs ([], dsz1, csz1) = (rstbl, dsz2, csz2) -> *)
(*     exists stbl1 stbl2, *)
(*       partition (symbentry_id_eq id) (rev rstbl) = (stbl1, stbl2) /\ *)
(*       Forall2 match_def_symbentry defs1 stbl1  /\ *)
(*       Forall2 match_def_symbentry defs2 stbl2. *)
(* Proof. *)
(*   induction defs as [|def defs]. *)
(*   - intros until csz2.  *)
(*     intros ASF PART ACC. *)
(*     simpl in *. inv PART. inv ACC. simpl. eauto. *)
(*   - intros until csz2. *)
(*     intros ASF PART ACC. subst. *)
(*     simpl in *. *)
(*     destruct def as (id', def). *)
(*     destr_in PART. destr_in ACC. *)
(*     generalize (acc_symb_inv _ _ _ _ eq_refl ACC). *)
(*     destruct 1 as (rstbl' & EQ & ACC'). subst. *)
(*     destruct ident_eq; inv PART; simpl in *. *)
(*     + rewrite rev_unit. *)
(*       generalize (IHdefs _ _ _ _ _ _ _ eq_refl eq_refl ACC'). *)
(*       destruct 1 as (stbl1' & stbl2' & PART' & MATCH1 & MATCH2). *)
(*       simpl. rewrite PART'. *)
(*       unfold symbentry_id_eq.  *)
(*       rewrite get_symbentry_id.  *)
(*       rewrite dec_eq_true. *)
(*       do 2 eexists; split; eauto. *)
(*       split; auto. *)
(*       constructor; auto. *)
(*       red. eauto. *)
(*     + rewrite rev_unit. *)
(*       generalize (IHdefs _ _ _ _ _ _ _ eq_refl eq_refl ACC'). *)
(*       destruct 1 as (stbl1' & stbl2' & PART' & MATCH1 & MATCH2). *)
(*       simpl. rewrite PART'. *)
(*       unfold symbentry_id_eq.  *)
(*       rewrite get_symbentry_id.  *)
(*       rewrite dec_eq_false; auto. *)
(*       do 2 eexists; split; eauto. *)
(*       split; auto. *)
(*       constructor; auto. *)
(*       red. eauto. *)
(* Qed.       *)


Lemma match_def_symbentry_pres_internal_prop : forall id def e,
    match_def_symbentry (id, def) e ->
    is_def_internal is_fundef_internal def = is_symbentry_internal e.
Proof.
  intros id def e MATCH.
  red in MATCH. destruct MATCH as (dsz & csz & SYMB). subst.
  apply get_symbentry_pres_internal_prop.
Qed.


Lemma get_extfun_entry_secindex : forall did cid dsz1 csz1 id f,
    is_fundef_internal f = false 
    -> symbentry_secindex (get_symbentry did cid dsz1 csz1 id (Some (Gfun f))) = secindex_undef.
Proof.
  intros. cbn. auto.
  destruct f.
  cbn in *. congruence.
  simpl. auto.
Qed.

Lemma get_comm_var_entry_secindex:
  forall did cid (dsz1 csz1 : Z) (id : ident) v,
  is_var_comm v = true 
  -> symbentry_secindex
      (get_symbentry did cid dsz1 csz1 id
                         (Some (Gvar v))) = secindex_comm.
Proof.
  intros. subst. cbn. 
  unfold is_var_comm in H.
  destruct (gvar_init v); cbn in H; try congruence.
  cbn. auto.
  destruct i; cbn in H; try congruence.
  destruct l; cbn in H; try congruence.
  cbn. auto.
Qed.

Lemma get_extern_var_entry_secindex:
  forall did cid (dsz1 csz1 : Z) (id : ident) v,
  is_var_extern v = true 
  -> symbentry_secindex
          (get_symbentry did cid dsz1 csz1 id
                         (Some (Gvar v))) = secindex_undef.
Proof.
  intros. subst. cbn. 
  unfold is_var_extern in H.
  destruct (gvar_init v); cbn in H; try congruence.
  cbn. auto.
  destruct i; cbn in H; try congruence.
  destruct l; cbn in H; try congruence.
Qed.


Lemma get_intvar_entry_secindex:
  forall did cid (dsz1 csz1 : Z) (id : ident) v,
  is_var_internal v = true 
  -> symbentry_secindex
          (get_symbentry did cid dsz1 csz1 id
                         (Some (Gvar v))) = 
    (secindex_normal did).
Proof.
  intros. cbn.
  unfold is_var_internal in H.
  destruct (gvar_init v); cbn in H; try congruence.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
Qed.


Lemma update_symbtype_unchanged: forall e t,
    symbentry_type e = t -> update_symbtype e t = e.
Proof.
  intros. destruct e. cbn in *.
  unfold update_symbtype. cbn. rewrite H. auto.
Qed.

Lemma link_get_symbentry_left_some_right_none_comm: forall did cid def id dsz1 dsz2 csz1 csz2,
    link_symb (get_symbentry did cid dsz1 csz1 id (Some def))
              (get_symbentry did cid dsz2 csz2 id None) = 
    Some (get_symbentry did cid dsz1 csz1 id (Some def)).
Proof.
  intros until csz2.
  destruct def. destruct f.
  - cbn. unfold link_symb. cbn. rewrite peq_true. auto.
  - cbn. unfold link_symb. cbn. rewrite peq_true. auto.
  - unfold link_symb.
    repeat rewrite get_symbentry_id.
    rewrite peq_true.
    rewrite get_var_entry_type.
    rewrite get_none_entry_type.
    replace (link_symbtype symb_data symb_notype) with (Some symb_data) by auto.
    rewrite get_none_entry_secindex.
    cbn. 
    destruct (gvar_init v); cbn; try congruence.
    destruct i; cbn; try congruence.
    destruct l; cbn; try congruence.
Qed.      


Lemma link_get_symbentry_right_none_comm: forall did cid def1 def id dsz1 dsz2 csz1 csz2,
    link_option def1 None = Some def 
    -> link_symb (get_symbentry did cid dsz1 csz1 id def1)
                (get_symbentry did cid dsz2 csz2 id None) = 
      Some (get_symbentry did cid dsz1 csz1 id def).
Proof.
  intros until csz2.
  intros LINK.
  unfold link_option in LINK.
  destruct def1 as [def1|].
  - inv LINK.    
    eapply link_get_symbentry_left_some_right_none_comm; eauto.
  - inv LINK. cbn. auto.
    unfold link_symb; cbn. rewrite peq_true. auto.
Qed.

Lemma link_get_symbentry_right_extfundef_comm: forall did cid id f1 f2 f dsz1 csz1 dsz2 csz2,
    is_fundef_internal f2 = false
    -> link_fundef f1 f2 = Some f
    -> link_symb
        (get_symbentry did cid dsz1 csz1 id
                       (Some (Gfun f1)))
        (get_symbentry did cid dsz2 csz2 id
                       (Some (Gfun f2))) =
      Some (get_symbentry did cid dsz1 csz1 id
                          (Some (Gfun f))).
Proof.
  intros until csz2.
  intros INT LINK.
  unfold link_symb.
  repeat rewrite get_symbentry_id. cbn.
  rewrite peq_true.
  destruct f1, f2, f; cbn in *; try congruence.
  destruct e; inv LINK; try congruence.
  destruct e; inv LINK; try congruence.
  destruct external_function_eq; subst; cbn; inv LINK.
Qed.

Lemma link_getsymbentry_right_extfun : forall did cid id def1 def f dsz1 csz1 dsz2 csz2,
    is_fundef_internal f = false
    -> link_option def1 (Some (Gfun f)) = Some def
    -> link_symb
        (get_symbentry did cid dsz1 csz1 id def1)
        (get_symbentry did cid dsz2 csz2 id (Some (Gfun f))) =
      Some (get_symbentry did cid dsz1 csz1 id def).
Proof.
  intros until csz2.
  intros INT LINK.
  destruct def1 as [def1|].
  - inv LINK.
    destr_in H0; try congruence. inv H0.
    destruct def1; try (cbn in *; congruence).
    simpl in Heqo. destr_in Heqo; try congruence.
    inv Heqo.
    apply link_get_symbentry_right_extfundef_comm; auto.    
  - inv LINK. 
    unfold link_symb.   
    rewrite get_fun_entry_type.
    rewrite get_none_entry_type.
    replace (link_symbtype symb_notype symb_func) with (Some symb_func) by auto.
    rewrite get_none_entry_secindex.
    rewrite get_extfun_entry_secindex; auto.
    unfold update_symbtype. cbn. 
    destruct f. cbn in *; congruence. auto.
    cbn. rewrite peq_true. auto.
Qed.


Lemma link_get_symbentry_extvars_init_comm :
  forall did cid v1 v2 id dsz1 csz1 dsz2 csz2 (inf:unit) init rd vl,
    is_var_internal v1 = false 
    -> is_var_internal v2 = false 
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some init
    -> link_symb
        (get_symbentry did cid dsz1 csz1 id
                       (Some (Gvar v1)))
        (get_symbentry did cid dsz2 csz2 id
                       (Some (Gvar v2))) =
      Some
        (get_symbentry did cid dsz1 csz1 id
                       (Some (Gvar (mkglobvar inf init rd vl)))).
Proof.
  intros until vl.
  intros INT1 INT2 LINK.
  rewrite var_not_internal_iff in INT1, INT2.
  destruct INT1 as [INT1|INT1]; destruct INT2 as [INT2|INT2].
  - generalize (link_comm_vars_init _ _ INT1 INT2 LINK).
    destruct 1 as (EQ & INIT). subst.
    repeat (rewrite get_comm_var_entry; auto).
    cbn. unfold link_symb; cbn. rewrite peq_true.
    rewrite EQ.
    destruct zeq; try congruence.
    erewrite Zmax_left; auto.
    apply Z.le_ge. apply Z.le_max_r.
  - generalize (link_comm_extern_var_init _ _ INT1 INT2 LINK).
    intros. subst.
    rewrite (get_comm_var_entry _ _ _ _ _ _ INT1).
    rewrite (get_external_var_entry _ _ _ _ _ _ INT2).
    rewrite get_comm_var_entry; cbn; auto.
    unfold link_symb; cbn.
    rewrite peq_true. auto.
  - generalize (link_extern_comm_var_init _ _ INT1 INT2 LINK).
    intros. subst.
    rewrite (get_comm_var_entry _ _ _ _ _ _ INT2).
    rewrite (get_external_var_entry _ _ _ _ _ _ INT1).
    rewrite get_comm_var_entry; auto.
    unfold link_symb; cbn.
    cbn. rewrite peq_true. auto.
  - generalize (link_extern_vars_init _ _ INT1 INT2 LINK).
    intros. subst.
    rewrite (get_external_var_entry _ _ _ _ _ _ INT2).
    rewrite (get_external_var_entry _ _ _ _ _ _ INT1).
    rewrite get_external_var_entry; auto.
    unfold link_symb; cbn.
    cbn. rewrite peq_true. auto.
Qed.    
    
Lemma link_get_symbentry_right_extvar_init_comm :
  forall did cid v1 v2 id dsz1 csz1 dsz2 csz2 (inf:unit) init rd vl,
    is_var_internal v2 = false 
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some init
    -> link_symb
        (get_symbentry did cid dsz1 csz1 id
                       (Some (Gvar v1)))
        (get_symbentry did cid dsz2 csz2 id
                       (Some (Gvar v2))) =
      Some
        (get_symbentry did cid dsz1 csz1 id
                       (Some (Gvar (mkglobvar inf init rd vl)))).
Proof.
  intros until vl.
  intros INT LINK.
  destruct (is_var_internal v1) eqn:INT1.
  generalize INT. intros INT'.
  rewrite var_not_internal_iff in INT.
  destruct INT as [INT|INT].
  - generalize (link_internal_comm_varinit _ _ _ INT1 INT LINK).
    destruct 1 as (IEQ & SEQ & CLS1). subst.
    unfold link_symb.
    repeat rewrite get_var_entry_type.
    cbn -[get_symbentry].
    rewrite get_intvar_entry_secindex; auto.
    rewrite get_comm_var_entry_secindex; auto.
    rewrite get_var_entry_size.
    rewrite get_var_entry_size.
    rewrite SEQ.
    repeat rewrite get_symbentry_id. rewrite peq_true.
    apply dec_eq_true. 
  - unfold link_symb.
    repeat rewrite get_var_entry_type.
    cbn -[get_symbentry].
    rewrite get_intvar_entry_secindex; auto.
    rewrite get_extern_var_entry_secindex; auto.
    generalize (link_internal_external_varinit _ _ _ INT1 INT' LINK).
    destruct 1 as (INITEQ & CLS).
    f_equal.
    repeat rewrite get_symbentry_id. rewrite peq_true.
    erewrite get_symbentry_eq_gvar_init; eauto.
  - apply link_get_symbentry_extvars_init_comm; auto.
Qed.
    

Lemma link_getsymbentry_right_extvar : forall did cid id def1 def v dsz1 csz1 dsz2 csz2,
    is_var_internal v = false
    -> link_option def1 (Some (Gvar v)) = Some def
    -> link_symb
        (get_symbentry did cid dsz1 csz1 id def1)
        (get_symbentry did cid dsz2 csz2 id (Some (Gvar v))) =
      Some (get_symbentry did cid dsz1 csz1 id def).
Proof.
  intros until csz2.
  intros INT LINK.
  destruct def1 as [def1|].
  - inv LINK.
    destr_in H0; try congruence. inv H0.
    destruct def1; try (cbn in *; congruence).
    simpl in Heqo. destr_in Heqo; try congruence.
    inv Heqo.
    unfold link_vardef in Heqo0.
    repeat (destr_in Heqo0; try congruence).
    cbn in Heqo1.
    apply link_get_symbentry_right_extvar_init_comm; auto.
  - inv LINK. 
    unfold link_symb.   
    rewrite get_var_entry_type.
    rewrite get_none_entry_type.
    replace (link_symbtype symb_notype symb_data) with (Some symb_data) by auto.
    rewrite get_none_entry_secindex.
    rewrite var_not_internal_iff in INT. 
    destruct INT as [INT|INT].
    + rewrite get_comm_var_entry_secindex; auto.
      repeat rewrite get_symbentry_id. rewrite peq_true.
      f_equal. apply get_extern_symbentry_ignore_size.
      cbn. rewrite var_not_internal_iff. auto.
    + rewrite get_extern_var_entry_secindex; auto.
      repeat rewrite get_symbentry_id. rewrite peq_true.
      f_equal.
      generalize (extern_var_init_nil v INT).
      intros IL. 
      cbn. rewrite IL. 
      unfold update_symbtype. cbn. auto.
Qed.

Lemma link_get_symbentry_comm2: forall did cid def1 def2 def id dsz1 dsz2 csz1 csz2,
    is_def_internal is_fundef_internal def2 = false ->
    link_option def1 def2 = Some def 
    -> link_symb (get_symbentry did cid dsz1 csz1 id def1)
                (get_symbentry did cid dsz2 csz2 id def2) = 
      Some (get_symbentry did cid dsz1 csz1 id def).
Proof.
  intros until csz2.
  intros INT LINK.
  destruct def2 as [def2|].
  - cbn in INT. destruct def2.
    + apply link_getsymbentry_right_extfun; auto.
    + apply link_getsymbentry_right_extvar; auto.
  - apply link_get_symbentry_right_none_comm. auto.
Qed.

Lemma link_get_symbentry_comm1: forall did cid def1 def2 def id dsz1 dsz2 csz1 csz2,
    is_def_internal is_fundef_internal def1 = false ->
    link_option def1 def2 = Some def 
    -> link_symb (get_symbentry did cid dsz1 csz1 id def1)
                (get_symbentry did cid dsz2 csz2 id def2) = 
      Some (get_symbentry did cid dsz2 csz2 id def).
Proof.
  intros until csz2.
  intros DEFINT LINK.
  rewrite link_option_symm in LINK.
  rewrite link_symb_symm.
  apply link_get_symbentry_comm2; auto.
  intros. apply link_unit_symm.
Qed.

Lemma link_none_update_code_data_size: forall def1 def dsz1 csz1,
    link_option def1 None = Some def
    -> update_code_data_size dsz1 csz1 def1 = update_code_data_size dsz1 csz1 def.
Proof.
  intros until csz1.
  intros LINK.
  unfold link_option in LINK.
  destruct def1 as [def1|].
  - inv LINK. auto.
  - inv LINK. auto.
Qed.

Lemma link_update_size_extvars_init_comm :
  forall v1 (v2:globvar unit) dsz1 csz1 (inf:unit) init rd vl,
    is_var_internal v1 = false 
    -> is_var_internal v2 = false 
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some init
    -> update_code_data_size dsz1 csz1 (Some (Gvar v1)) =
      update_code_data_size dsz1 csz1
                            (Some (Gvar (mkglobvar inf init rd vl))).
Proof.
  intros until vl.
  intros INT1 INT2 LINK.
  rewrite update_code_data_size_external_ignore_size; auto.
  rewrite update_code_data_size_external_ignore_size; auto.
  cbn.
  generalize (link_external_varinit _ _ _ INT1 INT2 LINK).
  intros.
  unfold is_var_internal. cbn.
  destruct (classify_init init); congruence.
Qed.    


Lemma link_update_size_right_extvar_init_comm :
  forall v1 (v2: globvar unit) dsz1 csz1 (inf:unit) init rd vl,
    is_var_internal v2 = false 
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some init
    -> update_code_data_size dsz1 csz1 (Some (Gvar v1)) =
      update_code_data_size dsz1 csz1 (Some (Gvar (mkglobvar inf init rd vl))).
Proof.
  intros until vl.
  intros INT LINK.
  destruct (is_var_internal v1) eqn:INT1.
  generalize INT. intros INT'.
  rewrite var_not_internal_iff in INT.
  destruct INT as [INT|INT].
  - generalize (link_internal_comm_varinit _ _ _ INT1 INT LINK).
    destruct 1 as (IEQ & SEQ & CLS1). subst.
    auto.
  - generalize (link_internal_external_varinit _ _ _ INT1 INT' LINK).
    destruct 1 as (INITEQ & CLS). subst.
    auto.
  - apply link_update_size_extvars_init_comm with v2; auto.
Qed.


Lemma link_extern_vardef_update_code_data_size: forall def1 v def dsz1 csz1,
        is_var_internal v = false
        -> link_option def1 (Some (Gvar v)) = Some def
        -> update_code_data_size dsz1 csz1 def1 = update_code_data_size dsz1 csz1 def.
Proof.
  intros until csz1.
  intros INT LINK.
  destruct def1 as [def1|].
  - cbn in LINK.
    destr_in LINK; try congruence. inv LINK.
    destruct def1; try (cbn in *; congruence).
    simpl in Heqo. destr_in Heqo; try congruence.
    inv Heqo.
    unfold link_vardef in Heqo0.
    repeat (destr_in Heqo0; try congruence).
    cbn in Heqo1.
    apply link_update_size_right_extvar_init_comm with v; auto.
  - cbn in LINK. inv LINK.
    rewrite (update_code_data_size_external_ignore_size (Some (Gvar v))).
    simpl. auto.
    cbn. auto.
Qed.
  
Lemma link_update_size_right_extfun_comm :
  forall f1 f2 f dsz1 csz1,
    is_fundef_internal f2 = false 
    -> link_fundef f1 f2 = Some f
    -> update_code_data_size dsz1 csz1 (Some (Gfun f1)) =
       update_code_data_size dsz1 csz1 (Some (Gfun f)).
Proof.
  intros until csz1.
  intros INT LINK.
  destruct f2; try (cbn in INT; congruence).
  apply link_fundef_inv1 in LINK. subst.
  auto.
Qed.
  

Lemma link_extern_fundef_update_code_data_size: forall def1 f def dsz1 csz1,
        is_fundef_internal f = false
        -> link_option def1 (Some (Gfun f)) = Some def
        -> update_code_data_size dsz1 csz1 def1 = update_code_data_size dsz1 csz1 def.
Proof.
  intros until csz1.
  intros INT LINK.
  destruct def1 as [def1|].
  - cbn in LINK.
    destr_in LINK; try congruence. inv LINK.
    destruct def1; try (cbn in *; congruence).
    simpl in Heqo. destr_in Heqo; try congruence.
    inv Heqo.
    apply link_update_size_right_extfun_comm with f; auto.    
  - cbn in LINK.  inv LINK.
    rewrite (update_code_data_size_external_ignore_size (Some (Gfun f))).
    simpl. auto.
    cbn. auto.
Qed.


Lemma link_extern_def_update_code_data_size: forall def1 def2 def dsz1 csz1,
    is_def_internal is_fundef_internal def2 = false
    -> link_option def1 def2 = Some def
    -> update_code_data_size dsz1 csz1 def1 = update_code_data_size dsz1 csz1 def.
Proof.
  intros until csz1.
  intros INT LINK.
  destruct def2 as [def2|].
  - cbn in INT. destruct def2.
    + apply link_extern_fundef_update_code_data_size with f; auto.
    + apply link_extern_vardef_update_code_data_size with v; auto.
  - apply link_none_update_code_data_size. auto.
Qed.


Lemma partition_reloc_symbtable_comm : forall f l l1 l2 rf l',
    (forall e e', reloc_symbol rf e = Some e' -> f e = f e') 
    -> partition f l = (l1, l2)
    -> reloc_symbtable rf l = Some l'
    -> exists l1' l2', partition f l' = (l1', l2') 
                 /\ reloc_symbtable rf l1 = Some l1'
                 /\ reloc_symbtable rf l2 = Some l2'.
Proof.
  induction l as [| e l].
  - intros l1 l2 rf l' PRES PART RELOC.
    cbn in *. inv PART. inv RELOC.
    exists nil, nil.
    split; auto.
  - intros l1 l2 rf l' PRES PART RELOC.
    cbn in *. destr_in PART. destruct (f e) eqn:PEQ.
    + inv PART.
      unfold reloc_iter in RELOC. 
      destr_in RELOC; try congruence.
      destr_in RELOC; try congruence.
      inv RELOC.
      generalize (IHl _ _ _ _ PRES eq_refl Heqo).
      destruct 1 as (l1' & l2' & PART' & RELOC1 & RELOC2).
      exists (s :: l1'), l2'. 
      erewrite PRES in PEQ; eauto.
      cbn. rewrite PEQ. rewrite PART'.
      split; auto.
      split; auto.
      unfold reloc_iter. setoid_rewrite RELOC1.
      rewrite Heqo0. auto.
    + inv PART.
      unfold reloc_iter in RELOC. 
      destr_in RELOC; try congruence.
      destr_in RELOC; try congruence.
      inv RELOC.
      generalize (IHl _ _ _ _ PRES eq_refl Heqo).
      destruct 1 as (l1' & l2' & PART' & RELOC1 & RELOC2).
      exists (l1'), (s ::l2'). 
      erewrite PRES in PEQ; eauto.
      cbn. rewrite PEQ. rewrite PART'.
      split; auto.
      split; auto.
      unfold reloc_iter. setoid_rewrite RELOC2.
      rewrite Heqo0. auto.
Qed.    


Lemma reloc_symb_pres_internal_prop : forall rf s1 s2,
    reloc_symbol rf s1 = Some s2 
    -> is_symbentry_internal s1 = is_symbentry_internal s2.
Proof.
  intros rf s1 s2 RELOC.
  unfold reloc_symbol in RELOC. 
  unfold is_symbentry_internal.
  destr_in RELOC.
  destr_in RELOC.
  inv RELOC. cbn. auto.
  inv RELOC. rewrite Heqs. auto.
  inv RELOC. rewrite Heqs. auto.
Qed.

Lemma reloc_external_symb : forall rf s,
    is_symbentry_internal s = false
    -> reloc_symbol rf s = Some s. 
Proof.
  intros rf s RELOC.
  unfold is_symbentry_internal in RELOC.
  unfold reloc_symbol. destr_in RELOC.
Qed.  

Lemma reloc_symb_pres_id: forall rf e e', 
      reloc_symbol rf e = Some e' -> symbentry_id e = symbentry_id e'.
Proof.
  intros rf e e' RELOC.
  unfold reloc_symbol in RELOC.
  destruct e. cbn in *.
  destruct symbentry_secindex. destruct (rf idx).
  inv RELOC. cbn. auto.
  congruence.
  inv RELOC. cbn. auto.
  inv RELOC. cbn. auto.
Qed.

Lemma reloc_symb_pres_type: forall rf e e', 
      reloc_symbol rf e = Some e' -> symbentry_type e = symbentry_type e'.
Proof.
  intros rf e e' RELOC.
  unfold reloc_symbol in RELOC.
  destruct e. cbn in *.
  destruct symbentry_secindex. destruct (rf idx).
  inv RELOC. cbn. auto.
  congruence.
  inv RELOC. cbn. auto.
  inv RELOC. cbn. auto.
Qed.

Lemma reloc_symb_pres_secindex: forall rf e e', 
      reloc_symbol rf e = Some e' -> symbentry_secindex e = symbentry_secindex e'.
Proof.
  intros rf e e' RELOC.
  unfold reloc_symbol in RELOC.
  destruct e. cbn in *.
  destruct symbentry_secindex. destruct (rf idx).
  inv RELOC. cbn. auto.
  congruence.
  inv RELOC. cbn. auto.
  inv RELOC. cbn. auto.
Qed.

Lemma reloc_symb_pres_size: forall rf e e', 
      reloc_symbol rf e = Some e' -> symbentry_size e = symbentry_size e'.
Proof.
  intros rf e e' RELOC.
  unfold reloc_symbol in RELOC.
  destruct e. cbn in *.
  destruct symbentry_secindex. destruct (rf idx).
  inv RELOC. cbn. auto.
  congruence.
  inv RELOC. cbn. auto.
  inv RELOC. cbn. auto.
Qed.

Lemma reloc_symb_pres_update_symbtype : forall rf e e' t,
    reloc_symbol rf e = Some e' ->
    reloc_symbol rf (update_symbtype e t) = Some (update_symbtype e' t).
Proof.
  intros rf e e' t RELOC.
  destruct e. unfold reloc_symbol in *. cbn in *.
  destr_in RELOC; try congruence; subst.
  destr_in RELOC; try congruence.
  inv RELOC. auto.
Qed.


Lemma reloc_get_symbentry : forall dofs cofs dsz csz id def e,
    reloc_symbol (reloc_offset_fun dofs cofs) (get_symbentry sec_data_id sec_code_id dsz csz id def) = Some e
    -> e = (get_symbentry sec_data_id sec_code_id (dsz + dofs) (csz + cofs) id def).
Proof.
  intros until e. intro RELOC.
  destruct def. destruct g. destruct f.
  - cbn in *. inv RELOC. f_equal.
  - cbn in *. inv RELOC. auto.
  - cbn in *. destr_in RELOC. cbn in *. inv RELOC. auto.
    destruct i; cbn in *; try congruence.
    destruct l; cbn in *; try congruence.
  - cbn in *. inv RELOC. auto.
Qed.

Lemma acc_symb_reloc: forall asf defs stbl stbl' dsz1 dsz2 csz1 csz2 dofs cofs,
    asf = (acc_symb sec_data_id sec_code_id) 
    -> fold_left asf defs ([], dsz1, csz1) = (stbl, dsz2, csz2)
    -> reloc_symbtable (reloc_offset_fun dofs cofs) (rev stbl) = Some stbl'
    -> fold_left asf defs ([], dofs + dsz1, cofs + csz1) = (rev stbl', dofs + dsz2, cofs + csz2).
Proof.
  induction defs as [|def defs].
  - intros until cofs. intros ASF ACC RELOC.
    cbn in *. inv ACC. cbn in RELOC. inv RELOC. auto.
  - intros until cofs. intros ASF ACC RELOC.
    subst. cbn in *. destruct def as [id def].
    destr_in ACC.
    generalize (acc_symb_inv _ _ _ _ _ _ _ _ _ _ eq_refl ACC).
    destruct 1 as (stbl1 & EQ & ACC1). subst.    
    erewrite update_size_offset; eauto.
    rewrite rev_unit in RELOC.
    cbn in RELOC. unfold reloc_iter in RELOC.
    destr_in RELOC; try congruence.
    destr_in RELOC; try congruence.
    inv RELOC.
    generalize (IHdefs _ _ _ _ _ _ _ _ eq_refl ACC1 Heqo).
    intros ACC'.
    generalize (acc_symb_append_nil _ _ _ _ _ _ _ _
                                    [get_symbentry sec_data_id sec_code_id (dofs + dsz1) (cofs + csz1) id def] ACC').
    intros ACC''. setoid_rewrite ACC''.
    cbn. f_equal. f_equal.
    apply reloc_get_symbentry in Heqo0. subst. 
    f_equal. f_equal. f_equal; omega.
Qed.    


Lemma acc_symb_reloc_comm: forall asf defs1 defs2 stbl1 stbl2 stbl2'
                             dsz1 dsz2 csz1 csz2 dsz1' csz1',
    asf = (acc_symb sec_data_id sec_code_id) 
    -> fold_left asf defs1 ([], dsz1, csz1) = (stbl1, dsz1', csz1')
    -> fold_left asf defs2 ([], 0, 0) = (stbl2, dsz2, csz2)
    -> reloc_symbtable (reloc_offset_fun dsz1' csz1') (rev stbl2) = Some stbl2'
    -> fold_left asf (defs1 ++ defs2) ([], dsz1, csz1) = ((rev stbl2') ++ stbl1, dsz1' + dsz2, csz1' + csz2).
Proof.
  induction defs1.
  - intros until csz1'.
    intros ASF ACC1 ACC2 RELOC.
    cbn in *. inv ACC1.
    rewrite app_nil_r.
    erewrite <- acc_symb_reloc; eauto.
    repeat f_equal. omega. omega.
  - intros until csz1'.
    intros ASF ACC1 ACC2 RELOC.
    cbn in *. rewrite ASF in ACC1. unfold acc_symb in ACC1.
    destruct a as [id def]. destr_in ACC1.
    generalize (acc_symb_inv _ _ _ _ _ _ _ _ _ _ eq_refl ACC1).
    destruct 1 as (stbl1' & SEQ & ACC1'). subst.
    generalize (IHdefs1 _ _ _ _ _ _ _ _ _ _ eq_refl ACC1' ACC2 RELOC).
    intros ACC'.
    unfold acc_symb. rewrite Heqp. 
    setoid_rewrite acc_symb_append_nil; eauto.
    rewrite app_assoc. auto.
Qed.
  

(* Lemma gen_symb_table_reloc_comm : forall defs1 defs2 stbl1 stbl2 stbl2' dsz1 dsz2 csz1 csz2, *)
(*     gen_symb_table sec_data_id sec_code_id defs1 = (stbl1, dsz1, csz1) -> *)
(*     gen_symb_table sec_data_id sec_code_id defs2 = (stbl2, dsz2, csz2) -> *)
(*     reloc_symbtable (reloc_offset_fun dsz1 csz1) stbl2 = Some stbl2' -> *)
(*     gen_symb_table sec_data_id sec_code_id (defs1 ++ defs2) = (stbl1 ++ stbl2', dsz1 + dsz2, csz1 + csz2). *)
(* Proof. *)
(*   intros until csz2. *)
(*   intros GS1 GS2 RELOC. *)
(*   unfold gen_symb_table in GS1, GS2. *)
(*   destr_in GS1; inv GS1. *)
(*   destr_in GS2; inv GS2. *)
(*   destruct p, p0. inv H0. inv H1. *)
(*   unfold gen_symb_table. *)
(*   erewrite acc_symb_reloc_comm; eauto. *)
(*   rewrite rev_app_distr. rewrite rev_involutive. *)
(*   auto. *)
(* Qed. *)


  
Lemma reloc_symbtable_cons: forall f e e' stbl1 stbl2,
    reloc_symbtable f stbl1 = Some stbl2 ->
    reloc_symbol f e = Some e' ->
    reloc_symbtable f (e :: stbl1) = Some (e' :: stbl2).
Proof.
  intros. cbn.
  unfold reloc_iter. 
  setoid_rewrite H. rewrite H0. auto.
Qed.
  
Lemma reloc_symbtable_cons_inv: forall f e stbl1 stbl2,
    reloc_symbtable f (e :: stbl1) = Some stbl2 ->
    exists e' stbl3, reloc_symbtable f stbl1 = Some stbl3 /\
                reloc_symbol f e = Some e' /\
                stbl2 = e' :: stbl3.
Proof.
  intros f e stbl1 stbl2 RELOC.
  cbn in RELOC. unfold reloc_iter in RELOC.
  destr_in RELOC. destr_in RELOC. inv RELOC.
  eauto.
Qed.

Lemma reloc_symbtable_app: forall l1 l2 l1' l2' f, 
    reloc_symbtable f l1 = Some l1' ->
    reloc_symbtable f l2 = Some l2' ->
    reloc_symbtable f (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  induction l1 as [|e1 l1].
  - cbn. intros l2 l1' l2' f RELOC1 RELOC2.
    inv RELOC1. cbn.
    setoid_rewrite RELOC2. auto.
  - intros l2 l1' l2' f RELOC1 RELOC2.
    apply reloc_symbtable_cons_inv in RELOC1.
    destruct RELOC1 as (e' & l3 & RELOC1 &  RE & EQ). subst.
    cbn ["++"].
    apply reloc_symbtable_cons; auto.
Qed.

Lemma reloc_symbtable_app_inv: forall l1 l2 l3 f, 
    reloc_symbtable f (l1 ++ l2) = Some l3 ->
    exists l1' l2', l3 = l1' ++ l2' /\
               reloc_symbtable f l1 = Some l1' /\
               reloc_symbtable f l2 = Some l2'.
Proof.
  induction l1 as [|e1 l1].
  - cbn. intros l2 l3 f FR.
    exists nil, l3. split; auto.
  - cbn. intros l2 l3 f FR.
    unfold reloc_iter in FR.
    destr_in FR. destr_in FR. inv FR.
    apply IHl1 in Heqo.
    destruct Heqo as (l1' & l2' & EQ & RELOC1 & RELOC2). subst.
    exists (s::l1'), l2'. split; cbn; auto.
    split; auto.
    unfold reloc_iter. 
    setoid_rewrite RELOC1. rewrite Heqo0.
    auto.
Qed.



Lemma reloc_iter_some_inv: forall f t1 t2 t3,
   fold_right (reloc_iter f) (Some t1) t2 = Some t3 ->
   exists t4, fold_right (reloc_iter f) (Some []) t2 = Some t4 /\ t3 = t4 ++ t1.
Proof.
  induction t2 as [| e2 t2].
  - cbn. inversion 1. subst. eauto.
  - cbn. intros t3 H.
    unfold reloc_iter in H. destr_in H.
    destr_in H. inv H.
    apply IHt2 in Heqo.
    destruct Heqo as (t4' & FL & EQ). subst.
    rewrite FL. 
    unfold reloc_iter.
    rewrite Heqo0. eauto.
Qed.


Lemma reloc_iter_none: forall f t,
   fold_right (reloc_iter f) None t = None.
Proof.
  induction t as [| e t].
  - cbn. auto.
  - cbn. rewrite IHt. cbn. auto.
Qed.

Lemma reloc_symbtable_rev_inv : forall f stbl1 stbl2,
    reloc_symbtable f (rev stbl1) = Some stbl2 ->
    exists stbl3, reloc_symbtable f stbl1 = Some stbl3 /\ stbl2 = rev stbl3.
Proof.
  induction stbl1 as [|e stbl1].
  - cbn. inversion 1. subst. eauto.
  - cbn. 
    rewrite fold_right_app. cbn.
    intros stbl2 H.
    destruct (reloc_symbol f e) eqn:RELOC. 
    + apply reloc_iter_some_inv in H.
      destruct H as (t4 & FL & EQ). subst.
      apply IHstbl1 in FL.
      destruct FL as (stbl3 & RELOC' & EQ). subst.
      unfold reloc_iter.
      setoid_rewrite RELOC'. rewrite RELOC. eauto.
    + rewrite reloc_iter_none in H. congruence.
Qed.



Lemma gen_symb_table_pres_link_check: 
  forall p1 p2 stbl1 dsz1 csz1 stbl2 dsz2 csz2 stbl2',
    PTree_Properties.for_all (prog_option_defmap p1) (link_prog_check p1 p2) = true ->
    list_norepet (map fst (AST.prog_defs p1)) ->
    list_norepet (map fst (AST.prog_defs p2)) ->
    gen_symb_table sec_data_id sec_code_id (AST.prog_defs p1) = (stbl1, dsz1, csz1) ->
    gen_symb_table sec_data_id sec_code_id (AST.prog_defs p2) = (stbl2, dsz2, csz2) ->
    reloc_symbtable (reloc_offset_fun dsz1 csz1) stbl2 = Some stbl2' ->
    PTree_Properties.for_all (symbtable_to_tree stbl1) 
                             (link_symbtable_check (symbtable_to_tree stbl2')) = true.
Proof.
  intros until stbl2'.
  intros FALL NORPT1 NORPT2 GST1 GST2 RS.
  rewrite PTree_Properties.for_all_correct.
  rewrite PTree_Properties.for_all_correct in FALL.
  intros x a GET.
  unfold gen_symb_table in GST1.
  destr_in GST1. destruct p.
  apply acc_symb_inv' in Heqp.
  destruct Heqp as (s1 & EQ & ACC1). subst.
  rewrite rev_app_distr in GST1. cbn in GST1. inv GST1.
  unfold gen_symb_table in GST2.
  destr_in GST2. destruct p.
  apply acc_symb_inv' in Heqp.
  destruct Heqp as (s2 & EQ & ACC2). subst.
  rewrite rev_app_distr in GST2. cbn in GST2. inv GST2.
  (* apply reloc_symbtable_cons_inv in RS. *)
  (* destruct RS as (e & s3 & RS & RE & EQ). subst. *)
  (* cbn in RE. inv RE.  *)
  (* rewrite symbtable_to_tree_ignore_dummy. *)
  generalize (acc_symb_reloc (AST.prog_defs p2) _ _ _ _ eq_refl ACC2 RS).
  rewrite Z.add_0_r.  rewrite Z.add_0_r.
  intros ACC2'.
  unfold link_symbtable_check.
  destr; auto.
  generalize (acc_symb_tree_entry_some_inv _ _ _ _ _ _ _ _ _ _ NORPT1 ACC1 GET).
  intros (def1 & GET1).
  rewrite <- (rev_involutive stbl2') in Heqo.
  generalize (acc_symb_tree_entry_some_inv _ _ _ _ _ _ _ _ _ _ NORPT2 ACC2' Heqo).
  intros (def2 & GET2).

  erewrite (acc_symb_tree_entry_some _ _ (AST.prog_defs p1)) in GET; eauto.
  cbn in GET. inv GET.
  erewrite (acc_symb_tree_entry_some _ _ (AST.prog_defs p2)) in Heqo; eauto.
  inv Heqo.

  generalize (FALL _ _ GET1). intros CHK.
  unfold link_prog_check in CHK. 
  setoid_rewrite GET2 in CHK.
  rewrite andb_true_iff in CHK. destruct CHK as [_ CHK].
  destr_in CHK.
  destruct (is_def_internal is_fundef_internal def1) eqn:INT1.
  destruct (is_def_internal is_fundef_internal def2) eqn:INT2.
  - setoid_rewrite link_int_defs_none in Heqo; auto. congruence.
  - erewrite link_get_symbentry_comm2; eauto.
  - erewrite link_get_symbentry_comm1; eauto.
Qed.


Lemma link_prog_symb_comm_external: 
  forall did cid id def defs1 defs2 stbl1 stbl2 
    dsz1 dsz1' csz1 csz1' dsz2 dsz2' csz2 csz2'
    t1 t2 dsz3 csz3,
    list_norepet (map fst defs1) ->
    list_norepet (map fst defs2) ->
    fold_left (acc_symb did cid) defs1 ([], dsz1', csz1') = (stbl1, dsz1, csz1) ->
    fold_left (acc_symb did cid) defs2 ([], dsz2', csz2') = (stbl2, dsz2, csz2) ->
    t1 = PTree_Properties.of_list defs1 ->
    t2 = PTree_Properties.of_list defs2 ->
    def_none_or_ext is_fundef_internal (t1!id) ->
    def_none_or_ext is_fundef_internal (t2!id) ->
    link_prog_merge (t1!id) (t2!id) = Some def ->
    link_symb_merge (symbtable_to_tree (rev stbl1)) ! id (symbtable_to_tree (rev stbl2)) ! id =
    Some (get_symbentry did cid dsz3 csz3 id def).
Proof.
  intros until csz3.
  intros NORPT1 NORPT2 ACC1 ACC2 EQ1 EQ2 DEFNE1 DEFNE2 LINK; subst.
  red in DEFNE1. red in DEFNE2.
  destruct DEFNE1 as [DEFNE1 | DEFNE1];
    destruct DEFNE2 as [DEFNE2 | DEFNE2].
  + unfold link_prog_merge in LINK.
    setoid_rewrite DEFNE1 in LINK.
    setoid_rewrite DEFNE2 in LINK. congruence.
  + unfold link_prog_merge in LINK.
    setoid_rewrite DEFNE1 in LINK.
    destruct DEFNE2 as (def2' & DEF2 & EXT2).
    setoid_rewrite DEF2 in LINK. inv LINK.
    erewrite acc_symb_tree_entry_none; eauto.
    erewrite acc_symb_tree_entry_some; eauto.
    cbn. f_equal.
    eapply get_extern_symbentry_ignore_size; eauto.
  + unfold link_prog_merge in LINK.
    destruct DEFNE1 as (def1' & DEF1 & EXT1).
    setoid_rewrite DEF1 in LINK. 
    setoid_rewrite DEFNE2 in LINK.
    setoid_rewrite DEF1 in LINK. inv LINK.
    erewrite (@acc_symb_tree_entry_none _ _ defs2 _ _ _ _ stbl2); eauto.
    erewrite (@acc_symb_tree_entry_some _ _ defs1 _ _ _ _ stbl1); eauto.
    cbn. f_equal.
    eapply get_extern_symbentry_ignore_size; eauto.
  + unfold link_prog_merge in LINK.
    destruct DEFNE1 as (def1' & DEF1 & EXT1).    
    destruct DEFNE2 as (def2' & DEF2 & EXT2).
    setoid_rewrite DEF1 in LINK. 
    setoid_rewrite DEF2 in LINK. 
    erewrite (@acc_symb_tree_entry_some _ _ defs1 _ _ _ _ stbl1); eauto.
    erewrite (@acc_symb_tree_entry_some _ _ defs2 _ _ _ _ stbl2); eauto.
    cbn.
    rewrite (get_extern_symbentry_ignore_size 
               _ _ id def2'
               (dsz2' + defs_data_size (defs_before id defs2))
               (csz2' + defs_code_size (defs_before id defs2))
               dsz3 csz3); auto.
    eapply link_get_symbentry_comm1; eauto.
Qed.


Lemma PTree_combine_ids_defs_match_extdefs_comm: 
  forall did cid defs defs1 defs2 stbl1 stbl2 
    dsz1 dsz1' csz1 csz1' dsz2 dsz2' csz2 csz2'
    t1 t2 stbl dsz3 csz3 dsz4 csz4,
    list_norepet (map fst defs1) ->
    list_norepet (map fst defs2) ->
    fold_left (acc_symb did cid) defs1 ([], dsz1', csz1') = (stbl1, dsz1, csz1) ->
    fold_left (acc_symb did cid) defs2 ([], dsz2', csz2') = (stbl2, dsz2, csz2) ->
    t1 = PTree_Properties.of_list defs1 ->
    t2 = PTree_Properties.of_list defs2 ->
    defs_none_or_ext t1 (map fst defs) ->
    defs_none_or_ext t2 (map fst defs) ->
    PTree_combine_ids_defs_match t1 t2 link_prog_merge (map fst defs) defs ->
    fold_left (acc_symb did cid) defs ([], dsz3, csz3) = (stbl, dsz4, csz4) ->
    exists entries, PTree_combine_ids_defs_match (symbtable_to_tree (rev stbl1)) 
                                            (symbtable_to_tree (rev stbl2))
                                            link_symb_merge
                                            (map fst defs)
                                            entries /\
               map snd entries = rev stbl.
Proof.
  induction defs as [|def defs]; cbn;
    intros until csz4;
    intros NORPT1 NORPT2 ACC1 ACC2 EQ1 EQ2 SRC1 SRC2 MATCH ACC3; subst.
  - inv ACC3. cbn. exists nil.
    split; auto. red. auto.
  - destruct def as (id, def). cbn in *.
    inv MATCH. destruct H2.
    destr_in ACC3.
    apply acc_symb_inv' in ACC3. 
    destruct ACC3 as (stbl' & EQ & ACC3). subst.
    assert (exists entries : list (ident * symbentry),
               PTree_combine_ids_defs_match (symbtable_to_tree (rev stbl1))
                                            (symbtable_to_tree (rev stbl2)) 
                                            link_symb_merge 
                                            (map fst defs) entries /\
               map snd entries = rev stbl') as MATCH_RST.
    { eapply IHdefs with (defs1:= defs1) (stbl2:=stbl2); eauto.
      red. intros. apply SRC1. apply in_cons. auto.
      red. intros. apply SRC2. apply in_cons. auto. }
    destruct MATCH_RST as (entries' & MATCH_RST & EQ).
    rewrite rev_app_distr. cbn.
    exists ((id, get_symbentry did cid dsz3 csz3 id def) :: entries').
    split. 
    Focus 2. cbn. f_equal. auto.
    red. constructor; auto. 
    split; auto.
    
    eapply link_prog_symb_comm_external with (defs1:=defs1); eauto.
    unfold defs_none_or_ext in SRC1.
    eapply SRC1; apply in_eq.
    eapply SRC2; apply in_eq.
Qed.        


Lemma link_prog_symb_comm_internal1: 
  forall did cid def id defs1 defs2 stbl1 stbl2 
    dsz1 dsz1' csz1 csz1' dsz2 dsz2' csz2 csz2'
    t1 t2,
    list_norepet (map fst defs1) ->
    list_norepet (map fst defs2) ->
    fold_left (acc_symb did cid) defs1 ([], dsz1', csz1') = (stbl1, dsz1, csz1) ->
    fold_left (acc_symb did cid) defs2 ([], dsz2', csz2') = (stbl2, dsz2, csz2) ->
    t1 = PTree_Properties.of_list defs1 ->
    t2 = PTree_Properties.of_list defs2 ->
    def_some_int is_fundef_internal (t1!id) ->
    link_prog_merge (t1!id) (t2!id) = Some def ->
    link_symb_merge 
      (symbtable_to_tree (rev stbl1)) ! id
      (symbtable_to_tree (rev stbl2)) ! id = 
    Some (get_symbentry did cid 
                        (dsz1' + defs_data_size (defs_before id defs1))
                        (csz1' + defs_code_size (defs_before id defs1))
                        id def).
Proof.
  intros until t2.
  intros NORPT1 NORPT2 ACC1 ACC2 EQ1 EQ2 INT1 LINK. subst.
  red in INT1.
  destruct INT1 as (def' & GET1 & INT1).
  unfold link_prog_merge in LINK.
  setoid_rewrite GET1 in LINK.
  destruct ((PTree_Properties.of_list defs2) ! id) as [gd2|] eqn:DEFS2.
  + generalize (link_int_defs_some_inv _ _ INT1 LINK).
    intros INT2.
    erewrite acc_symb_tree_entry_some with (defs:= defs1) (dsz1:= dsz1'); eauto.
    erewrite acc_symb_tree_entry_some with (defs:= defs2) (dsz1:= dsz2'); eauto.
    cbn.
    eapply link_get_symbentry_comm2; eauto.
  + rewrite LINK in GET1. inv GET1.
    erewrite acc_symb_tree_entry_some with (defs:=defs1) (stbl:=stbl1); eauto.
    erewrite acc_symb_tree_entry_none with (defs:=defs2) (stbl:=stbl2); eauto.
Qed.


Lemma PTree_combine_ids_defs_match_intdefs_comm1: 
  forall did cid defs ids defs1 defs2 stbl1 stbl2 
    dsz1 dsz1' csz1 csz1' dsz2 dsz2' csz2 csz2'
    t1 t2 stbl dsz3 csz3 dsz4 csz4,
    list_norepet (map fst defs1) ->
    list_norepet (map fst defs2) ->
    fold_left (acc_symb did cid) defs1 ([], dsz1', csz1') = (stbl1, dsz1, csz1) ->
    fold_left (acc_symb did cid) defs2 ([], dsz2', csz2') = (stbl2, dsz2, csz2) ->
    t1 = PTree_Properties.of_list defs1 ->
    t2 = PTree_Properties.of_list defs2 ->
    defs_some_int t1 ids ->
    PTree_combine_ids_defs_match t1 t2 link_prog_merge ids defs ->
    fold_left (acc_symb did cid) defs ([], dsz3, csz3) = (stbl, dsz4, csz4) ->
    symbtable_entry_equiv_sizes stbl dsz1' csz1' defs1 ->
    exists entries, PTree_combine_ids_defs_match (symbtable_to_tree (rev stbl1)) 
                                            (symbtable_to_tree (rev stbl2))
                                            link_symb_merge
                                            ids
                                            entries /\
               map snd entries = rev stbl.
Proof.
  induction defs as [|def defs]; cbn;
    intros until csz4;
    intros NORPT1 NORTP2 ACC1 ACC2 EQ1 EQ2 SRC2 MATCH ACC3 SIZES; subst.
  - inv ACC3. inv MATCH. cbn. exists nil.
    split; auto. red. auto.
  - destruct def as (id, def). cbn in *.
    inv MATCH. destruct H2. subst.
    destr_in ACC3.
    apply acc_symb_inv' in ACC3. 
    destruct ACC3 as (stbl' & EQ & ACC3). subst.
    assert (exists entries : list (ident * symbentry),
               PTree_combine_ids_defs_match (symbtable_to_tree (rev stbl1))
                                            (symbtable_to_tree (rev stbl2)) 
                                            link_symb_merge 
                                            l entries /\
               map snd entries = rev stbl') as MATCH_RST.
    { eapply IHdefs with (defs1:= defs1) (stbl2:=stbl2); eauto.
      red. intros. eapply SRC2. apply in_cons. auto. 
      red. intros. red in SIZES.
      eapply SIZES. rewrite in_app. left. eauto.
    }
    destruct MATCH_RST as (entries' & MATCH_RST & EQ).
    rewrite rev_app_distr. cbn.
    exists ((id, get_symbentry did cid dsz3 csz3 id def) :: entries').
    split. 
    Focus 2. cbn. f_equal. auto.
    red. constructor; auto. 
    split; auto.
    red in SRC2.
    generalize (SRC2 _ (in_eq _ _)).
    intros INT. 

    erewrite link_prog_symb_comm_internal1 with (defs1:=defs1) (stbl1:=stbl1); eauto.
    red in SIZES.
    erewrite <- SIZES; eauto.
    rewrite in_app. right. apply in_eq. 
Qed.
    

Lemma PTree_combine_ids_defs_match_intdefs_comm2: 
  forall did cid ids defs defs1 defs2 stbl1 stbl2 
    dsz1 dsz1' csz1 csz1' dsz2 dsz2' csz2 csz2'
    t1 t2 stbl dsz3 csz3,
    list_norepet (map fst defs1) ->
    list_norepet (map fst defs2) ->
    fold_left (acc_symb did cid) defs1 ([], dsz1', csz1') = (stbl1, dsz1, csz1) ->
    fold_left (acc_symb did cid) defs2 ([], dsz2', csz2') = (stbl2, dsz2, csz2) ->
    t1 = PTree_Properties.of_list defs1 ->
    t2 = PTree_Properties.of_list defs2 ->
    defs_some_int t2 ids ->
    PTree_combine_ids_defs_match t1 t2 link_prog_merge ids defs ->
    fold_left (acc_symb did cid) defs ([], dsz2', csz2') = (stbl, dsz3, csz3) ->
    symbtable_entry_equiv_sizes stbl dsz2' csz2' defs2 ->
    exists entries, PTree_combine_ids_defs_match (symbtable_to_tree (rev stbl1)) 
                                            (symbtable_to_tree (rev stbl2))
                                            link_symb_merge
                                            ids
                                            entries /\
               map snd entries = rev stbl.
Proof.
  intros until csz3.
  intros NORPT1 NORPT2 ACC1 ACC2 T1 T2 SOME MATCH ACC3 SIZES. subst.
  assert (PTree_combine_ids_defs_match 
            (PTree_Properties.of_list defs2)
            (PTree_Properties.of_list defs1)
            link_prog_merge ids defs) as MATCH'.
  { eapply PTree_combine_ids_defs_match_symm; eauto.
    intros. apply link_prog_merge_symm. apply link_unit_symm. }

  assert (exists entries : list (ident * symbentry),
             PTree_combine_ids_defs_match (symbtable_to_tree (rev stbl2))
                                          (symbtable_to_tree (rev stbl1)) 
                                          link_symb_merge ids entries /\
             map snd entries = rev stbl) as RS.
  { eapply PTree_combine_ids_defs_match_intdefs_comm1 
      with (defs1:= defs2) (stbl1:=stbl2)
           (defs2:= defs1) (stbl2:=stbl1); eauto. }
  destruct RS as (entries & MATCH'' & EQ).
  exists entries; split; eauto.
  eapply PTree_combine_ids_defs_match_symm; eauto.
  eapply link_symb_merge_symm.
Qed.

Lemma def_external_data_size_0: forall def,
    is_def_internal is_fundef_internal def = false -> def_data_size def = 0.
Proof.
  intros.
  unfold def_data_size.
  setoid_rewrite extern_init_data_nil; auto.
Qed.

Lemma def_external_code_size_0: forall def,
    is_def_internal is_fundef_internal def = false -> def_code_size def = 0.
Proof.
  intros.
  unfold def_code_size.
  rewrite extern_fun_nil; auto.
Qed.

Lemma def_eq_data_size_eq: forall d1 d2,
    def_eq d1 d2 -> def_data_size d1 = def_data_size d2.
Proof.
  intros. unfold def_data_size.
  setoid_rewrite (get_def_init_data_eq H); eauto.
Qed.

Lemma def_eq_code_size_eq: forall d1 d2,
    def_eq d1 d2 -> def_code_size d1 = def_code_size d2.
Proof.
  intros. unfold def_code_size.
  erewrite get_def_instrs_eq; eauto.
Qed.


Lemma PTree_combine_ids_defs_match_size_eq: 
  forall defs1 defs2 t1 t2,
    (forall id def, In (id, def) defs1 -> t1 ! id = Some def) ->
    PTree_combine_ids_defs_match 
      t1 t2 link_prog_merge
      (map fst (filter_internal_defs is_fundef_internal defs1))
      defs2 ->
    defs_data_size (map snd defs1) = defs_data_size (map snd defs2) /\
    defs_code_size (map snd defs1) = defs_code_size (map snd defs2).
Proof.
  intros defs1 defs2 t1 t2 NIN MATCH.
  eapply PTree_combine_ids_defs_match_instrs_data_eq in MATCH; auto.
  destruct MATCH as (IEQ & DEQ).
  rewrite acc_instrs_size.
  rewrite acc_instrs_size.
  rewrite acc_init_data_size.
  rewrite acc_init_data_size.
  rewrite IEQ, DEQ. auto.
Qed.

(* Lemma get_symbentry_sizes_inv:  *)
(*   forall did1 cid1 dsz1 csz1 id1 def1  *)
(*     did2 cid2 dsz2 csz2 id2 def2,  *)
(*     def_internal def1 = true -> *)
(*     get_symbentry did1 cid1 dsz1 csz1 id1 def1 =  *)
(*     get_symbentry did2 cid2 dsz2 csz2 id2 def2 -> *)
(*     dsz1 = dsz2 /\ csz1 = csz2. *)
(* Proof. *)
(*   intros until def2. *)
(*   intros IN EQ. *)
(*   unfold def_internal in IN. *)
(*   unfold is_def_internal in IN. *)
(*   destr_in IN. destruct g; subst. *)
(*   destruct f. cbn in *. *)

(* Definition symbtable_entry_sizes_ stbl dsz1 csz1 defs1 := *)
(*   forall did cid dsz3 csz3 id def, *)
(*     In (get_symbentry did cid dsz3 csz3 id def) stbl -> *)
(*     get_symbentry did cid dsz3 csz3 id def = *)
(*     get_symbentry did cid  *)
(*                   (dsz1 + defs_data_size (defs_before id defs1)) *)
(*                   (csz1 + defs_code_size (defs_before id defs1))  *)
(*                   id def. *)


Lemma get_symbentry_eq_internal_fun_inv: 
  forall did1 cid1 dsz1 csz1 did2 cid2 dsz2 csz2 id1 id2 f def,
    get_symbentry did1 cid1 dsz1 csz1 id1 (Some (Gfun f)) =
    get_symbentry did2 cid2 dsz2 csz2 id2 def ->
    is_fundef_internal f = true ->
    exists f', def = (Some (Gfun f')) /\ is_fundef_internal f' = true /\
          csz1 = csz2.
Proof.
  intros until def.
  intros EQ INT.
  cbn in EQ. destruct f; cbn in INT; try congruence.
  destruct def; cbn in EQ; try congruence.
  destruct g; cbn in EQ; try congruence.
  destruct f0; cbn in EQ; try congruence.
  inv EQ. cbn; eauto.
  destr_in EQ; try congruence.
  destruct i; try congruence.
  destruct l; try congruence.
Qed.

Lemma get_symbentry_internal_fun_eq: 
  forall did cid dsz1 dsz2 csz id f, 
    is_fundef_internal f = true ->
    get_symbentry did cid dsz1 csz id (Some (Gfun f)) =
    get_symbentry did cid dsz2 csz id (Some (Gfun f)).
Proof.
  intros. 
  destruct f; cbn in H; try congruence.
  cbn. auto.
Qed.

Lemma get_symbentry_eq_internal_var_inv: 
  forall did1 cid1 dsz1 csz1 did2 cid2 dsz2 csz2 id1 id2 v def,
    get_symbentry did1 cid1 dsz1 csz1 id1 (Some (Gvar v)) =
    get_symbentry did2 cid2 dsz2 csz2 id2 def ->
    is_var_internal v = true ->
    exists v', def = (Some (Gvar v')) /\ is_var_internal v' = true /\
          dsz1 = dsz2.
Proof.
  intros until def.
  intros EQ INT.
  erewrite get_internal_var_entry in EQ; eauto.
  destruct def. destruct g.
  cbn in EQ. destruct f; inv EQ.
  destruct (is_var_internal v0) eqn:INT0.
  rewrite get_internal_var_entry in EQ; eauto.
  inv EQ. eauto.
  rewrite var_not_internal_iff in INT0.
  destruct INT0.
  erewrite get_comm_var_entry in EQ; eauto. inv EQ.
  erewrite get_external_var_entry in EQ; eauto. inv EQ.
  cbn in EQ. inv EQ.
Qed.

Lemma get_symbentry_internal_var_eq: 
  forall did cid dsz csz1 csz2 id v, 
    is_var_internal v = true ->
    get_symbentry did cid dsz csz1 id (Some (Gvar v)) =
    get_symbentry did cid dsz csz2 id (Some (Gvar v)).
Proof.
  intros. 
  erewrite get_internal_var_entry; eauto.
  erewrite get_internal_var_entry; eauto.
Qed.

Lemma symbtable_entry_equiv_sizes_cons :
  forall stbl dsz1 csz1 p def1 defs1,
    symbtable_entry_equiv_sizes 
      stbl
      (def_data_size def1 + dsz1)
      (def_code_size def1 + csz1) defs1 ->
    (forall e, In e stbl ->  symbentry_id e <> p) ->
    symbtable_entry_equiv_sizes stbl dsz1 csz1 ((p, def1) :: defs1).
Proof.
  intros stbl dsz1 csz1 p def1 defs1 SB NE.
  red. intros did cid dsz3 csz3 id def IN.
  generalize (NE _ IN). 
  intros NE'.
  rewrite get_symbentry_id in NE'. 
  assert (id <> p) by congruence.
  setoid_rewrite defs_before_tail; auto.
  rewrite defs_data_size_cons.
  rewrite defs_code_size_cons.
  red in SB.
  erewrite SB; eauto.
  f_equal; omega.
Qed.

Lemma PTree_combine_ids_defs_match_symbtable_entry_sizes:
  forall did cid defs1 defs2 t1 t2 dsz1 csz1 dsz2 csz2 stbl,
    (forall id def, In (id, def) defs1 -> t1 ! id = Some def) ->
    list_norepet (map fst defs1) ->
    PTree_combine_ids_defs_match 
      t1 t2 link_prog_merge
      (map fst (filter_internal_defs is_fundef_internal defs1))
      defs2 ->
    fold_left (acc_symb did cid) defs2 ([], dsz1, csz1) =
            (stbl, dsz2, csz2) ->
    symbtable_entry_equiv_sizes stbl dsz1 csz1 defs1.
Proof.
  induction defs1 as [|def1 defs1]; intros until stbl.
  - intros IN NORPT MATCH ACC.
    cbn in *. inv MATCH. cbn in *. inv ACC.
    red. intros. inv H.
  - intros IN NORPT MATCH ACC.
    cbn in *. destruct def1 as (id1, def1).
    destr_in MATCH.
    + cbn in *. inv MATCH.
      destruct y. destruct H1. subst.
      cbn in *. destr_in ACC.
      apply acc_symb_inv' in ACC.
      destruct ACC as (stbl' & EQ & ACC). subst.
      eapply symbtable_entry_equiv_sizes_app_comm.
      eapply symbtable_entry_equiv_sizes_app.
      * red. intros. inv H.
        assert (p = id).
        { eapply get_symbentry_eq_id_inv; eauto. }
        subst.
        rewrite defs_before_head. cbn.
        repeat rewrite Z.add_0_r.
        generalize (IN _ _ (or_introl eq_refl)).
        intros GET1. rewrite GET1 in H0.
        assert (def_internal o = true) as INT.
        { eapply link_prog_merge_def_internal; eauto. }
        destruct o; cbn in INT; try congruence.
        destruct g.
        ** eapply (get_symbentry_eq_internal_fun_inv 
                     did cid dsz1 csz1 did0 cid0) in INT; eauto.
           destruct INT as (f' & EQ & INT' & CEQ). subst.
           erewrite get_symbentry_internal_fun_eq; eauto.
        ** eapply (get_symbentry_eq_internal_var_inv
                     did cid dsz1 csz1 did0 cid0) in INT; eauto.
           destruct INT as (v' & EQ & INT' & CEQ). subst.
           erewrite get_symbentry_internal_var_eq; eauto.
        ** inv H1.
      * assert (symbtable_entry_equiv_sizes stbl'
                                      (def_data_size def1 + dsz1)
                                      (def_code_size def1 + csz1)
                                      defs1) as SE.
        { eapply (IHdefs1 l' t1 t2 _ _ dsz2 csz2); eauto.
          inv NORPT. auto.
          generalize (IN p def1 (or_introl eq_refl)).
          intros EQ. rewrite EQ in H0.
          generalize (link_merge_internal_external_defs _ _ _ Heqb H0).
          intros DEFEQ.
          erewrite <- def_eq_code_size_eq; eauto.
          erewrite <- def_eq_data_size_eq; eauto.
          apply update_code_data_size_inv in Heqp0. destruct Heqp0. subst.
          rewrite Z.add_comm.
          rewrite (Z.add_comm (def_code_size o) csz1). auto.
        }
        inv NORPT.
        generalize (PTree_combine_ids_defs_match_ids_eq _ _ _ _ _ H3).
        intros IDSEQ.
        generalize (acc_symb_pres_ids _ _ _ _ _ _ _ _ ACC).
        intros IDSEQ'.
        setoid_rewrite IDSEQ' in IDSEQ.
        assert (forall e, In e stbl' ->  symbentry_id e <> p) as IDNEQ. 
        { intros e IN'.  
          assert (In (symbentry_id e) (get_symbentry_ids (rev stbl'))).
          { eapply get_symbentry_ids_in; eauto. }
          rewrite <- IDSEQ in H.
          apply in_map_filter in H.
          intros IDE. inv IDE. contradiction.
        }
        eapply symbtable_entry_equiv_sizes_cons; eauto.
        
    + assert (symbtable_entry_equiv_sizes stbl dsz1 csz1 defs1) as SE.
      { eapply (IHdefs1 defs2 t1 t2 dsz1 csz1 dsz2 csz2 stbl); eauto.
        inv NORPT. auto.
      }
      inv NORPT.
      generalize (PTree_combine_ids_defs_match_ids_eq _ _ _ _ _ MATCH).
      intros IDSEQ.
      generalize (acc_symb_pres_ids _ _ _ _ _ _ _ _ ACC).
      intros IDSEQ'.
      setoid_rewrite IDSEQ' in IDSEQ.
      assert (forall e, In e stbl ->  symbentry_id e <> id1) as IDNEQ. 
      { intros e IN'.  
        assert (In (symbentry_id e) (get_symbentry_ids (rev stbl))).
        { eapply get_symbentry_ids_in; eauto. }
        rewrite <- IDSEQ in H.
        apply in_map_filter in H.
        intros IDE. inv IDE. contradiction.
      }
      eapply symbtable_entry_equiv_sizes_cons; eauto.
      erewrite def_external_data_size_0; auto.
      erewrite def_external_code_size_0; auto.
Qed.


Lemma PTree_extract_elements_remain_keys_eq_link: 
  forall did cid defs1 defs2 dsz1 csz1 dsz1' csz1'
    dsz2 csz2 dsz2' csz2' stbl1 stbl2 t1 t2 entries1 entries2 ids,
    (forall x d1 d2, (PTree_Properties.of_list defs1)!x = Some d1 ->
                (PTree_Properties.of_list defs2)!x = Some d2 ->
                exists d, link d1 d2 = Some d) ->
    list_norepet (map fst defs1) ->
    list_norepet (map fst defs2) ->
    fold_left (acc_symb did cid) defs1 ([], dsz1, csz1) = (stbl1, dsz1', csz1') ->
    fold_left (acc_symb did cid) defs2 ([], dsz2, csz2) = (stbl2, dsz2', csz2') ->
    ids = map fst (filter_internal_defs is_fundef_internal defs1) ++
              map fst (filter_internal_defs is_fundef_internal defs2) ->
    PTree_extract_elements ids
                           (PTree.combine link_prog_merge 
                                          (PTree_Properties.of_list defs1)
                                          (PTree_Properties.of_list defs2)) = Some (entries1, t1) ->
    PTree_extract_elements ids
                           (PTree.combine link_symb_merge 
                                          (symbtable_to_tree (rev stbl1))
                                          (symbtable_to_tree (rev stbl2))) = Some (entries2, t2) ->
    map fst (PTree.elements t1) = map fst (PTree.elements t2).
Proof.
  intros until ids.
  intros CHECK NORPT1 NORPT2 ACC1 ACC2 IDS EXT1 EXT2. subst.
  eapply PTree_extract_elements_remain in EXT1.
  eapply PTree_extract_elements_remain in EXT2.
  subst.
  apply PTree_elements_eq.
  - intros i x FL.
    generalize (PTree_remove_ids_not_in _ _ _ _ FL).
    intros NIN.
    rewrite PTree_get_remove_not_in_eq; eauto.
    apply PTree_get_remove_not_in in FL.
    rewrite PTree.gcombine in FL; auto.
    rewrite PTree.gcombine; auto.
    rewrite not_in_app in NIN.
    unfold collect_internal_def_ids in NIN.
    destruct NIN as (NIN1 & NIN2).
    generalize (filter_internal_defs_none_ext _ _ NORPT1 NIN1). 
    intros DN1.
    generalize (filter_internal_defs_none_ext _ _ NORPT2 NIN2). 
    intros DN2.
    erewrite link_prog_symb_comm_external with
        (t1:=PTree_Properties.of_list defs1)
        (t2:=PTree_Properties.of_list defs2)
        (defs1:= defs1)
        (defs2:= defs2) 
        (dsz3:= 0) (csz3:=0); eauto.
  - intros i x FL.
    generalize (PTree_remove_ids_not_in _ _ _ _ FL).
    intros NIN.
    rewrite PTree_get_remove_not_in_eq; eauto.
    apply PTree_get_remove_not_in in FL.
    rewrite PTree.gcombine in FL; auto.
    rewrite PTree.gcombine; auto.
    rewrite not_in_app in NIN.
    unfold collect_internal_def_ids in NIN.
    destruct NIN as (NIN1 & NIN2).
    generalize (filter_internal_defs_none_ext _ _ NORPT1 NIN1). 
    intros DN1.
    generalize (filter_internal_defs_none_ext _ _ NORPT2 NIN2). 
    intros DN2.
    red in DN1.
    destruct DN1 as [DNN1 | (def1 & DNS1 & EX1)];
    destruct DN2 as [DNN2 | (def2 & DNS2 & EX2)].
    + erewrite acc_symb_tree_entry_none in FL; eauto.
      erewrite acc_symb_tree_entry_none in FL; eauto.
      cbn in FL. congruence.
    + setoid_rewrite DNN1.
      setoid_rewrite DNS2. eauto.
    + setoid_rewrite DNS1.
      setoid_rewrite DNN2.
      setoid_rewrite link_prog_merge_symm; auto. cbn. eauto.
    + setoid_rewrite DNS1.
      setoid_rewrite DNS2. cbn.
      eapply CHECK; eauto.
Qed.

Lemma ext_defs_code_size: forall (defs: list (ident * option gdef)),
    Forall (fun '(_, def) => is_def_internal is_fundef_internal def = false) defs ->
    defs_code_size (map snd defs) = 0.
Proof.
  induction defs as [| def defs].
  - cbn. auto.
  - intros H. 
    cbn [map snd]. rewrite defs_code_size_cons.
    generalize (Forall_inv H).
    intros DI. destruct def as (id, def). cbn.
    unfold def_code_size.
    erewrite extern_fun_nil; eauto. cbn.
    eapply IHdefs; eauto.
    inv H. auto.
Qed.

Lemma ext_defs_data_size: forall (defs: list (ident * option gdef)),
    Forall (fun '(_, def) => is_def_internal is_fundef_internal def = false) defs ->
    defs_data_size (map snd defs) = 0.
Proof.
  induction defs as [| def defs].
  - cbn. auto.
  - intros H. 
    cbn [map snd]. rewrite defs_data_size_cons.
    generalize (Forall_inv H).
    intros DI. destruct def as (id, def). cbn.
    unfold def_data_size.
    setoid_rewrite extern_init_data_nil; eauto. cbn.
    eapply IHdefs; eauto.
    inv H. auto.
Qed.


Lemma link_ordered_gen_symb_comm_eq_size : forall p1 p2 stbl1 stbl2 dsz1 csz1 stbl2' dsz2 csz2 stbl3 dsz3 csz3 t1 defs3,
    PTree_Properties.for_all (prog_option_defmap p1) (link_prog_check p1 p2) = true ->
    list_norepet (map fst (AST.prog_defs p1)) ->
    list_norepet (map fst (AST.prog_defs p2)) ->
    gen_symb_table sec_data_id sec_code_id (AST.prog_defs p1) = (stbl1, dsz1, csz1) ->
    gen_symb_table sec_data_id sec_code_id (AST.prog_defs p2) = (stbl2, dsz2, csz2) ->
    reloc_symbtable (reloc_offset_fun dsz1 csz1) stbl2 = Some stbl2' ->
    PTree_extract_elements
      (collect_internal_def_ids is_fundef_internal p1 ++
       collect_internal_def_ids is_fundef_internal p2)
      (PTree.combine link_prog_merge 
                     (prog_option_defmap p1)
                     (prog_option_defmap p2)) = Some (defs3, t1) ->
    gen_symb_table sec_data_id sec_code_id (PTree.elements t1 ++ defs3) = (stbl3, dsz3, csz3) ->
    dsz3 = dsz1 + dsz2 /\
    csz3 = csz1 + csz2 /\ 
    exists entries t2,
      PTree_extract_elements
        (collect_internal_def_ids is_fundef_internal p1 ++
         collect_internal_def_ids is_fundef_internal p2)
        (PTree.combine link_symb_merge 
                       (symbtable_to_tree stbl1)
                       (symbtable_to_tree stbl2')) = Some (entries, t2) /\
      stbl3 = map snd (PTree.elements t2 ++ entries).
Proof.
  intros until defs3.
  intros CHECK NORPT1 NORPT2 GS1 GS2 RELOC EXT GS3.
  generalize (PTree_extract_elements_app _ _ _ _ _ EXT).
  intros (t1' & defs1 & defs2 & EXT2 & EXT1 & EQ). subst.
  generalize (PTree_extract_elements_range_norepet _ _ _ _ EXT1).
  intros NORPT1'.
  generalize (PTree_extract_elements_range_norepet _ _ _ _ EXT2).
  intros NORPT2'.
  
  unfold gen_symb_table in *.
  destr_in GS1. destruct p. inv GS1.
  destr_in GS2. destruct p. inv GS2.
  apply acc_symb_inv' in Heqp. 
  destruct Heqp as (stbl1 & EQ1 & ACCSYM1). subst.
  apply acc_symb_inv' in Heqp0. 
  destruct Heqp0 as (stbl2 & EQ2 & ACCSYM2). subst.
  rewrite rev_app_distr in RELOC. 
  cbn [rev "++"] in RELOC. 
  generalize (acc_symb_reloc _ _ _ _ _ eq_refl ACCSYM2 RELOC).
  repeat rewrite Z.add_0_r. intros ACCSYM2'.
  destr_in GS3. destruct p. inv GS3.
  apply acc_symb_inv' in Heqp. 
  destruct Heqp as (stbl3 & EQ3 & ACCSYM3). subst.
  repeat rewrite rev_app_distr in *; cbn[rev "++"] in *.
  repeat rewrite symbtable_to_tree_ignore_dummy in *.
  apply reloc_symbtable_rev_inv in RELOC.
  destruct RELOC as (stbl2'' & RELOC & EQ). subst.
  rewrite rev_involutive in ACCSYM2'.  

  rewrite fold_left_app in ACCSYM3.
  destruct (fold_left (acc_symb sec_data_id sec_code_id) 
                      (PTree.elements t1) ([], 0, 0)) eqn:ACCSYMRST.
  destruct p. 
  setoid_rewrite ACCSYMRST in ACCSYM3.
  apply acc_symb_inv' in ACCSYM3.
  destruct ACCSYM3 as (stbl1' & EQ & ACCSYM4). subst.
  rewrite fold_left_app in ACCSYM4.
  destruct (fold_left (acc_symb sec_data_id sec_code_id) defs1 ([], z0, z)) eqn:ACCSYM3.
  destruct p.
  apply acc_symb_inv' in ACCSYM4.
  destruct ACCSYM4 as (stbl3 & EQ & ACCSYM4). subst.

  (** Compute the sizes *)
  generalize (acc_symb_size' _ _ _ _ _ _ _ _ _ ACCSYM1).
  intros (DSZ1 & CSZ1). cbn in DSZ1, CSZ1.
  generalize (acc_symb_size' _ _ _ _ _ _ _ _ _ ACCSYM2).
  intros (DSZ2 & CSZ2). cbn in DSZ2, CSZ2.
  generalize (acc_symb_size' _ _ _ _ _ _ _ _ _ ACCSYMRST).
  intros (Z0 & Z). cbn in Z0, Z.
  generalize (acc_symb_size' _ _ _ _ _ _ _ _ _ ACCSYM3).
  intros (Z2 & Z1). cbn in Z2, Z1.
  generalize (acc_symb_size' _ _ _ _ _ _ _ _ _ ACCSYM4).
  intros (DSZ3 & CSZ3). cbn in DSZ3, CSZ3.


  (** Matching between remaining ids and external definitions*)
  assert (defs_none_or_ext (prog_option_defmap p1) (map fst (PTree.elements t1)) /\
          defs_none_or_ext (prog_option_defmap p2) (map fst (PTree.elements t1)))
    as RM_DEFS.
  { eapply PTree_extract_elements_remain_external; eauto. }
  destruct RM_DEFS as (RM_DEFS1 & RM_DEFS2).
  assert (PTree_combine_ids_defs_match (prog_option_defmap p1)
                                       (prog_option_defmap p2)
                                       link_prog_merge
                                       (map fst (PTree.elements t1))
                                       (PTree.elements t1)) as RM_MATCH.
  { eapply PTree_extract_elements_combine_remain_match; eauto. }

  (** Compute the sizes for external definitions *)
  generalize (combine_defs_none_or_ext RM_DEFS1 RM_DEFS2 RM_MATCH).
  intros RMEXT.
  erewrite ext_defs_code_size in Z; auto.
  erewrite ext_defs_data_size in Z0; auto.
  subst z0 z. cbn in Z1, Z2.
                            
  (** Matching between remaining ids and external symbols*)
  assert (exists entries, PTree_combine_ids_defs_match 
                       (symbtable_to_tree (rev stbl1)) 
                       (symbtable_to_tree (rev stbl2''))
                       link_symb_merge
                       (map fst (PTree.elements t1)) entries /\
                     map snd entries = rev s) as RM_MATCH'.
  { eapply PTree_combine_ids_defs_match_extdefs_comm 
      with (defs1 := AST.prog_defs p1) 
           (defs2 := AST.prog_defs p2); eauto. }
  destruct RM_MATCH' as (rm_stbl & RM'_MATCH & RM_ENTRIES).

  (** Matching between ids and internal definitions from program 2 *)    
  assert (defs_some_int (prog_option_defmap p2)
                        (collect_internal_def_ids is_fundef_internal p2)) as DEFS2.
  { eapply collect_defs_some_int; eauto. }

  assert (PTree_combine_ids_defs_match (prog_option_defmap p1)
                                       (prog_option_defmap p2)
                                       link_prog_merge
                                       (collect_internal_def_ids is_fundef_internal p2)
                                       defs2) as MATCH2.
  { eapply PTree_extract_elements_combine_match; eauto. }

  (** Matching between ids and internal definitions from program 1 *)    
  assert (defs_some_int (prog_option_defmap p1)
                        (collect_internal_def_ids is_fundef_internal p1)) as DEFS1.
  { eapply collect_defs_some_int; eauto. }

  assert (PTree_combine_ids_defs_match (prog_option_defmap p1)
                                       (prog_option_defmap p2)
                                       link_prog_merge
                                       (collect_internal_def_ids is_fundef_internal p1)
                                       defs1) as MATCH1.
  { 
    generalize (PTree_extract_elements_remain _ _ _ _ EXT2). 
    intros TEQ. rewrite TEQ in EXT1.
    generalize (PTree_extract_elements_remove_list_pres _ _ _ _ _ EXT1).
    intros (t1'' & EXT2').
    eapply PTree_extract_elements_combine_match; eauto. 
  }
  
  (** Compute the sizes for internal symbols *)

  assert (z2 = dsz1).
  { 
    subst. unfold collect_internal_def_ids in MATCH1.              
    apply PTree_combine_ids_defs_match_size_eq in MATCH1.
    destruct MATCH1. auto.
    intros. eapply prog_option_defmap_norepet; eauto.
  }
  assert (z1 = csz1). 
  {
    subst. unfold collect_internal_def_ids in MATCH1.              
    apply PTree_combine_ids_defs_match_size_eq in MATCH1.
    destruct MATCH1. auto.
    intros. eapply prog_option_defmap_norepet; eauto.
  }
  clear Z1 Z2. subst z1 z2.
  assert (defs_data_size (map snd (AST.prog_defs p2)) = defs_data_size (map snd defs2)).
  {
    subst. 
    apply PTree_combine_ids_defs_match_symm in MATCH2; eauto.
    unfold collect_internal_def_ids in MATCH2.              
    apply PTree_combine_ids_defs_match_size_eq in MATCH2.
    destruct MATCH2. auto.
    intros. eapply prog_option_defmap_norepet; eauto.
    eapply link_prog_merge_symm. 
    apply link_unit_symm.
  }
  rewrite H in DSZ2. rewrite <- DSZ2 in DSZ3. clear H DSZ2.
  assert (defs_code_size (map snd (AST.prog_defs p2)) = defs_code_size (map snd defs2)).
  {
    subst. 
    apply PTree_combine_ids_defs_match_symm in MATCH2; eauto.
    unfold collect_internal_def_ids in MATCH2.              
    apply PTree_combine_ids_defs_match_size_eq in MATCH2.
    destruct MATCH2. auto.
    intros. eapply prog_option_defmap_norepet; eauto.
    eapply link_prog_merge_symm.
    apply link_unit_symm.
  }
  rewrite H in CSZ2. rewrite <- CSZ2 in CSZ3. clear H CSZ2.
  clear DSZ1 CSZ1.
  subst.

  assert (symbtable_entry_equiv_sizes s0 0 0 (AST.prog_defs p1)) as SIZES1.
  { 
    unfold collect_internal_def_ids in MATCH1.
    eapply PTree_combine_ids_defs_match_symbtable_entry_sizes; eauto.
    intros. eapply prog_option_defmap_norepet; eauto.
  }
  assert (symbtable_entry_equiv_sizes stbl3 dsz1 csz1 (AST.prog_defs p2)) as SIZES2.
  { 
    unfold collect_internal_def_ids in MATCH2. 
    apply PTree_combine_ids_defs_match_symm in MATCH2.
    eapply PTree_combine_ids_defs_match_symbtable_entry_sizes; eauto.
    intros. eapply prog_option_defmap_norepet; eauto.
    eapply link_prog_merge_symm.
    apply link_unit_symm.
  }

  (** Matching between ids and internal symbols from program 2 *)    
  assert (exists entries, PTree_combine_ids_defs_match 
                       (symbtable_to_tree (rev stbl1)) 
                       (symbtable_to_tree (rev stbl2''))
                       link_symb_merge
                       (collect_internal_def_ids is_fundef_internal p2)
                       entries /\
                     map snd entries = rev stbl3) as MATCH2'.
  { eapply PTree_combine_ids_defs_match_intdefs_comm2
           with (defs1:= (AST.prog_defs p1))
                (defs2:= (AST.prog_defs p2)); eauto. }
  destruct MATCH2' as (stbl4 & MATCH2' & ENTRIES2).
  
  (** Matching between ids and internal symbols from program 1 *)    
  assert (exists entries, PTree_combine_ids_defs_match 
                       (symbtable_to_tree (rev stbl1)) 
                       (symbtable_to_tree (rev stbl2''))
                       link_symb_merge
                       (collect_internal_def_ids is_fundef_internal p1)
                       entries /\
                     map snd entries = rev s0) as MATCH1'.
  { eapply PTree_combine_ids_defs_match_intdefs_comm1
      with (defs1:= (AST.prog_defs p1))
           (defs2:= (AST.prog_defs p2)); eauto. }
  destruct MATCH1' as (stbl5 & MATCH1' & ENTRIES1).
  
  repeat split.

  (** symbtable equiv *)  

  
  (** Finish the proof using the determinacy of PTree_combine_ids_defs_match*)
  repeat rewrite rev_app_distr.
  rewrite <- ENTRIES1.
  rewrite <- ENTRIES2.
  rewrite <- RM_ENTRIES.
  repeat rewrite <- map_app.

  assert (exists (entries : list (ident * symbentry)) (t2 : PTree.t symbentry),
            PTree_extract_elements
              (collect_internal_def_ids is_fundef_internal p1 ++
               collect_internal_def_ids is_fundef_internal p2)
              (PTree.combine link_symb_merge (symbtable_to_tree (rev stbl1))
                 (symbtable_to_tree (rev stbl2''))) = Some (entries, t2)) as EXT'.
  { eapply PTree_extract_elements_exists; eauto.
    eapply PTree_extract_elements_domain_norepet; eauto.
    apply incl_app.
    eapply PTree_combine_ids_defs_match_incl_ids; eauto.
    eapply PTree_combine_ids_defs_match_incl_ids; eauto.
  }
  destruct EXT' as (entries & t2 & EXT').
  do 2 eexists. split; eauto.
  f_equal.
  
  assert (PTree_combine_ids_defs_match 
            (symbtable_to_tree (rev stbl1))
            (symbtable_to_tree (rev stbl2''))
            link_symb_merge
            (collect_internal_def_ids is_fundef_internal p1 ++
             collect_internal_def_ids is_fundef_internal p2)
            entries) as MATCH3.
  { eapply PTree_extract_elements_combine_match; eauto. }
  assert (PTree_combine_ids_defs_match 
            (symbtable_to_tree (rev stbl1))
            (symbtable_to_tree (rev stbl2''))
            link_symb_merge
            (map fst (PTree.elements t2))
            (PTree.elements t2)) as MATCH4.
  { eapply PTree_extract_elements_combine_remain_match; eauto. }
  
  assert (PTree_combine_ids_defs_match 
            (symbtable_to_tree (rev stbl1))
            (symbtable_to_tree (rev stbl2'')) 
            link_symb_merge
            (map fst (PTree.elements t1) ++
             collect_internal_def_ids is_fundef_internal p1 ++
             collect_internal_def_ids is_fundef_internal p2)
            (rm_stbl ++ stbl5 ++ stbl4)) as MATCH5.
  { eapply PTree_combine_ids_defs_match_app; eauto.
    eapply PTree_combine_ids_defs_match_app; eauto. }
  assert (PTree_combine_ids_defs_match 
            (symbtable_to_tree (rev stbl1))
            (symbtable_to_tree (rev stbl2'')) 
            link_symb_merge
            (map fst (PTree.elements t2) ++
             collect_internal_def_ids is_fundef_internal p1 ++
             collect_internal_def_ids is_fundef_internal p2)
            (PTree.elements t2 ++ entries)) as MATCH6.
  { eapply PTree_combine_ids_defs_match_app; eauto. }
  
  assert (map fst (PTree.elements t1) = map fst (PTree.elements t2)) as IDEQ.
  { eapply PTree_extract_elements_remain_keys_eq_link
      with (defs1 := AST.prog_defs p1)
           (defs2 := AST.prog_defs p2); eauto.
    generalize (link_prog_check_link_exists _ _ CHECK).
    intros CH. exact CH.
  }
  rewrite <- IDEQ in MATCH6.
  eapply PTree_combine_ids_defs_match_det; eauto.
Qed.


(* Lemma add_symb_to_list_id_eq: forall stbl id s, *)
(*     In (id, s) (fold_left add_symb_to_list stbl []) -> *)
(*     symbentry_id s = id. *)
(* Proof. *)
(*   induction stbl as [| e stbl]. *)
(*   - cbn. tauto. *)
(*   - cbn. intros id s IN. *)
(*     rewrite add_symb_to_list_inv in IN. *)
(*     rewrite in_app in IN. destruct IN. *)
(*     eauto. *)
(*     unfold add_symb_to_list in H.  *)
(*     inv H; try congruence. inv H0.  *)
(* Qed. *)


Lemma link_symb_pres_id: forall s1 s2 s id,
    symbentry_id s1 = id ->
    symbentry_id s2 = id ->
    link_symb s1 s2 = Some s ->
    symbentry_id s = id.
Proof.
  intros s1 s2 s id ID1 ID2 LINK.
  unfold link_symb in LINK.
  rewrite ID1, ID2 in LINK.
  rewrite peq_true in LINK.
  destr_in LINK; try congruence.
  destr_in LINK; try congruence.
  destr_in LINK; try congruence.
  destruct zeq; try congruence.
  destr_in LINK; try congruence.
  destruct zeq; try congruence.
  destruct zeq; try congruence.
  inv LINK. cbn. congruence.
  destr_in LINK; try congruence. 
  inv LINK. cbn. congruence.
Qed.  

Lemma link_symb_elements_entry_id_eq: forall stbl1 stbl2 id e,
    In (id, e)
       (PTree.elements
          (PTree.combine link_symb_merge
                         (symbtable_to_tree stbl1)
                         (symbtable_to_tree stbl2))) ->
    symbentry_id e = id.
Proof.
  intros stbl1 stbl2 id e IN.
  apply PTree.elements_complete in IN.
  rewrite PTree.gcombine in IN; cbn; auto.
  unfold link_symb_merge in IN.
  destr_in IN. destr_in IN.
  - apply PTree_Properties.in_of_list in Heqo.
    apply PTree_Properties.in_of_list in Heqo0.
    apply symbtable_to_idlist_id_eq in Heqo.
    apply symbtable_to_idlist_id_eq in Heqo0.
    erewrite (link_symb_pres_id s s0); eauto.
    congruence.
  - inv IN.
    apply PTree_Properties.in_of_list in Heqo.
    apply symbtable_to_idlist_id_eq in Heqo.
    rewrite Heqo.
    auto.
  - apply PTree_Properties.in_of_list in IN.
    apply symbtable_to_idlist_id_eq in IN.
    rewrite IN.
    auto.
Qed.


Lemma link_ordered_gen_symb_comm_syneq_size : forall p1 p2 stbl1 stbl2 dsz1 csz1 stbl2' dsz2 csz2 stbl3 dsz3 csz3 t' defs3,
    PTree_Properties.for_all (prog_option_defmap p1) (link_prog_check p1 p2) = true ->
    list_norepet (map fst (AST.prog_defs p1)) ->
    list_norepet (map fst (AST.prog_defs p2)) ->
    gen_symb_table sec_data_id sec_code_id (AST.prog_defs p1) = (stbl1, dsz1, csz1) ->
    gen_symb_table sec_data_id sec_code_id (AST.prog_defs p2) = (stbl2, dsz2, csz2) ->
    reloc_symbtable (reloc_offset_fun dsz1 csz1) stbl2 = Some stbl2' ->
    PTree_extract_elements
      (collect_internal_def_ids is_fundef_internal p1 ++
       collect_internal_def_ids is_fundef_internal p2)
      (PTree.combine link_prog_merge 
                     (prog_option_defmap p1)
                     (prog_option_defmap p2)) = Some (defs3, t') ->
    gen_symb_table sec_data_id sec_code_id (PTree.elements t' ++ defs3) = (stbl3, dsz3, csz3) ->
    dsz3 = dsz1 + dsz2 /\
    csz3 = csz1 + csz2 /\ 
    symbtable_syneq (map snd
                         (PTree.elements
                            (PTree.combine link_symb_merge 
                                           (symbtable_to_tree stbl1)
                                           (symbtable_to_tree stbl2')))) stbl3.
Proof.
  intros until defs3.
  intros CHECK NORPT1 NORPT2 GS1 GS2 RELOC EXT GS3.
  generalize (link_ordered_gen_symb_comm_eq_size _ _ CHECK NORPT1 NORPT2 GS1 GS2 RELOC EXT GS3).
  intros (DSZ & CSZ & (entries & t2 & EXT' & STBL)). subst.
  split; auto.
  split; auto.
  red.
  apply PTree_extract_elements_permutation' in EXT'.
  apply Permutation_map; auto.
Qed.


Lemma reloc_symbtable_pres_ids : forall f stbl stbl',
    reloc_symbtable f stbl = Some stbl' ->
    get_symbentry_ids stbl = get_symbentry_ids stbl'.
Proof.
  induction stbl as [|e stbl].
  - intros stbl' RELOC.
    cbn in RELOC. inv RELOC. cbn. auto.
  - intros stbl' RELOC.
    apply reloc_symbtable_cons_inv in RELOC.
    destruct RELOC as (e' & stbl'' & RELOC & RS & EQ).
    subst.
    cbn.
    unfold reloc_symbol in RS.
    f_equal.
    + repeat destr_in RS. auto.
    + eauto.
Qed.


Lemma link_ordered_gen_symb_comm : forall p1 p2 p stbl1 stbl2 dsz1 csz1 dsz2 csz2 f_ofs,
    link_prog_ordered is_fundef_internal p1 p2 = Some p ->
    gen_symb_table sec_data_id sec_code_id (AST.prog_defs p1) = (stbl1, dsz1, csz1) ->
    gen_symb_table sec_data_id sec_code_id (AST.prog_defs p2) = (stbl2, dsz2, csz2) ->
    f_ofs = reloc_offset_fun dsz1 csz1 ->
    exists stbl stbl2' stbl',
      reloc_symbtable f_ofs stbl2 = Some stbl2' /\
      link_symbtable stbl1 stbl2' = Some stbl /\ 
      gen_symb_table sec_data_id sec_code_id (AST.prog_defs p) = (stbl', dsz1 + dsz2, csz1 + csz2) /\ 
      symbtable_syneq stbl stbl'.
Proof.
  intros until f_ofs. 
  intros LINK GS1 GS2 FOFS.
  unfold link_prog_ordered in LINK.
  destr_in LINK. 
  repeat rewrite andb_true_iff in Heqb.
  destruct Heqb as [[[MAINIDEQ NORPT1] NORPT2] CHK].
  apply proj_sumbool_true in MAINIDEQ.
  apply proj_sumbool_true in NORPT1.
  apply proj_sumbool_true in NORPT2.
  destr_in LINK. destruct p0 as (defs3, t'). 
  inv LINK.
  cbn.

  generalize (reloc_symbtable_exists _ GS2 (eq_refl (reloc_offset_fun dsz1 csz1))).
  intros (stbl2' & RELOC & STBREL).
  generalize NORPT1. intros NORPT1'.
  erewrite gen_symb_table_pres_ids in NORPT1; eauto.
  generalize NORPT2. intros NORPT2'.
  erewrite gen_symb_table_pres_ids in NORPT2; eauto.
  exploit gen_symb_table_pres_link_check; eauto.
  intros SCHK.
  match goal with
  | [ |- context [(gen_symb_table ?a ?b ?c) = _] ] => 
    destruct (gen_symb_table a b c) as (p, csz3) eqn:GST
  end.
  destruct p as (stbl3 & dsz3). 
  generalize (link_ordered_gen_symb_comm_syneq_size _ _ CHK NORPT1' NORPT2' GS1 GS2 RELOC Heqo GST); eauto.
  intros (DSZ & CSZ & SYNEQ). subst.
  do 3 eexists. 
  intuition; eauto.

  unfold link_symbtable.
  repeat rewrite andb_if.
  repeat (setoid_rewrite pred_dec_true; auto).
  rewrite SCHK. eauto.
  erewrite <- reloc_symbtable_pres_ids; eauto. 

Qed.



Lemma transf_program_pres_main: forall p tp,
    transf_program p = OK tp ->
    AST.prog_main p = prog_main tp.
Proof.
  intros p tp TF.
  unfold transf_program in TF.
  destr_in TF. destr_in TF.
  destruct p0. destr_in TF. inv TF. cbn. auto.
Qed.

Lemma transf_program_pres_public: forall p tp,
    transf_program p = OK tp ->
    AST.prog_public p = prog_public tp.
Proof.
  intros p tp TF.
  unfold transf_program in TF.
  destr_in TF. destr_in TF.
  destruct p0. destr_in TF. inv TF. cbn. auto.
Qed.

Lemma transf_program_pres_defs: forall p tp,
    transf_program p = OK tp ->
    AST.prog_defs p = prog_defs tp.
Proof.
  intros p tp TF.
  unfold transf_program in TF.
  destr_in TF. destr_in TF.
  destruct p0. destr_in TF. inv TF. cbn. auto.
Qed.


Lemma match_prog_perm: forall p tp,
    match_prog p tp ->
    PermuteProgSep.match_prog p 
                              {| AST.prog_defs := prog_defs tp;
                                 AST.prog_public := prog_public tp;
                                 AST.prog_main := prog_main tp |}.
Proof.
  intros p tp MATCH.
  red in MATCH.
  destruct MATCH as (tp' & TF & SEQ).
  red in SEQ.
  destruct SEQ as (PERM & MAIN & PUB & STBL & SEQ & STR & RELOC).
  red. cbn.
  split.
  eapply Permutation_trans; [|exact PERM].
  erewrite transf_program_pres_defs; eauto.
  split.
  erewrite transf_program_pres_main; eauto.
  erewrite transf_program_pres_public; eauto.
Qed.

Lemma Exists_Permutation:
  forall A (l1 l2: list A) P, 
    Permutation l1 l2 ->
    Exists P l1 -> Exists P l2.
Proof.
  intros A l1 l2 P PERM EXT.
  rewrite Exists_exists in *.
  destruct EXT as (x & IN & PR).
  assert (In x l2) as IN'.
  { eapply Permutation_in; eauto. }
  eauto.
Qed.

Lemma main_exists_perm: forall p p',
    Permutation (AST.prog_defs p) (AST.prog_defs p') ->
    main_exists (AST.prog_main p) (AST.prog_defs p) ->
    main_exists (AST.prog_main p) (AST.prog_defs p').
Proof.
  intros p p' PERM EXT.
  red in EXT.
  red. eapply Exists_Permutation; eauto.
Qed.

Lemma def_aligned_perm: forall p p',
    Permutation (AST.prog_defs p) (AST.prog_defs p') ->
    Forall def_aligned (map snd (AST.prog_defs p)) ->
    Forall def_aligned (map snd (AST.prog_defs p')).
Proof.
  intros p p' PERM ALIGN.
  rewrite Forall_forall in *.
  intros x IN.
  eapply ALIGN; eauto.
  apply list_in_map_inv in IN.
  destruct IN as (x' & EQ & IN').
  subst.
  apply in_map.
  apply Permutation_sym in PERM. 
  eapply Permutation_in; eauto.
Qed.

Lemma def_instrs_valid_perm: forall p p',
    Permutation (AST.prog_defs p) (AST.prog_defs p') ->
    Forall def_instrs_valid (map snd (AST.prog_defs p)) ->
    Forall def_instrs_valid (map snd (AST.prog_defs p')).
Proof.
  intros p p' PERM ALIGN.
  rewrite Forall_forall in *.
  intros x IN.
  eapply ALIGN; eauto.
  apply list_in_map_inv in IN.
  destruct IN as (x' & EQ & IN').
  subst.
  apply in_map.
  apply Permutation_sym in PERM. 
  eapply Permutation_in; eauto.
Qed.

Lemma data_size_aligned_perm: forall p p',
    Permutation (AST.prog_defs p) (AST.prog_defs p') ->
    Forall data_size_aligned (map snd (AST.prog_defs p)) ->
    Forall data_size_aligned (map snd (AST.prog_defs p')).
Proof.
  intros p p' PERM ALIGN.
  rewrite Forall_forall in *.
  intros x IN.
  eapply ALIGN; eauto.
  apply list_in_map_inv in IN.
  destruct IN as (x' & EQ & IN').
  subst.
  apply in_map.
  apply Permutation_sym in PERM. 
  eapply Permutation_in; eauto.
Qed.

Lemma wf_prog_perm: forall p p',
    Permutation (AST.prog_defs p) (AST.prog_defs p') ->
    AST.prog_main p = AST.prog_main p' ->
    wf_prog p ->
    wf_prog p'.
Proof.
  intros p p' PERM EQ WF.
  inv WF. constructor.
  - eapply Permutation_list_norepet_map; eauto.
  (* - rewrite <- EQ. *)
  (*   eapply main_exists_perm; eauto. *)
  - eapply def_aligned_perm; eauto.
  - eapply def_instrs_valid_perm; eauto.
  - eapply data_size_aligned_perm; eauto.
Qed.

Lemma main_exists_combine: 
  forall id p1 p2,
    prog_linkable p1 p2 ->
    list_norepet (map fst (AST.prog_defs p1)) ->
    list_norepet (map fst (AST.prog_defs p2)) ->
    main_exists id (AST.prog_defs p1) ->
    main_exists id (AST.prog_defs p2) ->
    main_exists id (PTree.elements
                      (PTree.combine link_prog_merge
                                     (PTree_Properties.of_list (AST.prog_defs p1))
                                     (PTree_Properties.of_list (AST.prog_defs p2)))).
Proof.
  intros id p1 p2 LA NORPT1 NORPT2 E1 E2.
  red in E1, E2.
  red.
  rewrite Exists_exists in *.
  destruct E1 as ((id1, def1) & IN1 & EQ1 & DE1).
  destruct def1 as [def1 |]; try contradiction.
  destruct E2 as ((id2, def2) & IN2 & EQ2 & DE2).
  destruct def2 as [def2 |]; try contradiction.
  subst.
  generalize (PTree.gcombine _ link_prog_merge_none 
                             (PTree_Properties.of_list (AST.prog_defs p1))
                             (PTree_Properties.of_list (AST.prog_defs p2)) id2).
  intros GET.
  generalize (PTree_Properties.of_list_norepet _ _ _ NORPT1 IN1).
  intros GET1.
  generalize (PTree_Properties.of_list_norepet _ _ _ NORPT2 IN2).
  intros GET2.
  rewrite GET1, GET2 in GET.
  red in LA.
  generalize (LA id2 _ _ GET1 GET2).
  intros (INP1 & INP2 & gd & LINK').
  cbn in GET, LINK'. rewrite LINK' in GET.
  apply PTree.elements_correct in GET.
  exists (id2, gd). split; auto. split; auto.
  destr_in LINK'; try congruence. inv LINK'. auto.
Qed.

Hint Resolve link_prog_linkable.


Lemma def_aligned_combine: 
  forall defs1 defs2,
    Forall def_aligned (map snd defs1) ->
    Forall def_aligned (map snd defs2) ->
    Forall def_aligned 
           (map snd (PTree.elements
                       (PTree.combine link_prog_merge
                                      (PTree_Properties.of_list defs1)
                                      (PTree_Properties.of_list defs2)))).
Proof.
  intros defs1 defs2 AL1 AL2.
  rewrite Forall_forall in *.
  intros def IN.
  rewrite in_map_iff in IN.
  destruct IN as ((id, def') & EQ & IN). cbn in EQ. subst def'.
  apply PTree.elements_complete in IN.
  erewrite PTree.gcombine in IN; eauto.
  unfold link_prog_merge in IN.
  destr_in IN. destr_in IN.
  - apply PTree_Properties.in_of_list in Heqo.
    apply PTree_Properties.in_of_list in Heqo0.
    apply (in_map snd) in Heqo. cbn in Heqo.
    apply (in_map snd) in Heqo0. cbn in Heqo0.
    apply AL1 in Heqo.
    apply AL2 in Heqo0.
    apply link_pres_aligned with (def1:= o) (def2 := o0); eauto.
  - inv IN.
    apply PTree_Properties.in_of_list in Heqo.
    apply (in_map snd) in Heqo. cbn in Heqo.
    eauto.
  - apply PTree_Properties.in_of_list in IN.
    apply (in_map snd) in IN. cbn in IN.
    eauto.
Qed.


Lemma link_option_internal_external_pres_instrs_validity :
  forall def1 def2 def,
    is_def_internal is_fundef_internal def2 = false ->
    def_instrs_valid def1 -> link_option def1 def2 = Some def -> 
    def_instrs_valid def.
Proof.
  intros def1 def2 def INT ALIGN LINK.
  destruct def2. destruct g. destruct f; cbn in *; try congruence.
  - destruct def1. destruct g. destruct f. 
    + cbn in LINK. destr_in LINK; try congruence. inv LINK.
      destr_in Heqo; try congruence; inv Heqo.
      destruct e; try congruence. 
    + cbn in LINK. destr_in LINK; try congruence. inv LINK.
      destr_in Heqo; try congruence; inv Heqo.
      destr_in Heqo0; try congruence. 
    + cbn in LINK. congruence.
    + cbn in LINK. inv LINK. auto.
  - destruct def1. destruct g.
    + cbn in *. congruence.
    + cbn in LINK. destr_in LINK; try congruence.
      destr_in Heqo; try congruence. inv Heqo. inv LINK.
      cbn in INT.
      red. auto.
    + cbn in *. inv LINK. auto.
  - destruct def1. cbn in LINK. inv LINK. auto.
    cbn in *. inv LINK. auto.
Qed.
  

Lemma link_pres_instrs_validity :
  forall def1 def2 def : option (globdef fundef unit),
    def_instrs_valid def1 -> def_instrs_valid def2 -> 
    link def1 def2 = Some def -> def_instrs_valid def.
Proof.
  intros def1 def2 def AL1 AL2 LINK.
  cbn in LINK.
  destruct (is_def_internal is_fundef_internal def1) eqn:INT1.
  - generalize (link_int_defs_some_inv _ _ INT1 LINK).
    intros INT2.
    apply link_option_internal_external_pres_instrs_validity
      with (def1 := def1) (def2 := def2); eauto.
  - setoid_rewrite link_option_symm in LINK; eauto.
    apply link_option_internal_external_pres_instrs_validity
      with (def1 := def2) (def2 := def1); eauto.
Qed.
  

Lemma def_instrs_valid_combine: 
  forall defs1 defs2,
    Forall def_instrs_valid (map snd defs1) ->
    Forall def_instrs_valid (map snd defs2) ->
    Forall def_instrs_valid 
           (map snd (PTree.elements
                       (PTree.combine link_prog_merge
                                      (PTree_Properties.of_list defs1)
                                      (PTree_Properties.of_list defs2)))).
Proof.
  intros defs1 defs2 AL1 AL2.
  rewrite Forall_forall in *.
  intros def IN.
  rewrite in_map_iff in IN.
  destruct IN as ((id, def') & EQ & IN). cbn in EQ. subst def'.
  apply PTree.elements_complete in IN.
  erewrite PTree.gcombine in IN; eauto.
  unfold link_prog_merge in IN.
  destr_in IN. destr_in IN.
  - apply PTree_Properties.in_of_list in Heqo.
    apply PTree_Properties.in_of_list in Heqo0.
    apply (in_map snd) in Heqo. cbn in Heqo.
    apply (in_map snd) in Heqo0. cbn in Heqo0.
    apply AL1 in Heqo.
    apply AL2 in Heqo0.    
    apply link_pres_instrs_validity with (def1:= o) (def2 := o0); eauto.
  - inv IN.
    apply PTree_Properties.in_of_list in Heqo.
    apply (in_map snd) in Heqo. cbn in Heqo.
    eauto.
  - apply PTree_Properties.in_of_list in IN.
    apply (in_map snd) in IN. cbn in IN.
    eauto.
Qed.

Lemma eq_gvar_init_pres_data_size_aligned : forall v1 v2,
    gvar_init v1 = gvar_init v2 
    -> data_size_aligned (Some (Gvar v1))
    -> data_size_aligned (Some (Gvar v2)).
Proof.
  intros. red in H0. red.
  cbn in *. rewrite <- H. auto.
Qed.

Hint Resolve alignw0.

Lemma link_varinit_internal_external_pres_data_size_aligned:
  forall (v1 v2: globvar unit) l inf rd vl,
    is_var_internal v2 = false
    -> data_size_aligned (Some (Gvar v1))
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some l
    -> data_size_aligned (Some (Gvar (mkglobvar inf l rd vl))).
Proof.
  intros v1 v2 l inf rd vl INT2 ALIGN LINK.
  destruct (is_var_internal v1) eqn:INT1.
  - generalize (link_internal_external_varinit _ _ _ INT1 INT2 LINK).
    destruct 1 as (EQ & CLS). subst.   
    apply eq_gvar_init_pres_data_size_aligned with v1; auto.
  - generalize (link_external_varinit _ _ _ INT1 INT2 LINK).
    intros CLS.
    destruct l. red. cbn. auto.
    cbn in *. destruct i; try congruence.
    destruct l; try congruence. 
    red. cbn. auto.
Qed.


Lemma link_vardef_internal_external_pres_data_size_aligned:
  forall v1 v2 v,
    is_var_internal v2 = false
    -> data_size_aligned (Some (Gvar v1))
    -> link_vardef v1 v2 = Some v
    -> data_size_aligned (Some (Gvar v)).
Proof.
  intros v1 v2 v INT ALIGN LINK.
  unfold link_vardef in LINK. 
  destr_in LINK; try congruence.
  destr_in LINK; try congruence.
  destr_in LINK; try congruence.
  inv LINK. unfold is_var_internal in INT.
  eapply link_varinit_internal_external_pres_data_size_aligned; eauto.
Qed.
  

Lemma external_var_data_size_aligned: forall v,
    is_var_internal v = false -> data_size_aligned (Some (Gvar v)).
Proof.
  intros v INT. red. cbn.
  unfold is_var_internal in INT.
  cbn. destruct (gvar_init v); cbn in *; try congruence.
  auto.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
  auto.
Qed.


Lemma link_option_internal_external_pres_data_size_aligned: forall def1 def2 def,
    is_def_internal is_fundef_internal def2 = false
    -> data_size_aligned def1
    -> link_option def1 def2 = Some def
    -> data_size_aligned def.
Proof.
  intros def1 def2 def INT ALIGN LINK.
  destruct def2. destruct g. destruct f; cbn in *; try congruence.
  - destruct def1. destruct g. destruct f. 
    + cbn in LINK. destr_in LINK; try congruence. inv LINK.
      destr_in Heqo; try congruence; inv Heqo.
      destruct e; try congruence. 
    + cbn in LINK. destr_in LINK; try congruence. inv LINK.
      destr_in Heqo; try congruence; inv Heqo.
      destr_in Heqo0; try congruence. 
    + cbn in LINK. congruence.
    + cbn in LINK. inv LINK. auto.
  - destruct def1. destruct g.
    + cbn in *. congruence.
    + cbn in LINK. destr_in LINK; try congruence.
      destr_in Heqo; try congruence. inv Heqo. inv LINK.
      cbn in INT.
      eapply link_vardef_internal_external_pres_data_size_aligned; eauto.
    + cbn in *. inv LINK.       
      eapply external_var_data_size_aligned; eauto.
  - destruct def1. cbn in LINK. inv LINK. auto.
    cbn in *. inv LINK. auto.
Qed.

Lemma link_pres_data_size_aligned :
  forall def1 def2 def : option (globdef fundef unit),
    data_size_aligned def1 -> data_size_aligned def2 -> 
    link def1 def2 = Some def -> data_size_aligned def.
Proof.
  intros def1 def2 def AL1 AL2 LINK.
  cbn in LINK.
  destruct (is_def_internal is_fundef_internal def1) eqn:INT1.
  - generalize (link_int_defs_some_inv _ _ INT1 LINK).
    intros INT2.
    apply link_option_internal_external_pres_data_size_aligned
      with (def1 := def1) (def2 := def2); eauto.
  - setoid_rewrite link_option_symm in LINK; eauto.
    apply link_option_internal_external_pres_data_size_aligned
      with (def1 := def2) (def2 := def1); eauto.
Qed.

Lemma data_size_aligned_combine: 
  forall defs1 defs2,
    Forall data_size_aligned (map snd defs1) ->
    Forall data_size_aligned (map snd defs2) ->
    Forall data_size_aligned
           (map snd (PTree.elements
                       (PTree.combine link_prog_merge
                                      (PTree_Properties.of_list defs1)
                                      (PTree_Properties.of_list defs2)))).
Proof.
  intros defs1 defs2 AL1 AL2.
  rewrite Forall_forall in *.
  intros def IN.
  rewrite in_map_iff in IN.
  destruct IN as ((id, def') & EQ & IN). cbn in EQ. subst def'.
  apply PTree.elements_complete in IN.
  erewrite PTree.gcombine in IN; eauto.
  unfold link_prog_merge in IN.
  destr_in IN. destr_in IN.
  - apply PTree_Properties.in_of_list in Heqo.
    apply PTree_Properties.in_of_list in Heqo0.
    apply (in_map snd) in Heqo. cbn in Heqo.
    apply (in_map snd) in Heqo0. cbn in Heqo0.
    apply AL1 in Heqo.
    apply AL2 in Heqo0.    
    apply link_pres_data_size_aligned with (def1:= o) (def2 := o0); eauto.
  - inv IN.
    apply PTree_Properties.in_of_list in Heqo.
    apply (in_map snd) in Heqo. cbn in Heqo.
    eauto.
  - apply PTree_Properties.in_of_list in IN.
    apply (in_map snd) in IN. cbn in IN.
    eauto.
Qed.


Lemma link_prog_pres_wf_prog: forall p1 p2 p,
    link_prog p1 p2 = Some p ->
    wf_prog p1 ->
    wf_prog p2 ->
    wf_prog p.
Proof.
  intros p1 p2 p LINK WF1 WF2.
  generalize (link_prog_linkable _ _ _ LINK).
  intros LA.
  unfold link_prog in LINK.
  destr_in LINK. inv LINK. 
  repeat rewrite andb_true_iff in Heqb.
  destruct Heqb as (((MAINEQ & NORPT1) & NORPT2) & PALL).
  destruct ident_eq; try inv MAINEQ.
  destruct list_norepet_dec; try inv NORPT1.
  destruct list_norepet_dec; try inv NORPT2.
  inv WF1. inv WF2.
  constructor; cbn.
  - apply PTree.elements_keys_norepet.
  (* - rewrite e in *. *)
  (*   eapply main_exists_combine; eauto. *)
  - eapply def_aligned_combine; eauto.
  - eapply def_instrs_valid_combine; eauto.
  - eapply data_size_aligned_combine; eauto.
Qed.

Lemma link_ordered_prog_pres_wf_prog: forall p1 p2 p,
    link_prog_ordered is_fundef_internal p1 p2 = Some p ->
    wf_prog p1 ->
    wf_prog p2 ->
    wf_prog p.
Proof.
  intros p1 p2 p LINK WF1 WF2.
  edestruct (link_prog_ordered_inv' p1 p2 p) as (p' & LINK' & MAIN & PERM); eauto.
  apply Permutation_sym in PERM.
  eapply wf_prog_perm; eauto.
  eapply link_prog_pres_wf_prog; eauto.
Qed.  
  


Lemma reloc_symbtable_pres_syneq : forall f tbl1 tbl1' tbl2 ,
    reloc_symbtable f tbl1 = Some tbl2 ->
    symbtable_syneq tbl1 tbl1' ->
    exists tbl2', reloc_symbtable f tbl1' = Some tbl2' /\
             symbtable_syneq tbl2 tbl2'.
Proof.
  induction tbl1 as [|e tbl1].
  - cbn. intros tbl' tbl2 RELOC SEQ.
    inv RELOC.
    red in SEQ.
    apply Permutation_nil in SEQ. subst.
    exists nil. split; eauto.
    apply perm_nil.
  - intros tbl1' tbl2 RELOC SEQ.
    apply reloc_symbtable_cons_inv in RELOC.
    destruct RELOC as (e' & stbl3 & RELOC & RE & EQ). subst.
    red in SEQ.
    generalize (Permutation_in _ SEQ (in_eq e tbl1)).
    intros IN.
    apply in_split in IN.
    destruct IN as (l1 & l2 & EQ). subst.
    apply Permutation_cons_app_inv in SEQ.
    generalize (IHtbl1 _ _ RELOC SEQ).
    intros (tbl2' & RELOC' & SEQ').
    apply reloc_symbtable_app_inv in RELOC'.
    destruct RELOC' as (l1' & l2' & EQ & RELOC1 & RELOC2). subst.
    exists (l1' ++ e' :: l2'). split.
    apply reloc_symbtable_app; auto.
    apply reloc_symbtable_cons; auto.
    red. apply Permutation_cons_app; auto.
Qed.

Lemma symbtable_to_tree_permutation_some: forall stbl stbl' id a,
    list_norepet (get_symbentry_ids stbl) ->
    Permutation stbl stbl' ->
    (symbtable_to_tree stbl) ! id = Some a ->
    (symbtable_to_tree stbl') ! id = Some a.
Proof.
  unfold symbtable_to_tree.
  intros stbl stbl' id a NORPT PERM ALL.
  apply Permutation_pres_ptree_get_some with
      (symbtable_to_idlist stbl); eauto.
  rewrite <- get_symbentry_ids_add_symb_eq. auto.
  apply symbtable_to_idlist_permutation; auto.
Qed.

Lemma symbtable_to_tree_permutation_none: forall stbl stbl' id,
    Permutation stbl stbl' ->
    (symbtable_to_tree stbl) ! id = None ->
    (symbtable_to_tree stbl') ! id = None.
Proof.
  unfold symbtable_to_tree.
  intros stbl stbl' id PERM ALL.
  apply Permutation_pres_ptree_get_none with
      (symbtable_to_idlist stbl); eauto.
  apply symbtable_to_idlist_permutation; eauto.
Qed.

Lemma link_symbtable_check_permutation: forall stbl stbl' id a,
    list_norepet (get_symbentry_ids stbl) ->
    Permutation stbl stbl' ->
    link_symbtable_check (symbtable_to_tree stbl) id a = true ->
    link_symbtable_check (symbtable_to_tree stbl') id a = true.
Proof.
  unfold link_symbtable_check.
  intros stbl stbl' id a NORPT PERM CHK.
  destr_in CHK.
  erewrite symbtable_to_tree_permutation_some; eauto.
  erewrite symbtable_to_tree_permutation_none; eauto.
Qed.


Lemma link_symbtable_check_all_perm: forall stbl1 stbl2 stbl1' stbl2',
    list_norepet (get_symbentry_ids stbl1) ->
    list_norepet (get_symbentry_ids stbl2) ->
    PTree_Properties.for_all (symbtable_to_tree stbl1)
                             (link_symbtable_check (symbtable_to_tree stbl2)) = true ->
    Permutation stbl1 stbl1' ->
    Permutation stbl2 stbl2' ->
    PTree_Properties.for_all (symbtable_to_tree stbl1')
                             (link_symbtable_check (symbtable_to_tree stbl2')) = true.
Proof.
  intros stbl1 stbl2 stbl1' stbl2' NORPT1 NORPT2 ALL PERM1 PERM2.
  rewrite PTree_Properties.for_all_correct in ALL.
  rewrite PTree_Properties.for_all_correct.
  intros id a GET.
  generalize (get_symbentry_ids_permutation _ _ PERM1).
  intros PERM3.
  apply Permutation_sym in PERM1.
  generalize (Permutation_pres_list_norepet _ _ _ NORPT1 PERM3).
  intros NORPT1'.
  generalize (symbtable_to_tree_permutation_some id NORPT1' PERM1 GET).
  intros GET'.
  apply ALL in GET'.
  apply link_symbtable_check_permutation with stbl2; eauto.
Qed.
    

Lemma link_symbtable_permutation: forall stbl1 stbl2 stbl stbl1' stbl2',
    link_symbtable stbl1 stbl2 = Some stbl ->
    Permutation stbl1 stbl1' ->
    Permutation stbl2 stbl2' ->
    exists stbl', 
      link_symbtable stbl1' stbl2' = Some stbl' /\
      Permutation stbl stbl'.
Proof.
  intros stbl1 stbl2 stbl stbl1' stbl2' LINK PERM1 PERM2.
  unfold link_symbtable in LINK.
  destr_in LINK. inv LINK.
  repeat rewrite andb_true_iff in Heqb.
  destruct Heqb as ((NORPT1 & NORPT2) & ALL).
  destruct list_norepet_dec; try inv NORPT1.
  destruct list_norepet_dec; try inv NORPT2.
  unfold link_symbtable.
  assert (list_norepet_dec ident_eq (get_symbentry_ids stbl1') &&
                           list_norepet_dec ident_eq (get_symbentry_ids stbl2') &&
                           PTree_Properties.for_all (symbtable_to_tree stbl1')
                           (link_symbtable_check (symbtable_to_tree stbl2')) = true) as COND.  
  {
    repeat rewrite andb_true_iff. split. split.
    - apply proj_sumbool_is_true.
      apply Permutation_pres_list_norepet with 
          (get_symbentry_ids stbl1); eauto.
      eapply get_symbentry_ids_permutation; eauto.
    - apply proj_sumbool_is_true.
      apply Permutation_pres_list_norepet with 
          (get_symbentry_ids stbl2); eauto.
      eapply get_symbentry_ids_permutation; eauto.
    - apply link_symbtable_check_all_perm with stbl1 stbl2; eauto.
  }
  rewrite COND.
  repeat rewrite andb_true_iff in COND.
  destruct COND as ((NORPT1' & NORPT2') & ALL').
  destruct list_norepet_dec; try inv NORPT1'.
  destruct list_norepet_dec; try inv NORPT2'.
  eexists; split; eauto.
  unfold symbtable_to_tree.
  apply Permutation_map.
  apply PTree_combine_permutation; auto.
  - apply symbtable_to_idlist_permutation; auto.
  - apply symbtable_to_idlist_permutation; auto.
  - rewrite get_symbentry_ids_add_symb_eq in l1.
    apply list_norepet_rev in l1.
    apply Permutation_pres_list_norepet with 
        (map fst (symbtable_to_idlist stbl1')); auto.
    apply list_norepet_rev; eauto.
    apply Permutation_map. 
    eapply symbtable_to_idlist_permutation; eauto.
    apply Permutation_sym. auto.
  - rewrite get_symbentry_ids_add_symb_eq in l2.
    apply list_norepet_rev in l2.
    apply Permutation_pres_list_norepet with 
        (map fst (symbtable_to_idlist stbl2')); auto.
    apply list_norepet_rev; eauto.
    apply Permutation_map.     
    eapply symbtable_to_idlist_permutation; eauto.
    apply Permutation_sym. auto.
Qed.
  

Lemma link_symbtable_pres_syneq: forall stbl1 stbl2 stbl stbl1' stbl2',
    link_symbtable stbl1 stbl2 = Some stbl ->
    symbtable_syneq stbl1 stbl1' ->
    symbtable_syneq stbl2 stbl2' ->
    exists stbl', 
      link_symbtable stbl1' stbl2' = Some stbl' /\
      symbtable_syneq stbl stbl'.
Proof.
  intros stbl1 stbl2 stbl stbl1' stbl2' LINK EQ1 EQ2.
  eapply link_symbtable_permutation; eauto.
Qed.


(** ** Main linking theorem *)
Lemma link_transf_symbtablegen : forall (p1 p2 : Asm.program) (tp1 tp2 : program) (p : Asm.program),
    link p1 p2 = Some p -> match_prog p1 tp1 -> match_prog p2 tp2 ->
    exists tp : program, link tp1 tp2 = Some tp /\ match_prog p tp.
Proof.
  intros p1 p2 tp1 tp2 p LINK MATCH1 MATCH2.
  unfold link in LINK.
  unfold Linker_prog_ordered in LINK.
  unfold link. unfold Linker_reloc_prog. unfold link_reloc_prog.
  generalize (match_prog_perm MATCH1). intros OMATCH1.
  generalize (match_prog_perm MATCH2). intros OMATCH2.
  generalize (@transf_link _ _ _ _ _ TransfPermuteOrderedLink2 
                           _ _ _ _ _ LINK OMATCH1 OMATCH2).
  intros (tp3 & LINK3 & OMATCH). clear OMATCH1 OMATCH2.
  setoid_rewrite LINK3.
  
  red in MATCH1, MATCH2.
  destruct MATCH1 as (tp1' & TRANSF1 & RPEQ1).
  destruct MATCH2 as (tp2' & TRANSF2 & RPEQ2).
  
  unfold transf_program in TRANSF1.
  destruct check_wellformedness; try monadInv TRANSF1.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p1)) as (s & csz1) eqn:GSEQ1 .
  destruct s as (stbl1 & dsz1).
  destruct zle; try monadInv TRANSF1; simpl.

  unfold transf_program in TRANSF2.
  destruct check_wellformedness; try monadInv TRANSF2.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p2)) as (s & csz2) eqn:GSEQ2 .
  destruct s as (stbl2 & dsz2).
  destruct zle; try monadInv TRANSF2; simpl.

  red in RPEQ1. cbn in RPEQ1.
  destruct RPEQ1 as (PERM1 & MAINEQ1 & PUBEQ1 & SECTBLEQ1 & 
                     SYMTBLEQ1 & STRTBLEQ1 & RELOCTBLEQ1).
  red in RPEQ2. cbn in RPEQ2.
  destruct RPEQ2 as (PERM2 & MAINEQ2 & PUBEQ2 & SECTBLEQ2 & 
                     SYMTBLEQ2 & STRTBLEQ2 & RELOCTBLEQ2).

  rewrite <- SECTBLEQ1.
  unfold create_sec_table; cbn. unfold Pos.to_nat; cbn. 
  rewrite <- SECTBLEQ2.
  unfold create_sec_table.
  unfold link_sectable; cbn. unfold Pos.to_nat; cbn.
  
  simpl in LINK.
  generalize (link_prog_ordered_inv is_fundef_internal _ _ _ LINK). 
  intros (NRPT1 & NRPT2).

  generalize (link_ordered_gen_symb_comm _ _ LINK GSEQ1 GSEQ2
                                 (@eq_refl _ (reloc_offset_fun dsz1 csz1))); eauto.
  destruct 1 as (stbl & stbl2' & stbl' & RELOC & LINKS & GENS & STEQ).
  generalize (gen_symb_table_size _ _ _ _ _ _ GSEQ1).
  destruct 1 as (DSZ & CSZ).
  setoid_rewrite DSZ.
  setoid_rewrite CSZ.
  edestruct reloc_symbtable_pres_syneq as (stbl3 & RELOC1 & STBLEQ); eauto.
  rewrite RELOC1.
  edestruct link_symbtable_pres_syneq as (stbl4 & LINKS' & STBLEQ1); eauto.
  rewrite LINKS'.

  eexists. split. reflexivity.
  red.
  unfold transf_program.
  exploit link_ordered_prog_pres_wf_prog; eauto.
  intros WF.
  destruct check_wellformedness; try congruence.
  simpl. 
  setoid_rewrite GENS.
  
  destruct zle.
  eexists; split. reflexivity.
  red; cbn.

  split. red in OMATCH. tauto.
  split. red in OMATCH. tauto.
  split. red in OMATCH. tauto.
  split. 
  unfold create_sec_table. repeat f_equal.
  unfold create_data_section. f_equal.
  apply link_acc_init_data_comm; auto.
  unfold create_code_section. f_equal.
  apply link_acc_instrs_comm; auto.
  split.
  eapply symbtable_syneq_trans. 
  apply symbtable_syneq_symm. eauto. eauto.
  split. congruence.
  congruence.
  generalize (defs_size_inbound (AST.prog_defs p)).
  intros; omega.
Qed.


Instance TransfLinkSymbtablegen : TransfLink match_prog :=
  link_transf_symbtablegen.
