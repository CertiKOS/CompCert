Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Asm RelocProgram.
Require Import Symbtablegen.
Require Import Linking LinkingProp.
Require Import RelocLinking.
Require Import SeqTable.
Require Import RelationClasses.
Import ListNotations.

Set Implicit Arguments.

(** * Commutativity of linking and Symbtablgen *)

Definition match_prog (p: Asm.program) (tp: program) :=
  transf_program p = OK tp.

Lemma link_prog_inv: forall (F V: Type) (fi:F -> bool) (LF: Linker F) (LV: Linker V) (p1 p2 p: AST.program F V), 
    link_prog fi p1 p2 = Some p ->
    (AST.prog_main p1 = AST.prog_main p2)
    /\ list_norepet (map fst (AST.prog_defs p1))
    /\ list_norepet (map fst (AST.prog_defs p2))
    /\ exists defs, 
        p = {| AST.prog_defs := defs; 
               AST.prog_public := AST.prog_public p1 ++ AST.prog_public p2; 
               AST.prog_main := AST.prog_main p1 |}
        /\ link_defs fi (AST.prog_defs p1) (AST.prog_defs p2) = Some defs.
Proof.
  intros F V fi LF LV p1 p2 p LINK.
  unfold link_prog in LINK.
  destruct ident_eq; simpl in LINK.
  unfold prog_unique_idents in LINK.
  repeat (destruct list_norepet_dec; simpl in LINK).
  destr_in LINK; inv LINK. 
  repeat split; auto. eauto.
  congruence.
  congruence.
  congruence.
Qed.


Lemma match_prog_pres_prog_defs : forall p tp,
  match_prog p tp -> AST.prog_defs p = prog_defs tp.
Proof.
  intros p tp MATCH. red in MATCH.
  unfold transf_program in MATCH.
  destruct check_wellformedness; try monadInv MATCH.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p)) eqn:EQ.
  destruct p0. 
  destruct zle; try monadInv MATCH. simpl. auto.
Qed.

Lemma match_prog_pres_prog_main : forall p tp,
  match_prog p tp -> AST.prog_main p = prog_main tp.
Proof.
  intros p tp MATCH. red in MATCH.
  unfold transf_program in MATCH.
  destruct check_wellformedness; try monadInv MATCH.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p)) eqn:EQ.
  destruct p0. 
  destruct zle; try monadInv MATCH. simpl. auto.
Qed.

Lemma match_prog_pres_prog_public : forall p tp,
  match_prog p tp -> AST.prog_public p = prog_public tp.
Proof.
  intros p tp MATCH. red in MATCH.
  unfold transf_program in MATCH.
  destruct check_wellformedness; try monadInv MATCH.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p)) eqn:EQ.
  destruct p0. 
  destruct zle; try monadInv MATCH. simpl. auto.
Qed.


(** ** Commutativity of linking and generation of the symbol table *)
(* Lemma link_defs_acc_symb_comm : forall defs1 defs2 defs rstbl1 dsz1 csz1 rstbl2 dsz2 csz2, *)
(*       link_defs_aux is_fundef_internal defs1 defs2 postponed = Some defs -> *)
(*       fold_left (acc_symb sec_data_id sec_code_id) defs1 (entries1', dsz1', csz1') = (entries1 ++ entries1', dsz1, csz1) -> *)
(*       fold_left (acc_symb sec_data_id sec_code_id) defs2 (entries2', dsz2', csz2') = (entries2 ++ entries2', dsz2, csz2) -> *)
(*       exists stbl,  *)
(*         link_symbtable_aux (reloc_offset_fun' dsz1 csz1) *)
(*                            (rev entries1) *)
(*                            (rev entries2) *)
(*                             = Some stbl /\ *)
(*         fold_left (acc_symb sec_data_id sec_code_id) defs ([dummy_symbentry], 0, 0) =  *)
(*         (rev stbl, dsz1 + dsz2, csz1 + csz2). *)
(* Proof. *)
(*   intros defs1 defs2 defs rstbl1 dsz1 csz1 rstbl2 dsz2 csz2 LINK ACC1 ACC2. *)
(*   unfold link_symbtable. *)


(* Lemma link_defs_acc_symb_comm : forall defs1 defs2 defs rstbl1 dsz1 csz1 rstbl2 dsz2 csz2, *)
(*       link_defs_aux is_fundef_internal defs1 defs2 [] = Some defs -> *)
(*       fold_left (acc_symb sec_data_id sec_code_id) defs1 ([dummy_symbentry], 0, 0) = (rstbl1, dsz1, csz1) -> *)
(*       fold_left (acc_symb sec_data_id sec_code_id) defs2 ([dummy_symbentry], 0, 0) = (rstbl2, dsz2, csz2) -> *)
(*       exists stbl,  *)
(*         link_symbtable (reloc_offset_fun (create_data_section defs1) (create_code_section defs1))  *)
(*                        (rev rstbl1) (rev rstbl2) = Some stbl /\ *)
(*         fold_left (acc_symb sec_data_id sec_code_id) defs ([dummy_symbentry], 0, 0) =  *)
(*         (rev stbl, dsz1 + dsz2, csz1 + csz2). *)
(* Proof. *)
(*   induction defs1 as [| def defs1']. *)
(*   - intros defs2 defs rstbl1 dsz1 csz1 rstbl2 dsz2 csz2 LINK ACC1 ACC2. *)
(*     simpl in *. inv LINK. inv ACC1. *)
(*     simpl. *)
(*     admit. *)
(*   - intros defs2 defs rstbl1 dsz1 csz1 rstbl2 dsz2 csz2 LINK ACC1 ACC2. *)
(*     simpl in *. destruct def as (id1 & def1). *)
(*     destruct (partition (fun '(id', _) => ident_eq id' id1) defs2) as (defs2' & defs2'') eqn:PART. *)
(*     destruct defs2' as [| def2 defs2''']. *)
    

(*   intros defs1 defs2 defs rstbl1 dsz1 csz1 rstbl2 dsz2 csz2  *)
(*   unfold link_symbtable. *)



Definition symbentry_index_in_range range e :=
  match symbentry_secindex e with
  | secindex_normal i => In i range
  | _ => True
  end.

Definition symbtable_indexes_in_range range t :=
  Forall (symbentry_index_in_range range) t.

Lemma gen_symb_table_index_in_range : forall defs sec_data_id sec_code_id stbl dsz csz,
    gen_symb_table sec_data_id sec_code_id defs = (stbl, dsz, csz) ->
    symbtable_indexes_in_range (map SecIndex.interp [sec_data_id; sec_code_id]) stbl.
Admitted.

Lemma reloc_symbtable_exists : forall stbl f dsz csz,
    symbtable_indexes_in_range (map SecIndex.interp [sec_data_id; sec_code_id]) stbl ->
    f = (reloc_offset_fun dsz csz) ->
    exists stbl', reloc_symbtable f stbl = Some stbl' /\
             Forall2 (fun e1 e2 => reloc_symb f e1 = Some e2) stbl stbl'.
Admitted.


Lemma link_gen_symb_comm : forall defs1 defs2 defs stbl1 stbl2 dsz1 csz1 dsz2 csz2 f_ofs,
    link_defs is_fundef_internal defs1 defs2 = Some defs ->
    gen_symb_table sec_data_id sec_code_id defs1 = (stbl1, dsz1, csz1) ->
    gen_symb_table sec_data_id sec_code_id defs2 = (stbl2, dsz2, csz2) ->
    f_ofs = reloc_offset_fun dsz1 csz1 ->
    exists stbl stbl2',
      reloc_symbtable f_ofs stbl2 = Some stbl2' /\
      link_symbtable stbl1 stbl2' = Some stbl
      /\ gen_symb_table sec_data_id sec_code_id defs = (stbl, dsz1 + dsz2, csz1 + csz2).
Proof.
Admitted.
(*   intros defs1 defs2 defs stbl1 stbl2 dsz1 csz1 dsz2 csz2 LINK GS1 GS2. *)
(*   unfold link_defs in LINK. *)
(*   unfold gen_symb_table in GS1, GS2. *)
(*   destruct (fold_left (acc_symb sec_data_id sec_code_id) defs1 ([dummy_symbentry], 0, 0)) *)
(*     as (r1 & csz1') eqn:GSEQ1. destruct r1 as (rstbl1 & dsz1'). inv GS1. *)
(*   destruct (fold_left (acc_symb sec_data_id sec_code_id) defs2 ([dummy_symbentry], 0, 0)) *)
(*     as (r2 & csz') eqn:GSEQ2. destruct r2 as (rstbl2 & dsz2'). inv GS2. *)
(*   unfold gen_symb_table. *)
(*   exploit link_defs_acc_symb_comm; eauto. *)
(*   destruct 1 as (stbl & LINKS & ACC). *)
(*   exists stbl. split; auto. rewrite ACC. *)
(*   rewrite rev_involutive. auto. *)
(* Qed. *)



Lemma link_pres_wf_prog: forall p1 p2 p defs,
    link_defs is_fundef_internal (AST.prog_defs p1) (AST.prog_defs p2) = Some defs ->
    wf_prog p1 -> wf_prog p2 -> 
    p = {| AST.prog_defs := defs; 
           AST.prog_public := AST.prog_public p1 ++ AST.prog_public p2; 
           AST.prog_main := AST.prog_main p1 |} ->
    wf_prog p.
Admitted.


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


Lemma link_external_defs : forall {LV: Linker V} (def1 def2 def: option (globdef (AST.fundef F) V)),
    def_internal def1 = false ->
    def_internal def2 = false ->
    link_option def1 def2 = Some def ->
    def_internal def = false.
Proof.
  intros LV def1 def2 def INT1 INT2 LINK.
  unfold link_option in LINK.
  destruct def1, def2.
  - 
    destruct (link g g0) eqn:LINKG; try congruence. inv LINK.
    unfold link in LINKG.
    Transparent Linker_def.
    unfold Linker_def in LINKG.
    unfold link_def in LINKG.
    destruct g, g0.
    + destruct (link f f0) eqn:LINKF; try congruence. inv LINKG.
      unfold link in LINKF.
      Transparent Linker_fundef.
      unfold Linker_fundef in LINKF.
      simpl in *.
      apply link_external_fundefs with f f0; eauto.
    + congruence.
    + congruence.
    + destruct (link v v0) eqn:LINKV; try congruence. inv LINKG.
      simpl in *.     
      apply link_external_vars with _ v v0; eauto.
  - inv LINK. auto.
  - inv LINK. auto.
  - inv LINK. auto.
Qed.    
  

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


Lemma part_not_in_nil : forall id (defs defs' l: list (ident * option (globdef (AST.fundef F) V))),
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

Lemma lst_norepet_partition_inv : forall id (defs defs1 defs2: list (ident * option (globdef (AST.fundef F) V))),
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
  
Lemma partition_inv_nil1 : forall (A:Type) f (l1 l2:list A),
    partition f l1 = ([], l2) -> l1 = l2.
Proof.
  induction l1; intros; simpl in *.
  - inv H. auto.
  - destr_in H. destr_in H. inv H.
    f_equal. apply IHl1; auto.
Qed.

Lemma partition_pres_list_norepet : forall f (l l1 l2: list (ident * option (globdef (AST.fundef F) V))),
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

Lemma link_defs_rest_elem : 
  forall (LV: Linker V) f 
    (defs1 defs2 defs1_linked defs1_rest defs2_rest: list (ident * option (globdef (AST.fundef F) V))),
    link_defs1 f defs1 defs2 = Some (defs1_linked, defs1_rest, defs2_rest) ->
    (forall x, In x defs1_rest -> In x defs1) /\ (forall x, In x defs2_rest -> In x defs2).
Proof.
  induction defs1.
  - intros defs2 defs1_linked defs1_rest defs2_rest LINK.
    simpl in *. inv LINK. auto.
  - intros defs2 defs1_linked defs1_rest defs2_rest LINK.
    simpl in *. destruct a.
    destr_in LINK. destruct p. destruct p.
    destr_in LINK. destruct l2.
    + inv LINK.
      generalize (partition_inv_nil1 _ _ Heqp). intros. subst.
      generalize (IHdefs1 _ _ _ _ Heqo0). 
      destruct 1. split; auto.
    + destruct p. destr_in LINK.
      * destr_in LINK. inv LINK.
        generalize (IHdefs1 _ _ _ _ Heqo0). 
        destruct 1. split; auto.
        intros x IN. inv IN; auto.
      * destr_in LINK. inv LINK.
        generalize (IHdefs1 _ _ _ _ Heqo0).
        destruct 1. split; auto.
        intros x IN.
        apply H0.
        rewrite elements_in_partition; eauto.
Qed.

Lemma link_defs_rest_norepet_pres1 : 
  forall (LV: Linker V) f 
    (defs1 defs2 defs1_linked defs1_rest defs2_rest: list (ident * option (globdef (AST.fundef F) V))),
    list_norepet (map fst defs1) ->
    link_defs1 f defs1 defs2 = Some (defs1_linked, defs1_rest, defs2_rest) ->
    list_norepet (map fst defs1_rest).
Proof.
  induction defs1.
  - intros defs2 defs1_linked defs1_rest defs2_rest NORPT LINK.
    simpl in *. inv LINK. auto.
  - intros defs2 defs1_linked defs1_rest defs2_rest NORPT LINK.
    simpl in *. destruct a.
    destr_in LINK. destruct p. destruct p.
    destr_in LINK. destruct l2.
    + inv LINK. inv NORPT.
      eapply IHdefs1; eauto.
    + destruct p. destr_in LINK.
      * destr_in LINK. inv LINK.
        inv NORPT.
        generalize (IHdefs1 _ _ _ _ H2 Heqo0). 
        intros. simpl. constructor; auto.
        intros IN. apply H1. rewrite in_map_iff in *.
        destruct IN as (x & EQF & IN1). 
        exists x. split; auto. 
        generalize (link_defs_rest_elem _ _ _ _ Heqo0).
        destruct 1. auto.
      * destr_in LINK. inv LINK. inv NORPT.
        generalize (IHdefs1 _ _ _ _ H2 Heqo0).
        auto.
Qed.
        
Lemma link_defs_rest_norepet_pres2 : 
  forall (LV: Linker V) f 
    (defs1 defs2 defs1_linked defs1_rest defs2_rest: list (ident * option (globdef (AST.fundef F) V))),
    list_norepet (map fst defs2) ->
    link_defs1 f defs1 defs2 = Some (defs1_linked, defs1_rest, defs2_rest) ->
    list_norepet (map fst defs2_rest).
Proof.
  induction defs1.
  - intros defs2 defs1_linked defs1_rest defs2_rest NORPT LINK.
    simpl in *. inv LINK. auto.
  - intros defs2 defs1_linked defs1_rest defs2_rest NORPT LINK.
    simpl in *. destruct a.
    destr_in LINK. destruct p. destruct p.
    destr_in LINK. destruct l2.
    + inv LINK.
      generalize (partition_inv_nil1 _ _ Heqp). intros. subst.
      generalize (IHdefs1 _ _ _ _ NORPT Heqo0). auto.
    + destruct p. destr_in LINK.
      * destr_in LINK. inv LINK.
        generalize (IHdefs1 _ _ _ _ NORPT Heqo0). auto.
      * destr_in LINK. inv LINK.
        generalize (IHdefs1 _ _ _ _ NORPT Heqo0).
        intros. 
        generalize (partition_pres_list_norepet _ _ Heqp H).
        destruct 1. auto.
Qed.

Lemma link_defs1_in_order : forall {LV: Linker V} defs1 defs2 defs1_linked defs1_rest defs2_rest,
    list_norepet (map fst defs2) ->
    link_defs1 is_fundef_internal defs1 defs2 = Some (defs1_linked, defs1_rest, defs2_rest) ->
    list_in_order id_def_eq id_def_internal defs1 defs1_linked /\
    list_in_order id_def_eq id_def_internal defs2 defs2_rest.
Proof.
  induction defs1 as [|def1 defs1'].
  - intros defs2 defs1_linked defs1_rest defs2_rest NORPT LINK.
    simpl in *. inv LINK. split.
    constructor.
    apply list_in_order_refl.

  - intros defs2 defs1_linked defs1_rest defs2_rest NORPT LINK.
    simpl in LINK. destruct def1 as (id1, def1).
    destruct (link_defs1 is_fundef_internal defs1' defs2) eqn:LINK1; try congruence.
    destruct p as (p, defs2_rest').
    destruct p as (defs1_linked', defs1_rest').
    destruct (partition (fun '(id', _) => ident_eq id' id1) defs2_rest') as (defs2' & defs2_rest'') eqn:PART.
    destruct defs2' as [| iddef2 defs2''].
    + (** No definition with the same id found in defs2 *)
      inv LINK.
      generalize (IHdefs1' _ _ _ _ NORPT LINK1).
      destruct 1 as (LORDER1 & LORDER2).
      split; auto.      
      apply list_in_order_cons; eauto.

    + (** Some definition with the same id found in defs2 *)
      destruct iddef2 as (id2 & def2).     
      destruct (is_def_internal_dec is_fundef_internal def2) as [DEFINT2 | DEFINT2];
        rewrite DEFINT2 in LINK.
      destruct (is_def_internal_dec is_fundef_internal def1) as [DEFINT1 | DEFINT1];
        rewrite DEFINT1 in LINK.
      congruence.
      inv LINK.
      * (** The left definition is external and the right definition is internal.
            The linking is delayed *)
        generalize (IHdefs1' _ _ _ _ NORPT LINK1).
        destruct 1 as (LORDER1 & LORDER2). split; auto.
        apply lorder_left_false; auto.

      * destruct (link_option def1 def2) as [def|] eqn:LINK_SYMB; inv LINK.
        (** The right definition is external.
            The linking proceeds normally *)
        generalize (IHdefs1' _ _ _ _ NORPT LINK1).
        destruct 1 as (LORDER1 & LORDER2).
        generalize (link_defs_rest_norepet_pres2 _ is_fundef_internal _ _ NORPT LINK1).
        intros NORPT1.
        generalize (lst_norepet_partition_inv _ _ NORPT1 PART).
        destruct 1. congruence. destruct H. inv H.
        subst. split.
        ** destruct (def_internal def1) eqn:DEFINT1.
           *** generalize (link_internal_external_defs _ def2 DEFINT1 DEFINT2 LINK_SYMB).
               intros DEQ. 
               apply lorder_true. simpl. split; auto.
               apply PER_Symmetric; auto.
               auto.
           *** simpl in LINK_SYMB. inv LINK_SYMB.
               apply lorder_left_false; auto.
               apply lorder_right_false; auto.
               simpl. 
               apply link_external_defs with def1 def2; eauto.
        ** generalize (partition_pres_list_in_order _ _ PART).
           intros LORDER3.
           apply list_in_order_trans with defs2_rest'; auto.
Qed.

End WithFunVar.
(** *)

(** Data section generation and linking *)

Lemma extern_var_init_data_nil : forall v,
    is_var_internal v = false ->
    get_def_init_data (Some (Gvar v)) = [].
Proof.
  intros v H. simpl in *.
  unfold is_var_internal in H.
  destruct (gvar_init v); try congruence.
  destruct i; simpl in *; try congruence.
  destruct l; simpl in *; try congruence.
Qed.

Lemma extern_init_data_nil : forall def,
    def_internal def = false -> get_def_init_data def = nil.
Proof.
  intros def H.
  destruct def. destruct g. 
  - simpl in *. auto.
  - simpl in H. apply extern_var_init_data_nil. auto.
  - simpl in *. auto.
Qed.


Lemma acc_init_data_app : forall def l1 l2,
    (acc_init_data def l1) ++ l2 = acc_init_data def (l1 ++ l2).
Proof.
  intros def l1 l2. destruct def as (id & def').
  simpl. rewrite app_assoc. auto.
Qed.

Lemma fold_right_acc_init_data_app : forall defs l,
    fold_right acc_init_data [] defs ++ l = fold_right acc_init_data l defs.
Proof.
  induction defs. 
  - intros l. simpl. auto.
  - intros l. simpl. 
    rewrite acc_init_data_app. rewrite IHdefs. auto.
Qed.

Lemma get_def_init_data_eq : forall d1 d2,
      def_eq d1 d2 -> get_def_init_data d1 = get_def_init_data d2.
Proof.
  intros d1 d2 EQ. inv EQ.
  - simpl. auto.
  - simpl in *. rewrite H1. auto.
Qed.

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
    erewrite extern_init_data_nil; eauto.
  - destruct e as (id, def). simpl.
    erewrite extern_init_data_nil; eauto.
  - simpl.
    rewrite IHlist_in_order. auto.
    apply acc_init_data_eq; auto.
Qed.          

(** Hint for Asm definitions *)                
Definition PERIdAsmDefEq := (@PERIdDefEq Asm.function unit).
Existing Instance PERIdAsmDefEq.
Definition IdAsmDefEq := (@IdDefEq Asm.function unit).
Existing Instance IdAsmDefEq.

Lemma link_acc_init_data_comm : forall defs1 defs2 defs,
    list_norepet (map fst defs1) ->
    list_norepet (map fst defs2) ->
    link_defs is_fundef_internal defs1 defs2 = Some defs ->
    fold_right acc_init_data [] defs = 
    fold_right acc_init_data [] defs1 ++ fold_right acc_init_data [] defs2.
Proof.
  intros defs1 defs2 defs NORPT1 NORPT2 LINK.
  unfold link_defs in LINK.
  destruct (link_defs1 is_fundef_internal defs1 defs2) eqn:LINK1; try inv LINK.
  destruct p as (r & defs2_rest). destruct r as (defs1_linked & defs1_rest).
  destruct (link_defs1 is_fundef_internal defs2_rest defs1_rest) eqn:LINK2; try inv H0.
  destruct p. destruct p as (defs2_linked & p). inv H1.
  rewrite fold_right_app. rewrite <- fold_right_acc_init_data_app.
  generalize (link_defs_rest_norepet_pres1 _ is_fundef_internal defs1 defs2 NORPT1 LINK1).
  intros NORPT3.
  apply link_defs1_in_order in LINK1; auto. destruct LINK1 as (ORDER1 & ORDER2).
  apply link_defs1_in_order in LINK2; auto. destruct LINK2 as (ORDER3 & ORDER4).
  generalize (list_in_order_trans ORDER2 ORDER3).
  intros ORDER5.
  rewrite (acc_init_data_in_order_eq ORDER1).
  rewrite (acc_init_data_in_order_eq ORDER5). auto.  
Qed.


Lemma acc_instrs_app : forall def l1 l2,
    (acc_instrs def l1) ++ l2 = acc_instrs def (l1 ++ l2).
Proof.
  intros def l1 l2. destruct def as (id & def').
  simpl. rewrite app_assoc. auto.
Qed.

Lemma fold_right_acc_instrs_app : forall defs l,
    fold_right acc_instrs [] defs ++ l = fold_right acc_instrs l defs.
Proof.
  induction defs. 
  - intros l. simpl. auto.
  - intros l. simpl. 
    rewrite acc_instrs_app. rewrite IHdefs. auto.
Qed.

(** Code section generation and linking *)
Lemma link_acc_instrs_comm : forall defs1 defs2 defs,
    link_defs is_fundef_internal defs1 defs2 = Some defs ->
    fold_right acc_instrs [] defs = fold_right acc_instrs [] (defs1 ++ defs2).
Admitted.


(** Main linking theorem *)
Lemma link_transf_symbtablegen : forall (p1 p2 : Asm.program) (tp1 tp2 : program) (p : Asm.program),
    link p1 p2 = Some p -> match_prog p1 tp1 -> match_prog p2 tp2 -> 
    exists tp : program, link tp1 tp2 = Some tp /\ match_prog p tp.
Proof.
  intros p1 p2 tp1 tp2 p LINK MATCH1 MATCH2.
  unfold link. unfold Linker_reloc_prog. unfold link_reloc_prog.
  rewrite <- (match_prog_pres_prog_defs MATCH1).
  rewrite <- (match_prog_pres_prog_defs MATCH2).
  rewrite <- (match_prog_pres_prog_main MATCH1).
  rewrite <- (match_prog_pres_prog_main MATCH2).
  rewrite <- (match_prog_pres_prog_public MATCH1).
  rewrite <- (match_prog_pres_prog_public MATCH2).
  setoid_rewrite LINK.
  apply link_prog_inv in LINK.
  destruct LINK as (MAINEQ & NRPT1 & NRPT2 & defs & PEQ & LINKDEFS). subst. simpl.
  unfold match_prog in *.

  unfold transf_program in MATCH1.
  destruct check_wellformedness; try monadInv MATCH1.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p1)) as (p & csz1) eqn:GSEQ1 .
  destruct p as (stbl1 & dsz1).
  destruct zle; try monadInv MATCH1; simpl.
  
  unfold transf_program in MATCH2.
  destruct check_wellformedness; try monadInv MATCH2.
  destruct (gen_symb_table sec_data_id sec_code_id (AST.prog_defs p2)) as (p & csz2) eqn:GSEQ2 .
  destruct p as (stbl2 & dsz2).
  destruct zle; try monadInv MATCH2; simpl.
  

  (* generalize (gen_symb_table_index_in_range _ _ _ GSEQ2). *)
  (* intro SIDX_RANGE2.   *)
  (* generalize (reloc_symbtable_exists  *)
  (*               SIDX_RANGE2  *)
  (*               (eq_refl  *)
  (*                  (reloc_offset_fun (sec_size (create_data_section (AST.prog_defs p1))) *)
  (*                                    (sec_size (create_code_section (AST.prog_defs p1)))))). *)
  (* destruct 1 as (stbl2' & RELOC2 & RELOC_REL). *)
  (* setoid_rewrite RELOC2. *)

  exploit link_gen_symb_comm; eauto.
  destruct 1 as (stbl & stbl2' & RELOC & LINKS & GENS).

  Lemma gen_symb_table_size: forall defs d_id c_id stbl dsz csz,
      gen_symb_table d_id c_id defs = (stbl, dsz, csz) ->
      sec_size (create_data_section defs) = dsz /\
      sec_size (create_code_section defs) = csz.
  Admitted.

  generalize (gen_symb_table_size _ _ _ GSEQ1).
  destruct 1 as (DSZ & CSZ).
  setoid_rewrite DSZ.
  setoid_rewrite CSZ.
  rewrite RELOC.
  rewrite LINKS.

  eexists. split. reflexivity.
  unfold transf_program.

  exploit link_pres_wf_prog; eauto.
  intros WF.
  destruct check_wellformedness; try congruence.
  simpl. rewrite GENS.
  
  destruct zle.
  repeat f_equal.
  unfold create_sec_table. repeat f_equal.
  unfold create_data_section. f_equal.
  (* rewrite fold_right_acc_init_data_app. *)
  (* rewrite <- fold_right_app. *)
  apply link_acc_init_data_comm; auto.
  unfold create_code_section. f_equal.
  rewrite fold_right_acc_instrs_app.
  rewrite <- fold_right_app.
  apply link_acc_instrs_comm; auto.

  Admitted.

Instance TransfLinkSymbtablegen : TransfLink match_prog :=
  link_transf_symbtablegen.

