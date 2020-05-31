(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   May 31, 2020 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram Symbtablegen.
Require Import CheckDef.
Require Import AsmFacts.
Require Import LocalLib.
Import ListNotations.


Lemma get_symbentry_id : forall d_id c_id dsz csz id def,
    symbentry_id (get_symbentry d_id c_id dsz csz id def) = id.
Proof.
  intros until def.
  destruct def. destruct g. destruct f.
  simpl; auto.
  simpl; auto.
  simpl. destruct (gvar_init v); auto. destruct i; auto. destruct l; auto.
  simpl; auto.
Qed.


Lemma get_symbentry_eq_id_inv: 
  forall did1 cid1 dsz1 csz1 id1 def1 did2 cid2 dsz2 csz2 id2 def2,
    get_symbentry did1 cid1 dsz1 csz1 id1 def1 = get_symbentry did2 cid2 dsz2 csz2 id2 def2 -> id1 = id2.
Proof.
  intros. 
  generalize (get_symbentry_id did1 cid1 dsz1 csz1 id1 def1).
  intros ID1.
  generalize (get_symbentry_id did2 cid2 dsz2 csz2 id2 def2).
  intros ID2.
  rewrite H in ID1.
  rewrite ID1 in ID2.
  inv ID2. auto.
Qed.

Lemma get_var_entry_size : forall did cid dsz csz id v, 
    symbentry_size (get_symbentry did cid dsz csz id (Some (Gvar v))) = AST.init_data_list_size (gvar_init v).
Proof.
  intros.
  cbn. destruct (gvar_init v); auto.
  destruct i; auto.
  destruct l; auto.
  cbn. omega.
Qed.


Lemma acc_init_data_app : forall def l1 l2,
    (acc_init_data def l1) ++ l2 = acc_init_data def (l1 ++ l2).
Proof.
  intros def l1 l2. destruct def as (id & def').
  simpl. rewrite app_assoc. auto.
Qed.

Lemma fold_right_acc_init_data_app' : forall defs l,
    fold_right acc_init_data [] defs ++ l = fold_right acc_init_data l defs.
Proof.
  induction defs. 
  - intros l. simpl. auto.
  - intros l. simpl. 
    rewrite acc_init_data_app. rewrite IHdefs. auto.
Qed.

Lemma fold_right_acc_init_data_app : forall defs1 defs2,
    fold_right acc_init_data [] (defs1 ++ defs2) = 
    fold_right acc_init_data [] defs1 ++ fold_right acc_init_data [] defs2.
Proof.
  intros.
  rewrite fold_right_app.
  rewrite <- fold_right_acc_init_data_app'. auto.
Qed.

Lemma acc_instrs_app : forall def l1 l2,
    (acc_instrs def l1) ++ l2 = acc_instrs def (l1 ++ l2).
Proof.
  intros def l1 l2. destruct def as (id & def').
  simpl. rewrite app_assoc. auto.
Qed.

Lemma fold_right_acc_instrs_app' : forall defs l,
    fold_right acc_instrs [] defs ++ l = fold_right acc_instrs l defs.
Proof.
  induction defs. 
  - intros l. simpl. auto.
  - intros l. simpl. 
    rewrite acc_instrs_app. rewrite IHdefs. auto.
Qed.

Lemma fold_right_acc_instrs_app : forall defs1 defs2,
    fold_right acc_instrs [] (defs1 ++ defs2) = 
    fold_right acc_instrs [] defs1 ++ fold_right acc_instrs [] defs2.
Proof.
  intros. rewrite fold_right_app.
  rewrite <- fold_right_acc_instrs_app'. auto.
Qed.

Lemma update_code_data_size_eq : forall def dsz csz dincr cincr,
    dincr = init_data_list_size (get_def_init_data def) ->
    cincr = code_size (get_def_instrs def) ->
    update_code_data_size dsz csz def = (dincr + dsz, cincr + csz).
Proof.
  intros def dsz csz dincr cincr DINCR CINCR.
  unfold update_code_data_size. destruct def. destruct g. destruct f.
  - simpl in *. subst. f_equal; omega.
  - simpl in *. subst. f_equal; omega.
  - simpl in DINCR, CINCR. subst.
    destruct (gvar_init v).
    + simpl. auto.
    + destruct i; try (f_equal; omega).
      destruct l; f_equal; omega.
  - simpl in *. subst. f_equal; omega.
Qed.

Lemma acc_symb_size: forall d_id c_id defs s1 s2 dsz1 csz1 dsz2 csz2 data code,
    fold_left (acc_symb d_id c_id) defs (s1, dsz1, csz1) = (s2, dsz2, csz2) ->
    init_data_list_size data = dsz1 ->
    code_size code = csz1 ->
    init_data_list_size (fold_right acc_init_data data defs) = dsz2 /\ 
    code_size (fold_right acc_instrs code defs) = csz2.
Proof.
  induction defs as [| def defs].
  - intros s1 s2 dsz1 csz1 dsz2 csz2 data code SYMB INIT CODE.
    simpl in *. inv SYMB. auto.
  - intros s1 s2 dsz1 csz1 dsz2 csz2 data code SYMB INIT CODE.
    destruct def as (id, def).
    simpl in *. destr_in SYMB.
    rewrite init_data_list_size_app.
    rewrite code_size_app.
    erewrite update_code_data_size_eq in Heqp; eauto.
    inv Heqp.
    rewrite <- init_data_list_size_app in SYMB.
    rewrite <- code_size_app in SYMB.
    generalize (IHdefs _ _ _ _ _ _ _ _ SYMB 
                       (@eq_refl _ (init_data_list_size (get_def_init_data def ++ data)))
                       (@eq_refl _ (code_size (get_def_instrs def ++ code)))).
    destruct 1. subst. split.
    + rewrite <- (fold_right_acc_init_data_app' defs data).
      rewrite <- (fold_right_acc_init_data_app' defs (get_def_init_data def ++ data)).
      repeat rewrite init_data_list_size_app.
      omega.
    + rewrite <- (fold_right_acc_instrs_app' defs code).
      rewrite <- (fold_right_acc_instrs_app' defs (get_def_instrs def ++ code)).
      repeat rewrite code_size_app.
      omega.
Qed.


Lemma gen_symb_table_size: forall defs d_id c_id stbl dsz csz,
    gen_symb_table d_id c_id defs = (stbl, dsz, csz) ->
    sec_size (create_data_section defs) = dsz /\
    sec_size (create_code_section defs) = csz.
Proof.
  intros defs d_id c_id stbl dsz csz SGEN.
  simpl. unfold gen_symb_table in SGEN.
  destr_in SGEN. destruct p. inv SGEN. 
  eapply acc_symb_size; eauto.
Qed.


Lemma acc_symb_append : forall d_id c_id defs dsz1 csz1 stbl1 dsz2 csz2 stbl2 stbl3,
    fold_left (acc_symb d_id c_id) defs (stbl1, dsz1, csz1) = (stbl2, dsz2, csz2) ->
    fold_left (acc_symb d_id c_id) defs (stbl1 ++ stbl3, dsz1, csz1) = (stbl2 ++ stbl3, dsz2, csz2).
Proof.
  induction defs.
  - intros until stbl2. intros stbl3 ACC. simpl in *.
    inv ACC. auto.
  - intros until stbl2. intros stbl3 ACC. simpl in *.
    destr_in ACC. destruct a. inv Heqp. destr_in ACC.
    rewrite app_comm_cons.
    apply IHdefs. auto.
Qed.

Lemma acc_symb_append_nil : forall d_id c_id defs dsz1 csz1 dsz2 csz2 stbl2 stbl3,
    fold_left (acc_symb d_id c_id) defs ([], dsz1, csz1) = (stbl2, dsz2, csz2) ->
    fold_left (acc_symb d_id c_id) defs (stbl3, dsz1, csz1) = (stbl2 ++ stbl3, dsz2, csz2).
Proof.
  intros until stbl3. intros ACC.
  replace stbl3 with ([] ++ stbl3) by auto.
  apply acc_symb_append. auto.
Qed.


Lemma acc_symb_inv: forall asf d_id c_id defs stbl1 dsz1 csz1 stbl2 dsz2 csz2,
    asf = (acc_symb d_id c_id) ->
    fold_left asf defs (stbl1, dsz1, csz1) = (stbl2, dsz2, csz2) ->
    exists stbl1', stbl2 = stbl1' ++ stbl1 /\
              fold_left asf defs ([], dsz1, csz1) = (stbl1', dsz2, csz2).
Proof.
  induction defs.
  - intros stbl1 dsz1 csz1 stbl2 dsz2 csz2 ASF ACC.
    simpl in *. inv ACC. exists nil. eauto.
  - intros until csz2. intros ASF ACC. simpl in *.
    rewrite ASF in ACC. simpl in ACC. destruct a as (id & def).
    destruct (update_code_data_size dsz1 csz1 def) as [dsize' csize'] eqn:UPDATE.
    rewrite <- ASF in ACC.
    generalize (IHdefs _ _ _ _ _ _ ASF ACC).
    destruct 1 as (stbl1' & EQ & ACC1).
    rewrite app_cons_comm in EQ.
    rewrite EQ.
    eexists. split; auto.
    subst. simpl.
    rewrite UPDATE. 
    apply acc_symb_append_nil. auto.
Qed.

Lemma acc_symb_inv': forall d_id c_id defs stbl1 dsz1 csz1 stbl2 dsz2 csz2,
    fold_left (acc_symb d_id c_id) defs (stbl1, dsz1, csz1) = (stbl2, dsz2, csz2) ->
    exists stbl1', stbl2 = stbl1' ++ stbl1 /\
              fold_left (acc_symb d_id c_id) defs ([], dsz1, csz1) = (stbl1', dsz2, csz2).
Proof.
  intros. eapply acc_symb_inv; eauto.
Qed.

Definition symbentry_index_in_range range e :=
  match symbentry_secindex e with
  | secindex_normal i => In i range
  | _ => True
  end.

Definition symbtable_indexes_in_range range t :=
  Forall (symbentry_index_in_range range) t.

Lemma get_symbentry_in_range: forall d_id c_id dsz csz id def,
  symbentry_index_in_range [d_id; c_id] (get_symbentry d_id c_id dsz csz id def).
Proof.
  intros.
  destruct def. destruct g. destruct f.
  - cbn. auto.
  - cbn. auto.
  - cbn. destr; cbn; auto.
    destruct i; cbn; auto.
    destruct l; cbn; auto.
  - cbn. auto.
Qed.

Lemma acc_symb_index_in_range: forall d_id c_id defs dsz1 csz1 tbl dsz2 csz2,
      fold_left (acc_symb d_id c_id) defs ([], dsz1, csz1) = (tbl, dsz2, csz2)
      -> symbtable_indexes_in_range [d_id; c_id] (rev tbl).
Proof.
  induction defs as [| def defs].
  - intros until csz2. intros ACC. cbn in *.
    inv ACC. red. cbn. apply Forall_nil.
  - intros until csz2. intros ACC. cbn in *.
    destruct def as [id def]. destr_in ACC.
    generalize (acc_symb_inv _ _ _ _ _ _ _ _ _ _ eq_refl ACC).
    destruct 1 as (stbl1' & EQ & ACC'). subst.
    rewrite rev_unit.
    generalize (IHdefs _ _ _ _ _ ACC').
    intros IN_RNG.
    red. rewrite Forall_forall.
    intros x IN.
    inv IN.
    + apply get_symbentry_in_range.
    + red in IN_RNG.
      rewrite Forall_forall in IN_RNG.
      apply IN_RNG; auto.
Qed.

Lemma gen_symb_table_index_in_range : forall defs sec_data_id sec_code_id stbl dsz csz,
    gen_symb_table sec_data_id sec_code_id defs = (stbl, dsz, csz) ->
    symbtable_indexes_in_range [sec_data_id; sec_code_id] stbl.
Proof.
  intros until csz.
  intros GS.
  unfold gen_symb_table in GS. destr_in GS. destruct p. inv GS.
  apply acc_symb_inv' in Heqp.
  destruct Heqp as (stbl1' & EQ & FL). subst.
  rewrite rev_app_distr. cbn.
  apply acc_symb_index_in_range in FL.
  red. red in FL.
  auto.
Qed.

Lemma get_var_entry_type : forall did cid dsz1 csz1 id v,
    symbentry_type (get_symbentry did cid dsz1 csz1 id (Some (Gvar v))) = symb_data.
Proof.
  intros. cbn.
  destruct (gvar_init v); auto.
  destruct i; auto.
  destruct l; auto.
Qed.

Lemma get_fun_entry_type : forall did cid dsz1 csz1 id f,
    symbentry_type (get_symbentry did cid dsz1 csz1 id (Some (Gfun f))) = symb_func.
Proof.
  intros. cbn.
  destruct f; auto.
Qed.

Lemma get_none_entry_type : forall did cid dsz1 csz1 id,
    symbentry_type (get_symbentry did cid dsz1 csz1 id None) = symb_notype.
Proof.
  intros. cbn. auto.
Qed.

Lemma get_none_entry_secindex : forall did cid dsz1 csz1 id,
    symbentry_secindex (get_symbentry did cid dsz1 csz1 id None) = secindex_undef.
Proof.
  intros. cbn. auto.
Qed.

Lemma get_symbentry_eq_gvar_init: forall did cid dsz1 csz1 id v1 v2,
    gvar_init v1 = gvar_init v2 ->
    get_symbentry did cid dsz1 csz1 id (Some (Gvar v1)) = 
    get_symbentry did cid dsz1 csz1 id (Some (Gvar v2)).
Proof.
  intros. cbn. rewrite H. auto.
Qed.

Lemma update_size_offset : forall def dsz csz dsz1 csz1 dofs cofs,
    update_code_data_size dsz csz def = (dsz1, csz1) ->
    update_code_data_size (dofs + dsz) (cofs + csz) def = (dofs + dsz1, cofs + csz1).
Proof.
  intros until cofs. intros UPDATE.
  destruct def. destruct g. destruct f.
  - cbn in *. inv UPDATE. f_equal; omega.
  - cbn in *. inv UPDATE. f_equal; omega.
  - unfold update_code_data_size in *.
    destr_in UPDATE. 
    destruct i; try (inv UPDATE; cbn; f_equal; omega).
    destruct l; try (inv UPDATE; cbn; f_equal; omega).
  - cbn in *. inv UPDATE. auto.
Qed.

Lemma acc_symb_pres_ids: forall did cid defs dsz1 csz1 stbl2 dsz2 csz2,
    fold_left (acc_symb did cid) defs ([], dsz1, csz1) = (stbl2, dsz2, csz2) ->
    (map fst defs) = get_symbentry_ids (rev stbl2).
Proof.
  induction defs as [| def defs].
  - cbn.  inversion 1. subst. inv H.
    cbn. auto.
  - intros dsz1 csz1 stbl2 dsz2 csz2 FL.
    cbn in *. destruct def as (id, def).
    destr_in FL. cbn.
    apply acc_symb_inv' in FL. 
    destruct FL as (stbl2' & EQ & FL). subst.
    unfold get_symbentry_ids.
    rewrite rev_app_distr.
    cbn.
    unfold acc_symb_ids. cbn.
    rewrite get_symbentry_id.
    fold acc_symb_ids.
    erewrite acc_symb_ids_inv.
    rewrite rev_app_distr.
    cbn. f_equal.
    eapply IHdefs; eauto.
Qed.

Lemma gen_symb_table_pres_ids: forall did cid defs stbl dsz csz,
    gen_symb_table did cid defs = (stbl, dsz, csz) ->
    (map fst defs) = (get_symbentry_ids stbl).
Proof.
  intros did cid defs stbl dsz csz GST.
  unfold gen_symb_table in GST.
  destr_in GST. destruct p. inv GST.
  apply acc_symb_inv' in Heqp.
  destruct Heqp as (s' & EQ & FL). subst.
  rewrite rev_app_distr. cbn.
  eapply acc_symb_pres_ids; eauto. 
Qed.
