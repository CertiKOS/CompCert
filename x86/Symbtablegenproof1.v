(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   May 31, 2020 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram RelocProgSemantics Symbtablegen.
Require Import CheckDef.
Require Import RealAsm AsmFacts.
Require Import LocalLib.
Require Import Linking.
Import ListNotations.


Lemma get_symbentry_pres_internal_prop : forall did cid id dsz csz def,
    is_def_internal is_fundef_internal def = 
    is_symbentry_internal (get_symbentry did cid dsz csz id def).
Proof.
  intros. destruct def.
  destruct g. destruct f.
  - cbn. auto.
  - cbn. auto.
  - cbn. unfold is_var_internal. 
    destruct (gvar_init v); cbn; auto.
    destruct i; cbn; auto.
    destruct l; cbn; auto.
  - cbn. auto.
Qed.


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
    rewrite get_symbentry_id.
    f_equal.
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


(** Symbol entires obtained from trees *)
Fixpoint elems_before_aux {A B} 
         (eq_dec: forall (a b:A), {a = b} + {a <> b})
         (id:A) (defs: list (A * B)) acc :=
  match defs with
  | nil => acc
  | (id', def) :: defs' =>
    if eq_dec id id' then
      acc
    else
      elems_before_aux eq_dec id defs' (def :: acc)
  end.

Definition elems_before {A B} 
           (eq_dec: forall (a b:A), {a = b} + {a <> b})
           (id:A) (defs: list (A * B)) :=
  rev (elems_before_aux eq_dec id defs nil).

Definition defs_before {F V}
           (id:ident) (defs: list (ident * option (globdef F V))) :=
  elems_before ident_eq id defs.

Lemma elems_before_cons: forall {A B} dec (id:A) (def:B) defs,
          elems_before dec id ((id, def) :: defs) = nil.
Proof.
  intros. unfold elems_before. cbn.
  rewrite dec_eq_true. cbn. auto.
Qed.

Lemma elems_before_aux_inv: forall {A B} dec (id:A) defs (l: list B),
      elems_before_aux dec id defs l = elems_before_aux dec id defs [] ++ l.
Proof.
  induction defs as [|def defs].
  - intros. cbn. auto.
  - cbn. destruct def. destruct dec. auto.
    intros. rewrite IHdefs. 
    rewrite (IHdefs [b]).
    rewrite <- app_assoc. cbn. auto.
Qed.

Lemma elems_before_tail:
  forall (A B : Type) (dec : forall a b : A, {a = b} + {a <> b}) 
    (id id': A) (def : B) (defs : list (A * B)),
  id <> id' ->
  elems_before dec id ((id', def) :: defs) = def :: elems_before dec id defs.
Proof.
  intros.
  unfold elems_before. cbn.
  rewrite dec_eq_false; auto.
  rewrite elems_before_aux_inv.
  rewrite rev_app_distr. cbn. auto.
Qed.

Lemma defs_before_tail:
  forall {F V} id id' (def : option (globdef F V)) defs,
  id <> id' ->
  defs_before id ((id', def) :: defs) = def :: defs_before id defs.
Proof.
  intros.
  eapply elems_before_tail; auto.
Qed.

Lemma defs_before_head:
  forall {F V} id  (def : option (globdef F V)) defs,
  defs_before id ((id, def) :: defs) = nil.
Proof.
  intros.
  cbn. rewrite peq_true. cbn. auto.
Qed.

Definition def_data_size (def: option gdef) :=
  init_data_list_size (get_def_init_data def).

Definition def_code_size (def: option gdef) :=
  code_size (get_def_instrs def).

Definition defs_data_size (defs: list (option gdef)) :=
  fold_right (fun def sz => def_data_size def + sz) 0 defs.

Definition defs_code_size (defs: list (option gdef)) :=
  fold_right (fun def sz => def_code_size def + sz) 0 defs.


Lemma defs_data_size_cons: forall def defs,
      defs_data_size (def :: defs) = (def_data_size def) + defs_data_size defs.
Proof.
  intros. unfold defs_data_size.
  cbn. auto.
Qed.

Lemma defs_code_size_cons: forall def defs,
      defs_code_size (def :: defs) = (def_code_size def) + defs_code_size defs.
Proof.
  intros. unfold defs_code_size.
  cbn. auto.
Qed.

Lemma symbtable_to_tree_cons: forall did cid tl dsz1 csz1 id def,
    ~In id (get_symbentry_ids tl) ->
    (symbtable_to_tree (get_symbentry did cid dsz1 csz1 id def :: tl)) ! id = Some (get_symbentry did cid dsz1 csz1 id def).
Proof.
  intros did cid tl dsz1 csz1 id def IN.
  unfold symbtable_to_tree.
  cbn [symbtable_to_idlist map].
  rewrite get_symbentry_id.
  match goal with
  | [ |- context [ PTree_Properties.of_list ?l ] ] =>
    replace l with ([] ++ l) by auto
  end.
  erewrite PTree_Properties.of_list_unique; eauto.
  rewrite list_map_compose. auto.
Qed.

Lemma symbtable_to_tree_tail: forall did cid tl dsz1 csz1 id id' def,
    id <> id' ->
    (symbtable_to_tree (get_symbentry did cid dsz1 csz1 id def :: tl)) ! id' =
    (symbtable_to_tree tl) ! id'.
Proof.
  intros. unfold symbtable_to_tree.
  cbn [symbtable_to_idlist map].
  rewrite get_symbentry_id.
  eapply PTree_Properties_of_list_tail; auto.
Qed.


Lemma update_code_data_size_inv: forall dsz1 csz1 def dsz2 csz2,
          update_code_data_size dsz1 csz1 def = (dsz2, csz2) ->
          dsz2 = dsz1 + def_data_size def /\
          csz2 = csz1 + def_code_size def.
Proof.
  intros dsz1 csz1 def dsz2 csz2 UPD.
  unfold update_code_data_size in UPD. 
  destruct def. destruct g. destruct f.
  - unfold def_data_size, def_code_size.
    simpl in *. inv UPD. f_equal; omega.
  - unfold def_data_size, def_code_size.
    inv UPD. cbn. split; omega.
  - destruct (gvar_init v) eqn:V.
    + inv UPD. cbn. rewrite V. cbn. split; omega.
    + destruct i; try (inv UPD; cbn; rewrite V; cbn; split; omega).
      destruct l; try (inv UPD; cbn; rewrite V; cbn; split; omega). 
  - inv UPD. cbn. split; omega.
Qed.


Lemma acc_symb_tree_entry_some : forall did cid defs dsz1 csz1 dsz2 csz2 stbl id def,
    list_norepet (map fst defs) ->
    fold_left (acc_symb did cid) defs ([], dsz1, csz1) = (stbl, dsz2, csz2) ->
    (PTree_Properties.of_list defs)!id = Some def ->
    (symbtable_to_tree (rev stbl))!id 
      = Some (get_symbentry did cid 
                            (dsz1 + defs_data_size (defs_before id defs))
                            (csz1 + defs_code_size (defs_before id defs))
                            id
                            def).
Proof.
  induction defs as [|def' defs].
  - cbn. inversion 1. subst. inv H. cbn. intros.
    rewrite PTree.gempty in H0. congruence.
  - intros dsz1 csz1 dsz2 csz2 stbl id def NORPT ACC GET.
    cbn in ACC. destruct def' as (id', def').
    destr_in ACC. apply acc_symb_inv' in ACC.
    destruct ACC as (stbl' & EQ & ACC). subst.
    rewrite rev_app_distr.
    cbn [rev "++"].
    destruct (ident_eq id id').
    + subst.
      setoid_rewrite elems_before_cons.
      replace ((id', def') :: defs) with ([] ++ (id', def') :: defs) in GET by auto.
      erewrite PTree_Properties.of_list_unique in GET; eauto.
      inv GET.
      rewrite symbtable_to_tree_cons. cbn.
      repeat rewrite Z.add_0_r. auto.
      erewrite <- acc_symb_pres_ids; eauto.
      inv NORPT. auto.
      inv NORPT. auto.
    + assert ((PTree_Properties.of_list defs) ! id = Some def) as GET'.
      { eapply PTree_Properties_of_list_tail_some; eauto. }
      rewrite symbtable_to_tree_tail; eauto.
      inv NORPT.
      generalize (IHdefs _ _ _ _ _ _ _ H2 ACC GET').
      intros SEQ. rewrite SEQ.
      setoid_rewrite defs_before_tail; auto.
      cbn [defs_data_size defs_code_size].
      rewrite defs_data_size_cons.
      rewrite defs_code_size_cons.
      generalize (update_code_data_size_inv _ _ _ _ _ Heqp).
      intros (EQ1 & EQ2); subst.
      f_equal. f_equal; omega.
Qed.


Lemma acc_symb_tree_entry_none : forall did cid defs dsz1 csz1 dsz2 csz2 stbl id,
    fold_left (acc_symb did cid) defs ([], dsz1, csz1) = (stbl, dsz2, csz2) ->
    (PTree_Properties.of_list defs)!id = None ->
    (symbtable_to_tree (rev stbl))!id = None.
Proof.
  induction defs as [|def defs].
  - cbn. intros dsz1 csz1 dsz2 csz2 stbl id EQ GET.
    inv EQ. cbn.
    rewrite PTree.gempty. auto.
  - intros dsz1 csz1 dsz2 csz2 stbl id FL GET.
    destruct def as (id', def').
    cbn in FL.
    destr_in FL.
    apply acc_symb_inv' in FL.
    destruct FL as (stbl1' & EQ  & FL). subst.
    rewrite rev_app_distr. cbn [rev "++"].
    destruct (ident_eq id id').
    + subst.
      assert (In id' (map fst ((id', def') :: defs))) as IN by apply in_eq.
      exploit PTree_Properties.of_list_dom; eauto.
      intros (v & GET'). congruence.
    + erewrite symbtable_to_tree_tail; eauto.
      eapply IHdefs; eauto.
      eapply PTree_Properties_of_list_tail_none; eauto.
Qed.


Lemma acc_symb_tree_entry_some_inv:
  forall (did cid : N) (defs : list (ident * option (globdef fundef unit)))
    (dsz1 csz1 dsz2 csz2 : Z) (stbl : symbtable) (id : positive) e,
  list_norepet (map fst defs) ->
  fold_left (acc_symb did cid) defs ([], dsz1, csz1) = (stbl, dsz2, csz2) ->
  (symbtable_to_tree (rev stbl)) ! id = Some e ->
  exists def, (PTree_Properties.of_list defs) ! id = Some def.
Proof.
  induction defs as [|def defs].
  - cbn. intros until e.
    intros NORPT EQ ST. inv EQ. cbn in ST.
    rewrite PTree.gempty in ST. congruence.
  - intros until e.
    intros NORPT ACC ST. inv NORPT.
    cbn in ACC. destruct def as (id', def).
    destr_in ACC.
    apply acc_symb_inv' in ACC.
    destruct ACC as (stbl1 & EQ & ACC). subst.
    rewrite rev_app_distr in ST. cbn [rev "++"] in ST.
    destruct (ident_eq id id').
    + subst.
      eapply PTree_Properties.of_list_dom; eauto.
      cbn. auto.
    + erewrite symbtable_to_tree_tail in ST; eauto.
      generalize (IHdefs _ _ _ _ _ _ _ H2 ACC ST).
      intros (def1 & GET1).
      rewrite PTree_Properties_of_list_tail; eauto.
Qed.

Definition symbtable_entry_equiv_sizes stbl dsz1 csz1 defs1 :=
  forall did cid dsz3 csz3 id def,
    In (get_symbentry did cid dsz3 csz3 id def) stbl ->
    get_symbentry did cid dsz3 csz3 id def =
    get_symbentry did cid 
                  (dsz1 + defs_data_size (defs_before id defs1))
                  (csz1 + defs_code_size (defs_before id defs1))
                  id def.

Lemma symbtable_entry_equiv_sizes_app_comm: forall l1 l2 dsz csz defs,
    symbtable_entry_equiv_sizes (l1 ++ l2) dsz csz defs ->
    symbtable_entry_equiv_sizes (l2 ++ l1) dsz csz defs.
Proof.
  intros l1 l2 dsz csz defs SE.
  red. intros; eapply SE; eauto.
  rewrite in_app in *. inv H. 
  right; eauto.
  left; eauto.
Qed.

Lemma symbtable_entry_equiv_sizes_app: forall l1 l2 dsz csz defs,
    symbtable_entry_equiv_sizes l1 dsz csz defs ->
    symbtable_entry_equiv_sizes l2 dsz csz defs ->
    symbtable_entry_equiv_sizes (l1 ++ l2) dsz csz defs.
Proof.
  intros l1 l2 dsz csz defs SE1 SE2.
  red. intros did cid dsz3 csz3 id def IN.
  rewrite in_app in IN. 
  destruct IN as [IN | IN].
  - eapply SE1; eauto.
  - eapply SE2; eauto.
Qed.

Lemma acc_symb_size':
  forall (d_id c_id : N) (defs : list (ident * option (globdef fundef unit)))
    (s1 s2 : symbtable) (dsz1 csz1 dsz2 csz2 : Z),
    fold_left (acc_symb d_id c_id) defs (s1, dsz1, csz1) = (s2, dsz2, csz2) ->
    dsz2 = dsz1 + defs_data_size (map snd defs) /\
    csz2 = csz1 + defs_code_size (map snd defs).
Proof.
  induction defs as [|def defs].
  - cbn. inversion 1. split; omega.
  - intros s1 s2 dsz1 csz1 dsz2 csz2 ACC.
    cbn in ACC. destruct def as (id, def). 
    cbn [map snd].
    rewrite defs_code_size_cons.
    rewrite defs_data_size_cons.
    destr_in ACC.
    generalize (update_code_data_size_inv _ _ _ _ _ Heqp).
    intros (EQ1 & EQ2). subst.
    apply IHdefs in ACC. 
    destruct ACC. subst; omega.
Qed.

Lemma acc_instrs_size: forall defs,
      defs_code_size (map snd defs) = code_size (fold_right acc_instrs [] defs).
Proof.
  induction defs as [|def defs].
  - cbn. auto.
  - cbn. setoid_rewrite IHdefs.
    destruct def. cbn.
    rewrite code_size_app. auto.
Qed.

Lemma acc_init_data_size: forall defs,
      defs_data_size (map snd defs) = 
      init_data_list_size (fold_right acc_init_data [] defs).
Proof.
  induction defs as [|def defs].
  - cbn. auto.
  - cbn. setoid_rewrite IHdefs.
    destruct def. cbn.
    rewrite init_data_list_size_app. auto.
Qed.

Lemma get_symbentry_ids_in: forall e stbl i,
    In e stbl -> symbentry_id e = i ->
    In i (get_symbentry_ids (rev stbl)).
Proof.
  induction stbl as [|e' stbl].
  inversion 1.
  intros i IN SE.
  cbn.
  rewrite map_app.
  cbn.
  rewrite in_app_iff.
  inv IN.
  - right. cbn. auto.
  - left. eapply IHstbl; eauto.
Qed.


Lemma acc_symb_map_inv : forall e t b ofs,
    t ! (symbentry_id e) = None ->
    (acc_symb_map e t) ! (symbentry_id e) = Some (b, ofs) ->
    ofs = Ptrofs.repr (symbentry_value e) /\
    (exists i : N,
        symbentry_secindex e = secindex_normal i /\
        b = sec_index_to_block i).
Proof.
  intros e t b ofs GET ACC.
  unfold acc_symb_map in ACC.
  destr_in ACC.
  erewrite PTree.gss in ACC. inv ACC.
  eauto.
Qed.

Lemma acc_symb_map_no_effect: forall stbl id t,
    ~In id (get_symbentry_ids stbl) ->
    (fold_right acc_symb_map t stbl) ! id = t ! id.
Proof.
  induction stbl as [|e stbl].
  - cbn. auto.
  - cbn. intros id t NIN.
    unfold acc_symb_map.
    destr; auto.
    destruct (peq (symbentry_id e) id); subst; eauto.
    + tauto.
    + erewrite PTree.gso; eauto.
Qed.

Lemma symbtable_to_tree_acc_symb_map_inv': forall stbl id e b ofs t,
    list_norepet (get_symbentry_ids stbl) ->
    (PTree_Properties.of_list (symbtable_to_idlist stbl)) ! id = Some e ->
    t ! id = None ->
    (fold_right acc_symb_map t stbl) ! id = Some (b, ofs) ->
    ofs = Ptrofs.repr (symbentry_value e) /\
    (exists i, symbentry_secindex e = secindex_normal i /\ b = sec_index_to_block i).
Proof.
  induction stbl as [|e stbl].
  - cbn. intros.
    congruence.
  - intros id e0 b ofs t NORPT T NG ACC.
    unfold get_symbentry_ids in NORPT.
    inv NORPT.
    cbn [symbtable_to_idlist map] in T.
    cbn in ACC.
    destruct (peq id (symbentry_id e)).
    + subst.
      rewrite PTree_Properties_of_list_cons in T. inv T.
      apply acc_symb_map_inv with (fold_right acc_symb_map t stbl); eauto.     
      erewrite acc_symb_map_no_effect; eauto.
      rewrite list_map_compose. cbn. auto.
    + erewrite PTree_Properties_of_list_tail in T; eauto. 
      eapply IHstbl; eauto.
      unfold acc_symb_map in ACC.
      destr_in ACC; auto.
      erewrite PTree.gso in ACC; eauto.
Qed.

Lemma symbtable_to_tree_acc_symb_map_inv: forall stbl id e b ofs,
    list_norepet (get_symbentry_ids stbl) ->
    (symbtable_to_tree stbl) ! id = Some e ->
    (fold_right acc_symb_map (PTree.empty _) stbl) ! id = Some (b, ofs) ->
    ofs = Ptrofs.repr (symbentry_value e) /\
    (exists i, symbentry_secindex e = secindex_normal i /\ b = sec_index_to_block i).
Proof.
  unfold symbtable_to_tree.
  intros. eapply symbtable_to_tree_acc_symb_map_inv'; eauto.
  rewrite PTree.gempty; auto.
Qed.


Lemma acc_symb_map_ignore: forall id e t,
    id <> symbentry_id e ->
    (acc_symb_map e t) ! id = t ! id.
Proof.
  intros.
  unfold acc_symb_map. destr; eauto.
  erewrite PTree.gso; auto.
Qed.

Lemma acc_symb_map_get_some_int: forall stbl e t,
    list_norepet (get_symbentry_ids stbl) ->
    In e stbl ->
    is_symbentry_internal e = true ->
    exists b ofs, 
      (fold_right acc_symb_map t stbl) ! (symbentry_id e) 
      = Some (b, ofs).
Proof.
  induction stbl as [|e' stbl].
  - cbn. intros. contradiction.
  - cbn. intros e t NORPT [EQ | IN] INT.
    + subst. unfold is_symbentry_internal in INT.
      destr_in INT. 
      unfold acc_symb_map. rewrite Heqs.
      erewrite PTree.gss. eauto.
    + inv NORPT.
      erewrite acc_symb_map_ignore; eauto.
      intros EQ. rewrite <- EQ in H1.
      apply H1. eapply in_map; eauto.
Qed.

Lemma acc_instr_map_no_effect: forall c ofs' ofs map cz map',
    fold_left acc_instr_map c (ofs', map') = (cz, map) ->
    (Ptrofs.unsigned ofs) < (Ptrofs.unsigned ofs') ->
    map ofs = map' ofs.
Proof.
  induction c as [|i c].
  - cbn. intros. inv H. auto.
  - cbn. intros ofs' ofs map cz map' ACC LE.
    assert (Ptrofs.unsigned ofs < Ptrofs.unsigned (Ptrofs.add ofs' (Ptrofs.repr (instr_size i)))) as LE'.
    { 
      rewrite Ptrofs.add_unsigned.
      repeat rewrite Ptrofs.unsigned_repr. 
      generalize (instr_size_positive i). omega.
      apply instr_size_repr.
      admit.
      apply instr_size_repr.
    }
    generalize (IHc _ _ _ _ _ ACC LE').
    intros MAP'.
    rewrite MAP'.
    destr. subst. omega.
Admitted.

Lemma acc_instr_map_pres_find : forall c i ofs ofs' map map' cz,
    find_instr ofs c = Some i ->
    fold_left acc_instr_map c (ofs', map') = (cz, map) ->
    map (Ptrofs.add ofs' (Ptrofs.repr ofs)) = Some i.
Proof.
  induction c as [|i c].
  - cbn. intros. congruence.
  - intros i1 ofs ofs' map map' cz FIND ACC.
    cbn in FIND. destruct zeq. subst.
    + inv FIND. 
      rewrite Ptrofs.add_zero.
      cbn in ACC.
      erewrite acc_instr_map_no_effect; eauto.
      cbn. destruct Ptrofs.eq_dec; congruence.
      rewrite Ptrofs.add_unsigned.
      rewrite Ptrofs.unsigned_repr. 
      generalize (Ptrofs.unsigned_range (Ptrofs.repr (instr_size i1))).
      rewrite Ptrofs.unsigned_repr. 
      generalize (instr_size_positive i1). omega.
      apply instr_size_repr.
      admit.
    + cbn in ACC.
      exploit IHc; eauto.
      intros MAP.
      rewrite Ptrofs.add_assoc in MAP.
      rewrite <- MAP. f_equal. f_equal.
      rewrite Ptrofs.add_unsigned. 
      rewrite Ptrofs.unsigned_repr. 
      rewrite Ptrofs.unsigned_repr. 
      f_equal. omega.
      admit.
      apply instr_size_repr.
Admitted.


Lemma acc_symb_map_size: forall c ofs map cz map',
    fold_left acc_instr_map c (ofs, map) = (cz, map') -> 
    cz = Ptrofs.add ofs (Ptrofs.repr (code_size c)).
Proof.
  induction c as [|i c].
  - cbn; intros. inv H. rewrite Ptrofs.add_zero. auto.
  - intros ofs map cz map' ACC.
    cbn in ACC.
    apply IHc in ACC. subst.
    rewrite Ptrofs.add_assoc.
    f_equal.
    rewrite Ptrofs.add_unsigned. 
    rewrite Ptrofs.unsigned_repr. 
    rewrite Ptrofs.unsigned_repr. auto.
    admit.
    apply instr_size_repr.
Admitted.


Lemma code_size_bound: forall defs (id:ident) f,
    In (id, Some (Gfun (Internal f))) defs ->
    code_size (fn_code f) <= odefs_size (map snd defs).
Proof.
  induction defs as [|def defs].
  - cbn. intros. contradiction.
  - cbn. intros id f [EQ | IN].
    + subst. cbn. 
      generalize (odefs_size_pos (map snd defs)).
      intros LE.
      apply StackADT.le_add_pos. auto.
    + generalize (IHdefs _ _ IN).
      intros. etransitivity; eauto.
      rewrite Z.add_comm. apply StackADT.le_add_pos.      
      eapply odef_size_pos.
Qed.

Lemma def_code_size_le_odef_size : forall def, 
    def_code_size def <= odef_size def.
Proof.
  intros. destruct def. destruct g. destruct f.
  cbn. omega.
  cbn. omega.
  cbn. generalize (init_data_list_size_pos (gvar_init v)). omega.
  cbn. omega.
Qed.

Lemma pres_find_instr_aux: forall (defs: list (ident * option (globdef fundef unit))) id f ofs i cz t ofs' t',
    list_norepet (map fst defs) ->
    In (id, Some (Gfun (Internal f))) defs ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    (cz, t) = fold_left acc_instr_map (fold_right acc_instrs [] defs) (ofs', t') ->
    t (Ptrofs.add ofs (Ptrofs.add ofs' (Ptrofs.repr (defs_code_size (defs_before id defs))))) = Some i.
Proof.
  clear.
  induction defs as [|def defs].
  - intros.
    cbn in *. contradiction.
  - intros id f ofs i cz t ofs' t' NORPT IN FIND ACC.
    assert (Ptrofs.unsigned ofs' + odefs_size (map snd (def::defs)) <= Ptrofs.max_unsigned) as SZ. 
    { admit. }
    inv NORPT.
    generalize (code_size_bound _ _ _ IN). intros CBN.
    assert (Ptrofs.unsigned ofs' + code_size (fn_code f) <= Ptrofs.max_unsigned) as CBN1.
    { etransitivity; eauto. 
      rewrite <- Z.add_le_mono_l. auto. }
    assert (0 <= code_size (fn_code f) <= Ptrofs.max_unsigned) as CRNG.
    { split. generalize (code_size_non_neg (fn_code f)). omega.
      generalize (Ptrofs.unsigned_range ofs'). intros. inv H.
      etransitivity. exact CBN.
      apply Z_le_add_l_inv with (Ptrofs.unsigned ofs'); auto. }
    generalize (find_instr_bound _ _ _ FIND). intros IBND.
    generalize (instr_size_positive i). intros IPOS. 
    assert (0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned ofs' <= Ptrofs.max_unsigned).
    { split.
      generalize (Ptrofs.unsigned_range ofs'). 
      generalize (Ptrofs.unsigned_range ofs); omega. omega.
    }
    inv IN.
    + cbn in ACC.
      rewrite fold_left_app in ACC.
      rewrite defs_before_head. cbn.
      rewrite Ptrofs.add_zero.
      destruct (fold_left acc_instr_map (fn_code f) (ofs', t'))
               as (cz', t'') eqn:ACC'.
      erewrite acc_instr_map_no_effect; eauto.
      rewrite Ptrofs.add_commut.
      replace ofs with ((Ptrofs.repr (Ptrofs.unsigned ofs))).
      eapply acc_instr_map_pres_find; eauto.
      erewrite Ptrofs.repr_unsigned; auto.
      exploit acc_symb_map_size; eauto.
      intros. subst. 
      rewrite Ptrofs.add_unsigned.
      rewrite Ptrofs.unsigned_repr.
      rewrite Ptrofs.add_unsigned.
      rewrite Ptrofs.unsigned_repr.
      rewrite Ptrofs.unsigned_repr; auto.
      generalize (code_size_non_neg (fn_code f)). intros. omega.
      rewrite Ptrofs.unsigned_repr; auto.
      generalize (Ptrofs.unsigned_range ofs'). omega.
      auto.
      
    + destruct def as (id', def).
      rewrite defs_before_tail.
      rewrite defs_code_size_cons.
      cbn in ACC.
      rewrite fold_left_app in ACC.
      destruct (fold_left acc_instr_map (get_def_instrs def) (ofs', t')) as (ofs'', t'') eqn:ACC1.
      exploit acc_symb_map_size; eauto. intros.
      assert (def_code_size def <= odef_size def) as DCBND.
      { eapply def_code_size_le_odef_size. }
      assert (t (Ptrofs.add ofs (Ptrofs.add ofs'' (Ptrofs.repr (defs_code_size (defs_before id defs))))) = Some i) as IHR.
      { eapply IHdefs; eauto. }
      subst. rewrite <- IHR. f_equal. f_equal.
      rewrite Ptrofs.add_assoc. f_equal.
      rewrite Ptrofs.add_unsigned. f_equal.
      repeat rewrite Ptrofs.unsigned_repr. auto.
      admit.
      admit.
      intros ID. subst. apply H1.
      rewrite in_map_iff. cbn. 
      eexists; split; eauto. cbn. auto.
Admitted.        

Lemma pres_find_instr: forall defs id f ofs i,
    list_norepet (map fst defs) ->
    In (id, Some (Gfun (Internal f))) defs ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    gen_instr_map (fold_right acc_instrs [] defs)
                  (Ptrofs.add ofs (Ptrofs.repr (defs_code_size (defs_before id defs)))) = Some i.
Proof.
  unfold gen_instr_map.
  intros. destr. 
  exploit pres_find_instr_aux; eauto.
  rewrite Ptrofs.add_zero_l. auto.
Qed.

Lemma gen_symb_table_only_internal_symbol_aux: 
  forall did cid defs stbl dz1 cz1 dz2 cz2 id def,
    list_norepet (map fst defs) ->
    is_def_internal is_fundef_internal def = true ->
    fold_left (acc_symb did cid) defs ([], dz1, cz1) = (stbl, dz2, cz2) ->
    In (id, def) defs ->
    only_internal_symbol id (rev stbl).
Proof.
  induction defs as [|def defs].
  - cbn. intros. contradiction.
  - intros stbl dz1 cz1 dz2 cz2 id def1 NORPT INT ACC IN. 
    inv NORPT. cbn in ACC. destruct def as (id1, def).
    destr_in ACC.
    apply acc_symb_inv' in ACC.
    destruct ACC as (stbl1' & EQ & ACC). subst.
    rewrite rev_app_distr. cbn.
    inv IN.
    + inv H. cbn in H1.
      erewrite acc_symb_pres_ids in H1; eauto.
      red. intros. inv H.
      * rewrite <- H3.
        erewrite <- get_symbentry_pres_internal_prop; eauto.
      * exfalso. apply H1.
        unfold get_symbentry_ids.
        rewrite in_map_iff. eauto.
    + cbn in H1.
      red. intros. inv H0.
      * rewrite get_symbentry_id in H. 
        exfalso. apply H1. rewrite in_map_iff. 
        exists (id1, def1). split; auto.
      * eapply IHdefs; eauto.
Qed.
      

Lemma gen_symb_table_only_internal_symbol: 
  forall did cid defs stbl dz cz id def,
    list_norepet (map fst defs) ->
    is_def_internal is_fundef_internal def = true ->
    gen_symb_table did cid defs = (stbl, dz, cz) ->
    In (id, def) defs ->
    only_internal_symbol id stbl.
Proof.
  intros until def.
  intros NORPT INT GS IN.
  unfold gen_symb_table in GS. destr_in GS.
  destruct p. inv GS.
  eapply gen_symb_table_only_internal_symbol_aux; eauto.
Qed.

Lemma norepet_only_internal_symbol: forall stbl e,
    list_norepet (get_symbentry_ids stbl) ->
    In e stbl ->
    is_symbentry_internal e = true ->
    only_internal_symbol (symbentry_id e) stbl.
Proof.
  induction stbl as [|e' stbl].
  - cbn. intros. red. auto.
  - cbn. intros e NORPT [EQ|IN] INT. 
    + subst. inv NORPT.
      red. intros e'' IN' ID.
      inv IN'; auto.
      rewrite <- ID in H1.
      exfalso.
      apply H1. apply in_map; auto.
    + inv NORPT.
      red. intros e'' IN' ID. inv IN'.
      * rewrite ID in H1.
        exfalso. apply H1. 
        apply in_map; auto.
      * generalize (IHstbl _ H2 IN INT).
        intros ONLY.
        red in ONLY. eauto.
Qed.


Definition symbs_before (id:ident) (stbl: symbtable) :=
  elems_before ident_eq id (symbtable_to_idlist stbl).

Lemma symbs_before_tail:
  forall id e stbl,
  id <> (symbentry_id e) ->
  symbs_before id (e :: stbl) = e :: symbs_before id stbl.
Proof.
  intros.
  unfold symbs_before, symbtable_to_idlist.
  cbn [map].
  eapply elems_before_tail; auto.
Qed.
        
Lemma add_external_globals_find_symb : forall stbl e ge extfuns, 
    list_norepet (get_symbentry_ids stbl) ->
    In e stbl ->
    is_symbentry_internal e = false ->
    Genv.find_symbol (add_external_globals extfuns ge stbl) (symbentry_id e) =
    Some (pos_advance_N (Genv.genv_next ge) 
                        (num_of_external_symbs (symbs_before (symbentry_id e) stbl)), 
          Ptrofs.zero).
Proof.
  induction stbl as [|e' stbl].
  - intros e ge extfuns NORPT IN INT. inv IN.
  - intros e ge extfuns NORPT IN INT.
    inv NORPT. inv IN. 
    + cbn. rewrite peq_true. cbn.
      erewrite add_external_globals_pres_find_symbol'; eauto.
      unfold add_external_global, Genv.find_symbol; cbn.
      rewrite INT.
      rewrite PTree.gss. auto.
    + 
      assert (symbentry_id e <> symbentry_id e') as NEQ.
      { 
        intros EQ. rewrite <- EQ in H1.
        apply H1. apply in_map; auto.
      }
      erewrite symbs_before_tail; eauto.
      cbn. erewrite IHstbl; eauto.
      f_equal. destruct (is_symbentry_internal e') eqn:INT'; cbn.
      * rewrite INT'. f_equal.
      * rewrite INT'. f_equal.
Qed.

Lemma add_external_globals_ext_funs : forall stbl extfuns ge e f,
    list_norepet (get_symbentry_ids stbl) ->
    In e stbl ->
    is_symbentry_internal e = false ->
    symbentry_type e = symb_func ->
    extfuns ! (symbentry_id e) = Some f ->
    (Genv.genv_ext_funs (add_external_globals extfuns ge stbl)) ! 
       (pos_advance_N (Genv.genv_next ge) (num_of_external_symbs (symbs_before (symbentry_id e) stbl))) = Some f.
Proof.
  clear.
  induction stbl as [| e' stbl].
  - cbn. intros. contradiction.
  - intros extfuns ge e f NORPT [EQ | IN] INT TYP EXT; inv NORPT.
    + cbn. subst. rewrite peq_true. cbn.
      erewrite add_external_globals_pres_ext_funs; eauto.
      unfold add_external_global; cbn.
      rewrite TYP. rewrite INT. rewrite EXT. 
      rewrite PTree.gss. auto.
      unfold add_external_global; cbn.
      rewrite INT.
      xomega.
    + assert (symbentry_id e <> symbentry_id e') as NEQ.
      { 
        intros EQ. rewrite <- EQ in H1.
        apply H1. eapply in_map; auto.
      }
      rewrite symbs_before_tail; auto.
      cbn.
      generalize (IHstbl _ (add_external_global extfuns ge e') _ _ H2 IN INT TYP EXT).
      intros GET'. rewrite <- GET'.
      f_equal.
      destruct (is_symbentry_internal e') eqn:INT'.
      * cbn. rewrite INT'. auto.
      * cbn. rewrite INT'. auto.
Qed.

Lemma gen_symb_map_internal_block_range: forall stbl e b ofs i,
    list_norepet (get_symbentry_ids stbl) ->
    is_symbentry_internal e = true ->
    symbentry_secindex e = secindex_normal i ->
    (i < 3)%N ->
    In e stbl ->
    (gen_symb_map stbl) ! (symbentry_id e) = Some (b, ofs) ->
    (b < 3)%positive.
Proof.
  induction stbl as [|e' stbl].
  - cbn. intros. contradiction.
  - cbn. intros e b ofs i NORPT INT IDX IDXRNG [EQ|IN] GS; inv NORPT.
    + exploit acc_symb_map_inv; eauto.
      erewrite acc_symb_map_no_effect; eauto.
      apply PTree.gempty.
      intros (OFS & i' & INDX & B). subst. 
      unfold sec_index_to_block. destr; try xomega.
      subst. rewrite IDX in INDX. inv INDX. xomega. 
    + unfold acc_symb_map in GS.
      destr_in GS; eauto.
      rewrite PTree.gso in GS. eauto.
      intros EQ.
      rewrite <- EQ in H1.
      apply H1. apply in_map. auto.
Qed.
      
