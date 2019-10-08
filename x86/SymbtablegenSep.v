Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Asm RelocProgram.
Require Import Symbtablegen.
Require Import Linking RelocLinking.
Require Import SeqTable.
Import ListNotations.

Set Implicit Arguments.

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

Inductive list_in_order (A:Type) (f: A -> bool) : list A -> list A -> Prop :=
| lorder_nil : list_in_order f nil nil
| lorder_left_false : forall e l1 l2, 
    f e = false -> list_in_order f l1 l2 -> list_in_order f (e :: l1) l2
| lorder_right_false : forall e l1 l2,
    f e = false -> list_in_order f l1 l2 -> list_in_order f l1 (e :: l2)
| lorder_true : forall e l1 l2,
    f e = true -> list_in_order f l1 l2 -> list_in_order f (e::l1) (e::l2).

Lemma list_in_order_false_inv : forall (A:Type) (l1' l1 l2: list A) f e,
    f e = false -> l1' = (e :: l1) -> list_in_order f l1' l2 -> list_in_order f l1 l2.
Proof.
  induction 3. 
  - inv H0.
  - inv H0. auto.
  - apply lorder_right_false; auto.
  - inv H0. congruence.
Qed.

Lemma list_in_order_true_inv : forall (A:Type) (l1' l1 l2: list A) f e,
    f e = true -> l1' = (e :: l1) -> list_in_order f l1' l2 -> 
    exists l3 l4, l2 = l3 ++ (e :: l4) /\ 
             Forall (fun e' => f e' = false) l3 /\
             list_in_order f l1 l4.
Proof.
  induction 3.
  - inv H0.
  - inv H0. congruence.
  - subst. 
    generalize (IHlist_in_order eq_refl).
    destruct 1 as (l3 & l4 & EQ & FP & ORDER). subst.
    exists (e0 :: l3), l4. split.
    rewrite <- app_comm_cons. auto. split; auto.
  - inv H0. exists nil, l2. split. auto.
    split; auto.
Qed.

Lemma list_in_order_right_false_list : forall (A:Type) f (l2' l1 l2: list A),
    Forall (fun e : A => f e = false) l2' ->
    list_in_order f l1 l2 -> 
    list_in_order f l1 (l2' ++ l2).
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


Lemma list_in_order_trans : forall (A:Type) f (l1 l2 l3: list A),
    list_in_order f l1 l2 -> list_in_order f l2 l3 -> list_in_order f l1 l3.
Proof.
  intros A f l1 l2 l3 ORDER.
  generalize l3.
  induction ORDER.
  - auto.
  - intros l0 ORDER1. constructor; auto.
  - intros l0 ORDER1. 
    generalize (list_in_order_false_inv H (eq_refl (e::l2)) ORDER1). auto.
  - intros l0 ORDER1.
    generalize (list_in_order_true_inv H (eq_refl (e::l2)) ORDER1).
    destruct 1 as (l2' & l2'' & EQ & FP & ORDER2).
    subst.
    apply IHORDER in ORDER2.
    apply list_in_order_right_false_list; auto.
    apply lorder_true; auto.
Qed.    

Lemma list_in_order_cons : forall (A:Type) f (l1 l2:list A) e,
    list_in_order f l1 l2 -> list_in_order f (e::l1) (e::l2).
Proof.
  intros A f l1 l2 e ORDER.
  destruct (f e) eqn:EQ.
  apply lorder_true; auto.
  apply lorder_left_false; auto.
  apply lorder_right_false; auto.
Qed.

Lemma list_in_order_refl: forall (A:Type) f (l:list A),
    list_in_order f l l.
Proof.
  induction l; intros.
  - apply lorder_nil.
  - apply list_in_order_cons. auto.
Qed.


Lemma partition_pres_list_in_order: forall (A:Type) pf f (l l1 l2: list A),
    partition pf l = (l1, l2) ->
    Forall (fun e => f e = false) l1 ->
    list_in_order f l l2.
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


Lemma extern_var_init_data_nil : forall v,
    is_var_internal v = false ->
    get_def_init_data (Some (Gvar v)) = [].
Proof.
  intros v H. simpl in *. 
  unfold is_var_internal in H. 
  destruct (gvar_init v); try congruence.
  destruct i; try congruence.
  destruct l; try congruence.
Qed.

Lemma extern_init_data_nil : forall def,
    is_def_internal is_fundef_internal def = false -> get_def_init_data def = nil.
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


Definition def_internal (iddef : ident * option (AST.globdef Asm.fundef unit)) :=
  let '(_,def) := iddef in
  is_def_internal is_fundef_internal def.

Lemma acc_init_data_in_order_eq : forall defs1 defs2,
    list_in_order def_internal defs1 defs2 ->
    fold_right acc_init_data [] defs1 = fold_right acc_init_data [] defs2.
Proof.
  induction 1.
  - simpl. auto.
  - destruct e as (id, def). simpl.     
    erewrite extern_init_data_nil; eauto.
  - destruct e as (id, def). simpl.
    erewrite extern_init_data_nil; eauto.
  - destruct e as (id, def). simpl.
    rewrite IHlist_in_order. auto.
Qed.

Lemma is_def_internal_dec' : forall (F V:Type) (f:F -> bool) (def: option (globdef F V)),
    {is_def_internal f def = true} + {is_def_internal f def <> true}.
Proof.
  decide equality.
Qed.

Lemma is_def_internal_dec : forall (F V:Type) (f:F -> bool) (def: option (globdef F V)),
    {is_def_internal f def = true} + {is_def_internal f def = false}.
Proof.
  intros F V f def.
  generalize (is_def_internal_dec' f def).
  intro H.
  inv H. auto.
  rewrite not_true_iff_false in H0. auto.
Qed.


Lemma link_fundef_inv1 : forall (F:Type) (f: AST.fundef F) f' e, 
    link_fundef f (External e) = Some f' -> f = f'.
Proof.
  intros F f f' e LINK.
  destruct f. simpl in *. destruct e; try congruence.
  simpl in LINK. destruct (external_function_eq e0 e); congruence.
Qed.

Lemma link_extern_fundef_inv: forall (F:Type) 
                                (f f' f'': AST.fundef F),
    is_fundef_internal f = false ->
    link f' f = Some f'' -> 
    f' = f''.
Proof.
  intros F f f' f'' FINT LINK.
  unfold link in LINK. 
  Transparent Linker_fundef.
  unfold Linker_fundef in LINK.
  destruct f; simpl in *. congruence.
  simpl in LINK.
  apply link_fundef_inv1 in LINK. auto.
Qed.

Lemma link_extern_gfundef_inv: forall (F V:Type) (LV: Linker V)
                             (f: AST.fundef F) (g g': (globdef (AST.fundef F) V)),
    is_fundef_internal f = false ->
    link g (Gfun f) = Some g' -> 
    g = g'.
Proof.
  intros F V LV f g g' INT LINK.
  destruct g. 
  - unfold link in LINK. 
    Transparent Linker_def.
    unfold Linker_def in LINK.
    simpl in LINK. destruct (link_fundef f0 f) eqn:LINKF; try congruence.
    inv LINK.
    generalize (link_extern_fundef_inv _ _ INT LINKF).
    intros. subst.
    auto.
  - simpl in LINK. congruence.
Qed.


Lemma link_extern_var_inv: forall (V:Type) (LV:Linker V)
                                (v v' v'': globvar V),
    is_var_internal v = false ->
    link v' v = Some v'' -> 
    v' = v''.
Proof.
  intros V LV v v' v'' VINT LINK.
  unfold link in LINK. 
  Transparent Linker_vardef.
  unfold Linker_vardef in LINK.
  unfold link_vardef in LINK.
  destruct (link (gvar_info v') (gvar_info v)) eqn:LINK_INFO; try congruence.
  destruct (link (gvar_init v') (gvar_init v)) eqn:LINK_INIT; try congruence.
  destruct (eqb (gvar_readonly v') (gvar_readonly v) && eqb (gvar_volatile v') (gvar_volatile v)) eqn:EQB; 
    try congruence.
  inv LINK.
  destruct v; simpl in *. 
  unfold link,link in LINK_INFO. 
  
  Admitted.

Lemma link_extern_gvar_inv: forall (F V:Type) (LV: Linker V)
                              (v: globvar V) (g g': (globdef (AST.fundef F) V)),
    is_var_internal v = false ->
    link g (Gvar v) = Some g' -> 
    g = g'.
Proof.
  intros F V LV v g g' INT LINK.
  destruct g. 
  - unfold link in LINK. 
    Transparent Linker_def.
    unfold Linker_def in LINK.
    simpl in LINK. congruence.
  - simpl in LINK. 
    destruct (link_vardef v0 v) eqn:LINKV; try congruence.
    inv LINK.
    generalize (link_extern_var_inv _ _ _ INT LINKV).
    intros. subst.
    auto.
Qed.   


Lemma link_def_inv2 : forall (F V: Type) (LV: Linker V) (def1 def2 def: option (globdef (AST.fundef F) V)),
    def1 <> None ->
    is_def_internal is_fundef_internal def2 = false ->
    link_option def1 def2 = Some def ->
    def = def1.
Proof.
  intros F V LV def1 def2 def NOTNONE INT LINK.
  destruct def2. destruct g.
  - simpl in *. unfold link_option in LINK.
    destruct def1 as [|def1].
    destruct (link g (Gfun f)) eqn:LEQ; try congruence.
    inv LINK.
    generalize (link_extern_gfundef_inv _ _ _ INT LEQ). intros. subst. auto.
    inv LINK.
    congruence.
  - simpl in *. unfold link_option in LINK.
    destruct def1 as [|def1].
    destruct (link g (Gvar v)) eqn:LEQ; try congruence.
    inv LINK.
    generalize (link_extern_gvar_inv _ _ _ INT LEQ). intros. subst. auto.
    congruence.    
  - simpl in *. unfold link_option in LINK.
    destruct def1 as [|def1].
    inv LINK. auto.
    inv LINK. auto.
Qed.


Lemma link_defs1_in_order : forall defs1 defs2 defs1_linked defs1_rest defs2_rest,
    link_defs1 is_fundef_internal defs1 defs2 = Some (defs1_linked, defs1_rest, defs2_rest) ->
    list_in_order def_internal defs1 defs1_linked /\
    list_in_order def_internal defs2 defs2_rest.
Proof.
  induction defs1 as [|def1 defs1'].
  - intros defs2 defs1_linked defs1_rest defs2_rest LINK.
    simpl in *. inv LINK. split.
    constructor.
    apply list_in_order_refl.

  - intros defs2 defs1_linked defs1_rest defs2_rest LINK.
    simpl in LINK. destruct def1 as (id1, def1).
    destruct (link_defs1 is_fundef_internal defs1' defs2) eqn:LINK1; try congruence.
    destruct p as (p, defs2_rest').
    destruct p as (defs1_linked', defs1_rest').
    destruct (partition (fun '(id', _) => ident_eq id' id1) defs2_rest') as (defs2' & defs2_rest'') eqn:PART.
    destruct defs2' as [| iddef2 defs2''].
    + (** No definition with the same id found in defs2 *)
      inv LINK.
      generalize (IHdefs1' _ _ _ _ LINK1).
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
        generalize (IHdefs1' _ _ _ _ LINK1).
        destruct 1 as (LORDER1 & LORDER2). split; auto.
        apply lorder_left_false; auto.

      * destruct (link_option def1 def2) as [def|] eqn:LINK_SYMB; inv LINK.
        (** The right definition is external.
            The linking proceeds normally *)
        generalize (IHdefs1' _ _ _ _ LINK1).
        destruct 1 as (LORDER1 & LORDER2).
        assert (defs2'' = nil). admit.
        subst. split.
        ** destruct def1 as [def1|].
           *** assert (Some def1 <> None) as NEQ by congruence .
               generalize (link_def_inv2 _ def2 NEQ DEFINT2 LINK_SYMB).
               intros. subst.
               apply list_in_order_cons. auto.
           *** simpl in LINK_SYMB. inv LINK_SYMB.
               apply lorder_left_false; auto.
               apply lorder_right_false; auto.
        ** generalize (partition_pres_list_in_order _ def_internal _ PART).
           intros LORDER3.
           apply list_in_order_trans with defs2_rest'; auto.
Admitted.          
          
                
Lemma link_acc_init_data_comm : forall defs1 defs2 defs,
    link_defs is_fundef_internal defs1 defs2 = Some defs ->
    fold_right acc_init_data [] defs = 
    fold_right acc_init_data [] defs1 ++ fold_right acc_init_data [] defs2.
Proof.
  intros defs1 defs2 defs LINK.
  unfold link_defs in LINK.
  destruct (link_defs1 is_fundef_internal defs1 defs2) eqn:LINK1; try inv LINK.
  destruct p as (r & defs2_rest). destruct r as (defs1_linked & defs1_rest).
  destruct (link_defs1 is_fundef_internal defs2_rest defs1_rest) eqn:LINK2; try inv H0.
  destruct p. destruct p as (defs2_linked & p). inv H1.
  rewrite fold_right_app. rewrite <- fold_right_acc_init_data_app.
  apply link_defs1_in_order in LINK1. destruct LINK1 as (ORDER1 & ORDER2).
  apply link_defs1_in_order in LINK2. destruct LINK2 as (ORDER3 & ORDER4).
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

Lemma link_acc_instrs_comm : forall defs1 defs2 defs,
    link_defs is_fundef_internal defs1 defs2 = Some defs ->
    fold_right acc_instrs [] defs = fold_right acc_instrs [] (defs1 ++ defs2).
Admitted.


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

