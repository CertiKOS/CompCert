(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 13, 2019 *)
(* *******************  *)

(** * Template of languages with information about symbols and relocation *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs SeqTable Asm.

(* (** In the programs we use postives (ident) for indexing into various *)
(*     tables.  However, the indexes of tables are natural numbers. *)
(*     Thus, we need to define interpretation of positives into natural *)
(*     numbers for different tables. The following sigature is for this *)
(*     purpose. *) *)
(* Module Type INDEX. *)
(*   Parameter interp : ident -> N. *)
(*   Parameter deinterp : N -> option ident. *)

(*   Axiom interp_round_trip : forall i, deinterp (interp i) = Some i.  *)
(* End INDEX. *)

(* Module IdIndex <: INDEX. *)
(*   Definition interp i := Npos i. *)
(*   Definition deinterp i := match i with *)
(*                            | N0 => None *)
(*                            | Npos p => Some p *)
(*                            end. *)
(*   Lemma interp_round_trip : forall i, deinterp (interp i) = Some i.  *)
(*   Proof. *)
(*     intros i. simpl. auto. *)
(*   Qed. *)

(* End IdIndex. *)

(* Module SubOneIndex <: INDEX. *)
(*   Definition interp i := Pos.pred_N i. *)
(*   Definition deinterp i := Some (N.succ_pos i). *)
(*   Definition deinterp' i := (N.succ_pos i). *)

(*   Lemma interp_round_trip : forall i, deinterp (interp i) = Some i.  *)
(*   Proof. *)
(*     intros i. unfold deinterp, interp. *)
(*     f_equal. unfold N.succ_pos, Pos.pred_N. *)
(*     destruct i. simpl. auto. *)
(*     rewrite Pos.succ_pred_double. auto. *)
(*     auto. *)
(*   Qed. *)

(* End SubOneIndex. *)


(** ** Sections *)

Inductive section : Type :=
| sec_text (code: list instruction)
| sec_data (init: list init_data)
| sec_bytes (bs: list byte).

Definition sec_size (s: section) : Z :=
  match s with
  | sec_text c => code_size c
  | sec_data d => AST.init_data_list_size d
  | sec_bytes bs => Z.of_nat (length bs)
  end.

(** Positive indexes to sections are mapped by the identity function,
    the 0-th section is a pre-defined null section *)
Module SecTblParams.
  Definition V := section.
  Definition ofs := 1%N.
End SecTblParams.

Module SecTable := SeqTable(SecTblParams).
Definition sectable := SecTable.t.

Definition sections_size stbl :=
  fold_left (fun sz sec => sz + (sec_size sec)) stbl 0.

Definition seclabel : Type := ident * Z.

(** ** Symbol table *)
Inductive symbtype : Type := symb_func | symb_data | symb_notype.

Inductive secindex : Type :=
| secindex_normal (idx:N)
| secindex_comm
| secindex_undef.

Inductive bindtype : Type :=
| bind_local
| bind_global.

Record symbentry : Type :=
{
  symbentry_id: ident;  (** The original identifier of the symbol *) 
  symbentry_bind: bindtype;
  symbentry_type: symbtype;
  symbentry_value: Z;  (** This holds the alignment info if secindex is secindex_comm,
                           otherwise, it holds the offset from the beginning of the section *)
  symbentry_secindex: secindex;
  symbentry_size: Z;
}.

(* Definition dummy_symbentry : symbentry := *)
(*   {| symbentry_id := None; *)
(*      symbentry_bind := bind_local; *)
(*      symbentry_type := symb_notype; *)
(*      symbentry_value := 0; *)
(*      symbentry_secindex := secindex_undef; *)
(*      symbentry_size := 0; *)
(*   |}. *)

Definition is_symbol_internal e :=
  match symbentry_secindex e with
  | secindex_normal _ => true
  | _ => false
  end.


(** Positive indexes to symbols are mapped by the identity function,
    the 0-th section is a pre-defined dummy symbol *)
Module SymbTblParams.
  Definition V := symbentry.
  Definition ofs := 1%N.
End SymbTblParams.

Module SymbTable := SeqTable(SymbTblParams).
Definition symbtable := SymbTable.t.

(** ** Relocation table *)
Inductive reloctype : Type := reloc_abs | reloc_rel | reloc_null.

Record relocentry : Type :=
{
  reloc_offset: Z;
  reloc_type  : reloctype;
  reloc_symb  : N;    (* Index into the symbol table *)
  reloc_addend : Z;
}.

Module RelocTblParams.
  Definition V := relocentry.
  Definition ofs := 0%N.
End RelocTblParams.

Module RelocTable := SeqTable(RelocTblParams).
Definition reloctable := RelocTable.t.

(** ** String table *)
Definition strtable := PTree.t Z.

(** ** Definition of program constructs *)
Definition gdef := AST.globdef fundef unit.

Inductive reloctable_id := RELOC_CODE | RELOC_DATA.

Definition reloctable_id_eq: forall (x y: reloctable_id), {x = y} + { x <> y}.
Proof.
  decide equality.
Defined.

Record reloctable_map :=
  {
    reloctable_code: reloctable;
    reloctable_data: reloctable;
  }.

Definition set_reloctable (i: reloctable_id) (rtbl:reloctable) (rmap:reloctable_map) :=
  match i with
  | RELOC_CODE => {| reloctable_code := rtbl; reloctable_data := reloctable_data rmap |}
  | RELOC_DATA => {| reloctable_data := rtbl; reloctable_code := reloctable_code rmap |}
  end.

Definition get_reloctable (i:reloctable_id) (rmap: reloctable_map) :=
  match i with
  | RELOC_CODE => reloctable_code rmap
  | RELOC_DATA => reloctable_data rmap
  end.

Record program : Type := {
  prog_defs: list (ident * option gdef);
  prog_public: list ident;
  prog_main: ident;
  prog_sectable: sectable;
  prog_symbtable: symbtable;
  prog_strtable: strtable;
  prog_reloctables: reloctable_map;
  prog_senv : Globalenvs.Senv.t;
}.

(** Generate the mapping from symbol ids to indexes *)
Definition symb_index_map_type := PTree.t N.

Definition acc_symb_index_map (rs:(N * symb_index_map_type)) (e:symbentry) : N * symb_index_map_type :=
  let '(index, map) := rs in
  let map' := PTree.set (symbentry_id e) index map in
  (N.succ index, map').

Definition gen_symb_index_map (stbl: symbtable) : symb_index_map_type :=
  let '(_, map) := fold_left acc_symb_index_map stbl (SymbTblParams.ofs, PTree.empty N) in
  map.

Definition reloc_ofs_map_type := ZTree.t relocentry.

Definition acc_reloc_ofs_map (e:relocentry) (rs: reloc_ofs_map_type): reloc_ofs_map_type :=
  let ofs := reloc_offset e in
  ZTree.set ofs e rs.

Definition gen_reloc_ofs_map (rtbl: reloctable) :  reloc_ofs_map_type :=
  fold_right acc_reloc_ofs_map (ZTree.empty relocentry) rtbl.

(* Definition prog_to_prog (p: program) : AST.program fundef unit := *)
(*   {| *)
(*     AST.prog_defs := prog_defs p; *)
(*     AST.prog_public := prog_public p; *)
(*     AST.prog_main := prog_main p; *)
(*   |}. *)

(* Coercion prog_to_prog : program >-> AST.program. *)

(** Section table ids *)
Definition sec_data_id     := 1%N.
Definition sec_code_id     := 2%N.
Definition sec_strtbl_id   := 3%N.
Definition sec_symbtbl_id  := 4%N.
Definition sec_rel_data_id := 5%N.
Definition sec_rel_code_id := 6%N.
Definition sec_shstrtbl_id := 7%N.

(** Ultility function s*)
(* Definition add_symb_to_list (t: list (ident * symbentry)) (s:symbentry) := *)
(*   (symbentry_id s, s) :: t. *)
Definition symbtable_to_idlist t := 
  map (fun e => (symbentry_id e, e)) t.

Definition symbtable_to_tree (t:symbtable) : PTree.t symbentry :=
  PTree_Properties.of_list (symbtable_to_idlist t).

(* Definition acc_symb_ids (ids: list ident) (s:symbentry) := *)
(*   symbentry_id s :: ids. *)

Definition get_symbentry_ids (t:symbtable) : list ident :=
  map symbentry_id t.

(** ** Various Properties *)
(* Definition symbentry_id_neq (id:ident) (e:symbentry) := *)
(*   match symbentry_id e with *)
(*   | None => true *)
(*   | Some id' => if ident_eq id id' then false else true *)
(*   end. *)

(* Definition symbentry_id_eq (id:ident) (e:symbentry) := *)
(*   match symbentry_id e with *)
(*   | None => false *)
(*   | Some id' => if ident_eq id id' then true else false *)
(*   end. *)


(* Lemma symbtable_to_tree_ignore_dummy: forall stbl,  *)
(*     symbtable_to_tree (dummy_symbentry :: stbl) = symbtable_to_tree stbl. *)
(* Proof. *)
(*   intros. unfold symbtable_to_tree. cbn. auto. *)
(* Qed. *)

(* Lemma add_symb_to_list_id_eq: forall id e l, *)
(*     symbentry_id_eq id e = true -> add_symb_to_list l e = (id,e)::l. *)
(* Proof. *)
(*   intros id e l EQ. *)
(*   unfold symbentry_id_eq in EQ.  *)
(*   destr_in EQ. destruct ident_eq; try congruence. subst. *)
(*   unfold add_symb_to_list. rewrite Heqo. auto. *)
(* Qed. *)

Lemma symbtable_to_idlist_id_eq : forall stbl id e,
  In (id, e) (symbtable_to_idlist stbl) -> 
  symbentry_id e = id.
Proof.
  induction stbl as [|e stbl]; cbn; intuition.
  inv H0. auto.
Qed.

Import List.ListNotations.
Require Import Permutation.
Require Import LocalLib.

(* Lemma acc_to_list_loop: forall idstbl1 idstbl2, *)
(*     Forall (fun '(id, e) => symbentry_id e = id) idstbl1 -> *)
(*     (fold_left add_symb_to_list (map snd idstbl1) idstbl2) = (rev idstbl1) ++ idstbl2. *)
(* Proof. *)
(*   induction idstbl1 as [|ide idstbl1]. *)
(*   - cbn. auto. *)
(*   - cbn. intros idstbl2 IDEQ. *)
(*     destruct ide as (id,e). *)
(*     inv IDEQ. *)
(*     cbn. *)
(*     rewrite <- app_assoc. *)
(*     auto. *)
(* Qed. *)

(* Lemma add_symb_to_list_inv: forall l1 l2, *)
(*     fold_left add_symb_to_list l1 l2 = fold_left add_symb_to_list l1 [] ++ l2. *)
(* Proof. *)
(*   induction l1 as [|e l1]. *)
(*   - cbn. auto. *)
(*   - cbn. intros.  *)
(*     rewrite IHl1. *)
(*     rewrite (IHl1 (add_symb_to_list nil e)). *)
(*     rewrite <- app_assoc. f_equal. *)
(* Qed. *)

(* Lemma acc_symb_ids_eq: forall ids s,  *)
(*     acc_symb_ids ids s = acc_symb_ids nil s ++ ids. *)
(* Proof. *)
(*   unfold acc_symb_ids. *)
(*   intros. cbn. auto. *)
(* Qed. *)

(* Lemma acc_symb_ids_inv: forall stbl ids, *)
(*     fold_left acc_symb_ids stbl ids = fold_left acc_symb_ids stbl [] ++ ids. *)
(* Proof. *)
(*   induction stbl as [|s stbl]. *)
(*   - intros. cbn. auto. *)
(*   - intros. cbn. *)
(*     erewrite IHstbl. erewrite (IHstbl (acc_symb_ids [] s)). *)
(*     rewrite <- app_assoc. f_equal. *)
(* Qed. *)

Lemma symbtable_to_idlist_permutation: forall stbl stbl',
    Permutation stbl stbl' ->
    Permutation (symbtable_to_idlist stbl)
                (symbtable_to_idlist stbl').
Proof.
  apply Permutation_map.
Qed.

(* Lemma acc_symb_ids_add_symb_eq: forall stbl,  *)
(*     fold_left acc_symb_ids stbl [] = map fst (fold_left add_symb_to_list stbl []). *)
(* Proof. *)
(*   induction stbl as [|e stbl]. *)
(*   - cbn. auto. *)
(*   - cbn.  *)
(*     rewrite add_symb_to_list_inv. *)
(*     rewrite acc_symb_ids_inv. *)
(*     rewrite IHstbl.  *)
(*     rewrite map_app.  *)
(*     f_equal. *)
(* Qed. *)

Lemma get_symbentry_ids_add_symb_eq: forall stbl, 
    get_symbentry_ids stbl = (map fst (symbtable_to_idlist stbl)).
Proof.
  unfold get_symbentry_ids.
  intros.
  unfold symbtable_to_idlist.
  rewrite list_map_compose. cbn. auto.
Qed.

Lemma get_symbentry_ids_permutation: forall stbl stbl',
    Permutation stbl stbl' ->
    Permutation (get_symbentry_ids stbl) (get_symbentry_ids stbl').
Proof.
  unfold get_symbentry_ids.
  intros.
  apply Permutation_map. auto.
Qed.


Lemma in_idstbl_conv: forall idstbl id e,
    Forall (fun '(id, e) => symbentry_id e = id) idstbl ->
    In (id, e) (map  (fun x => (symbentry_id (snd x), snd x)) idstbl) <->
    In (id, e) idstbl.
Proof.
  induction idstbl as [| e idstbl].
  - cbn. split; auto.
  - cbn. intros id e0 FALL; split.
    + intros [IN| IN].
      *  inv IN. rewrite Forall_forall in FALL.
         generalize (FALL _ (in_eq _ _)).
         destruct e. intros. subst. cbn. auto.
      * right. eapply IHidstbl; eauto.
        rewrite Forall_forall in *.
        intros. eapply FALL; eauto. apply in_cons. auto.
    + intros [EQ| IN].
      * subst. cbn.
        rewrite Forall_forall in FALL.
        generalize (FALL _ (in_eq _ _)). 
        intros. subst. auto.
      * right.
        erewrite IHidstbl; eauto.
        rewrite Forall_forall in *.
        intros. eapply FALL; eauto. apply in_cons. auto.
Qed.

Lemma idstbl_id_inv: forall idstbl,
    Forall (fun '(id, e) => symbentry_id e = id) idstbl ->
    (map (fun x : ident * symbentry => symbentry_id (snd x))
         idstbl) =
    map fst idstbl.
Proof.
  induction idstbl as [|e idstbl].
  - cbn. auto.
  - cbn. intros FALL.
    rewrite Forall_forall in FALL.
    generalize (FALL _ (in_eq _ _)).
    destruct e. intros. subst. cbn.
    f_equal. 
    eapply IHidstbl; eauto.
    rewrite Forall_forall. intros. 
    eapply FALL. apply in_cons. auto.
Qed.

Lemma elements_of_symbtable_to_idlist_perm': forall idstbl,
    list_norepet (map fst idstbl) ->
    Forall (fun '(id, e) => symbentry_id e = id) idstbl ->
    Permutation (PTree.elements 
                   (PTree_Properties.of_list
                      (symbtable_to_idlist (map snd idstbl))))
                idstbl.
Proof.
  intros.
  unfold symbtable_to_idlist.
  apply NoDup_Permutation.
  apply NoDup_ptree_elements.
  apply NoDup_map_inv with (f:=fst).
  rewrite NoDup_list_norepet_equiv. auto.
  intros (id,e). split.
  - intros IN.
    apply PTree.elements_complete in IN.
    apply PTree_Properties.in_of_list in IN.
    rewrite list_map_compose in IN.
    eapply in_idstbl_conv; eauto.
  - intros IN.
    apply PTree.elements_correct.
    rewrite list_map_compose; cbn.
    apply PTree_Properties.of_list_norepet.
    rewrite list_map_compose; cbn.
    eapply Permutation_pres_list_norepet; eauto.    
    erewrite idstbl_id_inv; eauto.
    erewrite in_idstbl_conv; eauto.
Qed.

Lemma elements_of_symbtable_to_tree_perm: forall idstbl,
    list_norepet (map fst idstbl) ->
    Forall (fun '(id, e) => symbentry_id e = id) idstbl ->
    Permutation (PTree.elements (symbtable_to_tree (map snd idstbl))) idstbl.
Proof.
  intros stbl NORPT IDEQ.
  unfold symbtable_to_tree.
  eapply elements_of_symbtable_to_idlist_perm'; eauto.
Qed.
