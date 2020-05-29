(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 23, 2019 *)
(* *******************  *)

(** * Generation of the string table *)
Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SeqTable Memdata.
Require Import SymbolString.
Require Import Hex Bits.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


Definition acc_symbol_strings id r := 
  do idbytes <- r;
  match find_symbol_pos id with
  | None =>     
    Error [MSG "Cannot find the string of the symbol "; CTX id]
  | Some pos_nums =>
    let bytes := map (fun p => Byte.repr (Zpos p)) pos_nums in
    OK ((id, bytes ++ [HB["00"]]) :: idbytes)
  end.

Definition acc_strmap r (idb: ident * list byte) := 
  let '(map,next) := r in
  let '(id, bytes) := idb in
  let map' := PTree.set id next map in
  let next'  := next + Z.of_nat(length bytes) in
  (map', next').

Definition get_strings_map_bytes (symbols: list ident) : res (PTree.t Z * list byte) :=
  do idbytes <-
     fold_right acc_symbol_strings (OK []) symbols;
  let '(strmap, maxofs) := fold_left acc_strmap idbytes (PTree.empty Z, 1) in
  let sbytes := fold_right (fun '(id,bytes) acc => bytes ++ acc) [] idbytes in
  if zlt maxofs Int.max_unsigned then
    OK (strmap, HB["00"] :: sbytes)
  else Error (msg "Too many strings").
                             
Definition create_strtab_section (strs: list byte) := sec_bytes strs.

Definition acc_symbols e ids := symbentry_id e :: ids.

Definition transf_program (p:program) : res program :=
  let symbols :=
      fold_right acc_symbols [] (prog_symbtable p) in
  do r <- get_strings_map_bytes symbols;
  let '(strmap, sbytes) := r in
  let strsec := create_strtab_section sbytes in
  let p' :=
      {| prog_defs := p.(prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_sectable := p.(prog_sectable) ++ [strsec];
        prog_strtable := strmap;
        prog_symbtable := p.(prog_symbtable);
        prog_reloctables := prog_reloctables p;
        prog_senv := p.(prog_senv);
     |} in
  let len := (length (prog_sectable p')) in
  if beq_nat len 4 then
    OK p'
  else
    Error [MSG "In Strtablegen: number of sections is incorrect (not 4): "; POS (Pos.of_nat len)].

Record valid_strtable_thr (bytes: list (ident * list byte)) (strtab: strtable) (o: Z): Prop :=
  {
    nodupstr: forall i j x y bytesx bytesy ox oy,
      strtab ! i = Some x ->
      strtab ! j = Some y ->
      Assoc.get_assoc _ _ peq bytes i = Some bytesx ->
      Assoc.get_assoc _ _ peq bytes j = Some bytesy ->
      i <> j ->
      0 <= ox < Z.of_nat (length bytesx) ->
      0 <= oy < Z.of_nat (length bytesy) ->
      x + ox <> y + oy;
    thr: forall i x bytesx ox,
        strtab ! i = Some x ->
        Assoc.get_assoc _ _ peq bytes i = Some bytesx ->
        0 <= ox < Z.of_nat (length bytesx) ->
        x + ox < o;
    real_string:
      forall i x,
        strtab ! i = Some x ->
        exists bytesx, Assoc.get_assoc _ _ peq bytes i = Some bytesx;
    table_range: forall i x, strtab ! i = Some x -> 0 <= x < two_p 32;
    strtab_no_0:
      forall i : positive, strtab ! i = Some 0 -> False;
  }.

Lemma acc_strmap_fold_lt:
  forall x t z t0 z1,
    fold_left acc_strmap x (t,z) = (t0, z1) ->
    z <= z1.
Proof.
  induction x; simpl; intros; eauto. inv H. omega.
  destr_in H.
  apply IHx in H. omega.
Qed.

Definition valid_strtable x tab :=
  exists o, valid_strtable_thr x tab o /\ o < Int.max_unsigned.

Lemma acc_symbols_in_in_symbols:
  forall s x0 l,
    fold_right acc_symbol_strings (OK l) (fold_right acc_symbols [] s) = OK x0 ->
    forall i,
      In i (map fst x0) ->
      In i (map fst l) \/ exists a, In a s /\ symbentry_id a = i.
Proof.
  induction s; simpl; intros x0 l FOLD i IN. 
  - inv FOLD. auto.
  - unfold acc_symbols at 1 in FOLD.
    destr_in FOLD; eauto.
    unfold acc_symbol_strings at 1 in H10. monadInv H10.
    repeat destr_in EQ0.
    simpl in IN. destruct IN as [eq | IN]; subst.
    right; eexists; split; eauto.
    exploit IHs. eauto. eauto. intros [A | [a0 [INs EQs]]]; eauto.
Qed.

Lemma transf_program_valid_strtable:
  forall pi p (TF: transf_program pi = OK p)
         x (EQ0 : fold_right acc_symbol_strings (OK []) (fold_right acc_symbols [] (prog_symbtable pi)) = OK x)
         (LNR: list_norepet (map symbentry_id (prog_symbtable pi)))
,
    valid_strtable x (prog_strtable p).
Proof.
  intros pi p TF x EQ0 LNR.
  unfold valid_strtable.
  unfold transf_program in TF.
  monadInv TF.

  assert (LNR': list_norepet (map fst x)).
  {
    revert x EQ0 LNR.
    generalize (prog_symbtable pi). clear.
    induction s; simpl; intros; eauto.
    - inv EQ0. constructor.
    - unfold acc_symbols at 1 in EQ0.
      unfold acc_symbol_strings at 1 in EQ0. monadInv EQ0.
      exploit IHs. apply EQ. inv LNR; auto.
      repeat destr_in EQ1. simpl. intros; constructor; auto.
      intro INi.
      eapply acc_symbols_in_in_symbols in INi; eauto. simpl in INi. destruct INi as [[]|(aa & IN & EQa)].
      inv LNR. apply H12.
      rewrite in_map_iff. eexists; split; eauto.
  }
  repeat destr_in EQ1. simpl in *.
  apply beq_nat_true in Heqb.
  destruct (prog_sectable pi); simpl in *; try congruence.
  destruct s; simpl in *; try congruence.
  destruct s; simpl in *; try congruence.
  destruct s; simpl in *; try congruence.
  2: destruct s; simpl in *; try congruence.
  unfold get_strings_map_bytes in EQ.
  rewrite EQ0 in EQ. simpl in EQ. repeat destr_in EQ.
  exists z; split; auto.
  revert z Heqp l0.
  assert (valid_strtable_thr x (PTree.empty Z) 1 /\ 0 < 1).
  {
    split.
    constructor; setoid_rewrite PTree.gempty; congruence.
    omega.
  }
  generalize t.
  destruct H as (VALID & POS).
  revert VALID POS.
  generalize (PTree.empty Z) 1.
  clear -LNR'.
  assert (forall elt, In elt x -> In elt x) by auto. revert H.
  generalize x at 1 4.
  induction x0; simpl.
  - intros; eauto. inv Heqp. auto.
  - intros IN t z VALID POS t0 z1 FOLD LT.
    destr_in FOLD.
    eapply IHx0 in FOLD. auto. eauto.
    constructor; repeat setoid_rewrite PTree.gsspec.
    + intros i0 j x1 y bytesx bytesy ox oy. repeat destr.
      * intros Tx Ty Bx By Diff Ox Oy. inv Tx. inv VALID.
        specialize (thr0 _ _ _ _ Ty By Oy). omega.
      * intros Tx Ty Bx By Diff Ox Oy. inv Ty. inv VALID.
        specialize (thr0 _ _ _ _ Tx Bx Ox). omega.
      * inv VALID; eauto.
    + intros i0 x1 bytesx ox Tx Bx Ox. destr_in Tx.
      * inv Tx. erewrite Assoc.in_lnr_get_assoc in Bx. 3: apply IN; left; reflexivity. inv Bx; omega.
        auto.
      * inv VALID.
        eapply thr0 in Bx; eauto. omega.
    + intros i0 x1 EQ. destr_in EQ.
      * inv EQ. erewrite Assoc.in_lnr_get_assoc; eauto.
      * inv VALID; eauto.
    + intros i0 x1 EQ. destr_in EQ.
      * inv EQ.
        apply acc_strmap_fold_lt in FOLD. change (two_p 32) with (Int.max_unsigned + 1).
        omega.
      * inv VALID; eauto.
    + intros i0 EQ. destr_in EQ. inv EQ.
      omega. inv VALID; eauto.
    + omega.
    + auto.
Qed.
