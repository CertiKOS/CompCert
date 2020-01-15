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
  let next'  := next + Z.of_nat(length bytes) + 1 in
  (map', next').

Definition get_strings_map_bytes (symbols: list ident) : res (PTree.t Z * list byte) :=
  do idbytes <-
     fold_right acc_symbol_strings (OK []) symbols;
  let '(strmap, maxofs) := fold_left acc_strmap idbytes (PTree.empty Z, 1) in
  let sbytes := fold_right (fun '(id,bytes) acc => bytes ++ acc) [] idbytes in
  if zlt maxofs Int.max_unsigned then
    OK (strmap, sbytes)
  else Error (msg "Too many strings").
                             
Definition create_strtab_section (strs: list byte) := sec_bytes strs.

Definition acc_symbols e ids := 
  match symbentry_id e with
  | None => ids
  | Some id => id :: ids
  end.

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

Record valid_strtable_thr (strtab: strtable) o: Prop :=
  {
    nodupstr: forall i j x y,
      strtab ! i = Some x -> strtab ! j = Some y -> i <> j ->
      x <> y;
    thr: forall i x, strtab ! i = Some x -> x < o;
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

Definition valid_strtable tab :=
  exists o, valid_strtable_thr tab o /\ o < Int.max_unsigned.

Lemma transf_program_valid_strtable:
  forall pi p (TF: transf_program pi = OK p),
    valid_strtable (prog_strtable p).
Proof.
  intros pi p TF.
  unfold valid_strtable.
  unfold transf_program in TF.
  monadInv TF.
  repeat destr_in EQ0. simpl in *.
  apply beq_nat_true in Heqb.
  destruct (prog_sectable pi); simpl in *; try congruence.
  destruct s0; simpl in *; try congruence.
  destruct s1; simpl in *; try congruence.
  destruct s2; simpl in *; try congruence.
  2: destruct s3; simpl in *; try congruence.
  unfold get_strings_map_bytes in EQ.
  monadInv EQ. repeat destr_in EQ1.
  exists z; split; auto.
  revert z Heqp l0.
  assert (valid_strtable_thr (PTree.empty Z) 1 /\ 0 < 1).
  {
    split.
    constructor; setoid_rewrite PTree.gempty; congruence.
    omega.
  }
  generalize t.
  destruct H as (VALID & POS).
  revert VALID POS.
  generalize (PTree.empty Z) 1.
  clear.
  induction x; simpl.
  - intros; eauto. inv Heqp. eauto.
  - intros t z VALID POS t0 z1 FOLD LT.
    destr_in FOLD.
    eapply IHx in FOLD. auto.
    constructor; repeat setoid_rewrite PTree.gsspec.
    + intros i0 j x0 y. repeat destr.
      * intros A; inv A. inv VALID. intro B; apply thr0 in B. omega.
      * subst. intro B. inv VALID. apply thr0 in B. intro A; inv A. omega.
      * inv VALID; eauto.
    + intros i0 x0. destr.
      * intro A; inv A.
        omega.
      * inv VALID. intro A; apply thr0 in A. omega.
    + intros i0 x0 EQ. destr_in EQ.
      * inv EQ.
        apply acc_strmap_fold_lt in FOLD. change (two_p 32) with (Int.max_unsigned + 1).
        omega.
      * inv VALID; eauto.
    + intros i0 EQ. destr_in EQ. inv EQ.
      omega. inv VALID; eauto.
    + omega.
    + auto.
Qed.
