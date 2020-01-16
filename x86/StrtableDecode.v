(* ********************  *)
(* Author: Pierre Wilke  *)
(* Date:   Dec 8th, 2019 *)
(* ********************  *)

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
Require Import StrtableEncode.
Require Import Lia.
Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.



Variable string_to_ident : list byte -> option ident.
Axiom string_to_ident_symbol_to_pos:
  forall s lb, find_symbol_pos s = Some lb ->
               string_to_ident (map (fun p => Byte.repr (Zpos p)) lb) = Some s.

Fixpoint split_bytes (l: list byte) (cur: list byte) (acc: list (list byte)) :=
  match l with
    [] => acc
  | b::r => if Byte.eq b (HB["00"])
            then split_bytes r [] (acc ++ [rev cur])
            else split_bytes r (b::cur) acc
  end.

Definition byte_to_string elt acc :=
  do r <- acc;
    match string_to_ident elt with
    | Some id => OK (id::r)
    | _ => Error []
    end.

Definition decode_string_map (l: list byte) : res (list ident) :=
  let strings := split_bytes l [] [] in
  fold_right byte_to_string (OK []) strings.

Lemma acc_symbol_strings_ok:
  forall symbols idbytes,
    fold_right acc_symbol_strings (OK []) symbols = OK idbytes ->
    list_forall2 (fun '(id, bytes) s => s = id /\
                                        exists nums,
                                          find_symbol_pos id = Some nums /\
                                          bytes = map (fun p => Byte.repr (Zpos p)) nums ++ [HB["00"]])
                 idbytes symbols.
Proof.
  induction symbols; simpl; intros; eauto.
  - inv H; constructor.
  - destruct (fold_right acc_symbol_strings (OK []) symbols) eqn:FR; simpl in *; try congruence.
    destr_in H. inv H. specialize (IHsymbols _ eq_refl).
    constructor; auto.
    split; auto.
    eexists; split; eauto.
Qed.

Axiom find_symbol_pos_ok_bytes:
  forall p nums,
    find_symbol_pos p = Some nums ->
    Forall (fun p => Pos.lt p 256) nums.

Definition split_bytes_simpl:
  forall nums l cur acc,
    Forall (fun p => Pos.lt p 256) nums ->
    split_bytes
      ((map (fun p : positive => Byte.repr (Z.pos p)) nums ++ [Byte.repr 0]) ++ l) cur acc =
    split_bytes l [] (acc ++ [rev cur ++ map (fun p : positive => Byte.repr (Z.pos p)) nums]).
Proof.
  induction nums; simpl; intros; eauto.
  - rewrite Byte.eq_true. rewrite app_nil_r. auto.
  - rewrite Byte.eq_false. rewrite IHnums. simpl. f_equal. f_equal. f_equal.
    rewrite <- app_assoc. simpl. reflexivity.
    inv H; auto.
    inv H.
    intro EQ.
    apply (f_equal Byte.unsigned) in EQ.
    rewrite Byte.unsigned_repr_eq in EQ.
    change (Byte.repr 0) with Byte.zero in EQ. rewrite Byte.unsigned_zero in EQ.
    rewrite Z.mod_small in EQ. inv EQ.
    change Byte.modulus with 256.
    lia.
Qed.

Lemma split_bytes_acc:
  forall l cur acc,
    split_bytes l cur acc = acc ++ split_bytes l cur [].
Proof.
  induction l; simpl; intros; eauto.
  rewrite app_nil_r; auto.
  destr.
  rewrite (IHl _ (acc ++ [rev cur])).
  rewrite (IHl _ [rev cur]). simpl.
  rewrite <- app_assoc. simpl. auto.
Qed.

Lemma fold_right_change_acc:
  forall l acc,
    fold_right byte_to_string (OK acc) l  =
    do result <- fold_right byte_to_string (OK []) l;
      OK (result ++ acc).
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl.
  destruct (fold_right byte_to_string (OK []) l).
  simpl. destr.
  simpl. auto.
Qed.

Lemma decode_string_map_correct: forall (symbols: list ident) idbytes,
    fold_right acc_symbol_strings (OK []) symbols = OK idbytes ->
    let strbytes := fold_right (fun '(_, bytes) (acc : list byte) => bytes ++ acc) [] idbytes in
    decode_string_map strbytes = OK (symbols).
Proof.
  unfold decode_string_map. intros.
  apply acc_symbol_strings_ok in H.
  induction H; simpl; intros; eauto.
  destr_in H. subst. destruct H as (? & nums & FS & ?). subst.
  simpl.
  rewrite split_bytes_simpl.
  - simpl.
    rewrite split_bytes_acc. simpl.
    rewrite IHlist_forall2. simpl.
    erewrite string_to_ident_symbol_to_pos; eauto.
  - eapply find_symbol_pos_ok_bytes; eauto.
Qed.

Lemma decode_string_map_correct':
  forall symbols strmap strbytes,
    get_strings_map_bytes symbols = OK (strmap, strbytes) ->
    decode_string_map strbytes = OK (symbols).
Proof.
  unfold get_strings_map_bytes. intros symbols strmap strbytes H.
  monadInv H.
  apply decode_string_map_correct in EQ.
  repeat destr_in EQ0.
Qed.

Definition decode_strtable_section (s: section): res (list ident * PTree.t Z) :=
  match s with
  | sec_bytes bytes =>
    do symbols <- decode_string_map bytes;
      do (strmap, _) <- get_strings_map_bytes symbols;
      OK(symbols, strmap)
  | _ => Error []
  end.

Definition correct_encoding_strtable_program p : Prop :=
  match nth_error (prog_sectable p) 3 with
  | None => False
  | Some s =>
    match decode_strtable_section s with
    | Error _ => False
    | OK (symbs, strmap) =>
      prog_strtable p = strmap /\ symbs = fold_right acc_symbols [] (prog_symbtable p)
    end
  end.

Lemma transf_program_correct p p' (TF: transf_program p = OK p'):
  correct_encoding_strtable_program p'.
Proof.
  unfold transf_program in TF.
  monadInv TF.
  repeat destr_in EQ0.
  simpl in *.
  unfold correct_encoding_strtable_program. simpl.
  rewrite app_length in Heqb. rewrite Nat.eqb_eq in Heqb.
  destruct (prog_sectable p); simpl in *; try congruence.
  destruct s0; simpl in *; try congruence.
  destruct s1; simpl in *; try congruence.
  destruct s2; simpl in *; try congruence; try lia.
  erewrite decode_string_map_correct'; eauto. simpl.
  rewrite EQ. simpl. auto.
Qed.

Fixpoint take_drop {A} n (l: list A) : res (list A * list A) :=
  match n, l with
  | O, l => OK ([], l)
  | S n, a::r =>
    do (a1,b1) <- take_drop n r ;
    OK (a::a1, b1)
  | S n, [] => Error (msg "take_drop: list too short")
  end.

Definition transf_program_inv p :=
  match nth_error (prog_sectable p) 3 with
  | None => Error (msg "Found no section for strtable")
  | Some s =>
    match decode_strtable_section s with
    | Error e => Error (msg "Unable to decode strtable")
    | OK (symbs, strmap) =>
      do (sectable, _) <- take_drop 3 (prog_sectable p);
        OK {|
        prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := sectable;
        prog_symbtable := prog_symbtable p;
        prog_strtable := PTree.empty Z;
        prog_reloctables := prog_reloctables p;
        prog_senv := prog_senv p |}
    end
  end.

Theorem transf_program_inv_correct p p'
        (EMPTYSTR: prog_strtable p = PTree.empty Z)
        (TP: transf_program p = OK p'):
  transf_program_inv p' = OK p.
Proof.
  unfold transf_program in TP.
  monadInv TP. destr_in EQ0. destr_in EQ0. inv EQ0. simpl in *.
  unfold transf_program_inv. simpl.
  apply beq_nat_true in Heqb.
  destruct (prog_sectable p) eqn:?; simpl in *; try congruence.
  destruct s0; simpl in *; try congruence.
  destruct s1; simpl in *; try congruence.
  destruct s2; simpl in *; try congruence.
  2: destruct s3; simpl in *; try congruence.
  erewrite decode_string_map_correct'. 2: eauto. simpl.
  rewrite EQ. simpl.
  f_equal. destruct p; simpl in *. f_equal; simpl in *; auto.
Qed.
