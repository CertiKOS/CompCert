(** Gang Tan: Bi-directional grammars for both parsing and pretty-printing *)

(** This file provides bit-level bigrammars for parsing and pretty-printing
    individual x86 instructions. *)

Require Import Coq.Init.Logic.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Program.

Require Import Coqlib.
Require Import CommonTacs.
Require Import Shared.Maps.

Unset Automatic Introduction.
Set Implicit Arguments.

(* Module X86_PARSER. *)
  (* Commented out because the Parser is no longer a functor, due to the
     bug with Extraction Implicit. 
     Module X86_BASE_PARSER := Parser.Parser(X86_PARSER_ARG).
  *)
  Require Import X86Syntax.
  Require X86Model.ParserArg.
  Import ParserArg.X86_PARSER_ARG.
  Require Import X86Model.BiGrammar.

  Definition int_t := User_t Int_t.
  Definition register_t := User_t Register_t.
  Definition byte_t := User_t Byte_t.
  Definition half_t := User_t Half_t.
  Definition word_t := User_t Word_t.
  Definition double_word_t := User_t Double_Word_t.
  Definition ten_byte_t := User_t Ten_Byte_t.
  Definition scale_t := User_t Scale_t.
  Definition condition_t := User_t Condition_t.
  Definition fpu_register_t := User_t Fpu_Register_t.
  Definition fp_debug_register_t := User_t Fp_Debug_Register_t.
  Definition fp_condition_t := User_t Fp_Condition_t.
  Definition mmx_granularity_t := User_t MMX_Granularity_t.
  Definition mmx_operand_t := User_t MMX_Operand_t.
  Definition mmx_register_t := User_t MMX_Register_t.
  Definition sse_operand_t := User_t SSE_Operand_t.
  Definition sse_register_t := User_t SSE_Register_t.
  Definition address_t := User_t Address_t.
  Definition operand_t := User_t Operand_t.
  Definition reg_or_immed_t := User_t Reg_or_Immed_t.
  Definition fp_operand_t := User_t Fp_Operand_t.  
  Definition i_instr1_t := User_t I_Instr1_t.
  Definition i_instr2_t := User_t I_Instr2_t.
  Definition i_instr3_t := User_t I_Instr3_t.
  Definition i_instr4_t := User_t I_Instr4_t.
  Definition i_instr5_t := User_t I_Instr5_t.
  Definition i_instr6_t := User_t I_Instr6_t.
  Definition f_instr1_t := User_t F_Instr1_t.
  Definition f_instr2_t := User_t F_Instr2_t.
  Definition m_instr_t := User_t M_Instr_t.
  Definition s_instr1_t := User_t S_Instr1_t.
  Definition s_instr2_t := User_t S_Instr2_t.
  Definition instruction_t := User_t Instruction_t.
  Definition control_register_t := User_t Control_Register_t.
  Definition debug_register_t := User_t Debug_Register_t.
  Definition segment_register_t := User_t Segment_Register_t.
  Definition lock_or_rep_t := User_t Lock_or_Rep_t.
  Definition bool_t := User_t Bool_t.
  Definition prefix_t := User_t Prefix_t.
  Definition bitvector_t n := User_t (BitVector_t n).
  Definition selector_t := User_t (BitVector_t 15).

  (* Mapping old definitions to new . *)
  Notation char_t := Char_t.
  Notation list_t := List_t.
  Notation unit_t := Unit_t.
  Notation pair_t := Pair_t.
  Notation sum_t := Sum_t.
  Notation option_t := Option_t.

  Local Ltac localcrush :=
    intros;
    repeat match goal with
      | [ |- invertible _ _ ] => invertible_tac
      | _ => crush
    end.
  
  Local Ltac localsimpl :=
    repeat match goal with
      | [v: unit |- _ ] => destruct v
      | [H: wf_bigrammar _ |- wf_grammar _] => destruct H
      | _ => unfold in_bigrammar_rng in *; in_bigrammar_inv; localcrush
    end.

  Local Ltac lineararith := 
    unfold two_power_nat, shift_nat in *; simpl in *; omega.


  Ltac ins_destruct_var v :=
    match goal with
    | [H: match v with true => _ | false => _ end = _ |- _] =>
      case v as []
    | [ H: match v with | EAX => _ | ECX => _ | EDX => _ | EBX => _
                   | ESP => _ | EBP => _ | ESI => _ | EDI => _ end
           = _ |- _ ] =>
      case v as []
    | [ H: match v with | Imm_op _ => _ | Reg_op _ => _
                   | Address_op _ => _ | Offset_op _ => _ end
           = _ |- _ ] =>
      case v as []
    | [ H: match v with | Reg_ri _ => _ | Imm_ri _ => _ end
           = _ |- _ ] =>
      case v as []
    | [ H: match v with | ES => _ | CS => _ | SS => _ | DS => _
                   | FS => _ | GS => _ end
           = _ |- _ ] =>
      case v as []
    end.

  Ltac ins_parsable_tac :=
    parsable_tac_gen ibr_sim ins_destruct_var.

  Obligation Tactic := localcrush.

  (** * Basic operators for converting values between types including bits_n, (Z->bool), int n, Z, etc. *)

  (** ** Definitions *)

  Fixpoint bits_n (n:nat) : type := 
    match n with 
      | 0%nat => unit_t
      | S n => pair_t char_t (bits_n n)
    end.

  (* A signature function that is false above an index n *)
  Definition sig_false_above (n:nat) (f:Z->bool) := 
    forall z, (z >= Z_of_nat n)%Z -> f z = false.

  (** convert a sequence of bits to a signature function that maps position
     indexes to bits so that we are not restricted by the
     right-associateness of the bits when processing them; position indexes
     in the signature function start at 0 *)
  Fixpoint sig_of_bitsn (n:nat) : interp (bits_n n) -> (Z -> bool) := 
    match n with
      | O => fun _ _ => false
      | S n' => 
        fun v =>
          let f' := sig_of_bitsn n' (snd v) in
          fun x => if zeq x (Z_of_nat n') then fst v else f' x
    end.

  Fixpoint bitsn_of_sig (n:nat) (f:Z->bool) : interp (bits_n n) :=
    match n with
      | O => tt
      | S n' => (f (Z_of_nat n'), bitsn_of_sig n' f)
    end.

  (* Definition bits_sig (n:nat) := {f:Z->bool | sig_false_above n f}. *)

  (* Fixpoint sig_of_bits (n:nat) : interp (bits_n n) -> bits_sig n.  *)
  (*   intros n. *)
  (*   refine( *)
  (*     match n return interp (bits_n n) -> bits_sig n with *)
  (*       | O => fun _ => exist _ (fun _:Z => false) _ *)
  (*       | S n' => *)
  (*         fun v => *)
  (*           let f' := sig_of_bits n' (snd v) in *)
  (*           exist _ (fun x => if zeq x (Z_of_nat n') *)
  (*                             then fst v else (` f') x) _ *)
  (*     end). *)
  (*   - crush. *)
  (*   - unfold sig_false_above. *)
  (*     intros z H. *)
  (*     destruct_head.  *)
  (*     + nat_to_Z; omega. *)
  (*     + apply (proj2_sig f'). nat_to_Z; omega. *)
  (* Defined. *)

  (* Fixpoint bits_of_sig (n:nat) : bits_sig n -> interp (bits_n n) := *)
  (*   match n return bits_sig n -> interp (bits_n n) with *)
  (*     | O => fun _ => tt *)
  (*     | S n' => fun f => ((` f) (Z_of_nat n'), @bits_of_sig n' f) *)
  (*   end. *)

  Definition int_of_bitsn (n:nat) (v:interp (bits_n n)) : interp int_t := 
    Word.Z_of_bits n (sig_of_bitsn n v).

  Definition bitsn_of_int (n:nat) (i:interp int_t) : option (interp (bits_n n)) := 
    if (zle (0%Z) i) then
      if (zlt i (two_power_nat n)) then 
        Some (bitsn_of_sig n (Word.bits_of_Z n i))
      else None
    else None.

  (* Compared to repr (Z_of_bits f), this one doesn't do the extra modular op *)
  Definition intn_of_sig (n:nat) (f:Z->bool): Word.int n :=
    Word.mkint _ (Word.Z_of_bits (S n) f) (Word.Z_of_bits_range n f).

  Definition sig_of_intn (n:nat) (i:Word.int n) : Z->bool :=
    Word.bits_of_Z (S n) (Word.unsigned i).

  Definition intn_of_bitsn (n:nat) (bs:[|bits_n (S n)|]) : Word.int n :=
    intn_of_sig n (sig_of_bitsn (S n) bs).

  Definition bitsn_of_intn (n:nat) (v:Word.int n) : [|bits_n (S n)|] := 
    bitsn_of_sig (S n) (sig_of_intn v).

  (* Definition matches a register with a list of booleans that 
   * represents its bit encoding. *)
  Definition register_to_Z r : Z :=
    (match r with
      | EAX => 0
      | ECX => 1
      | EDX => 2
      | EBX => 3
      | ESP => 4
      | EBP => 5
      | ESI => 6
      | EDI => 7
    end)%Z.


  Definition condition_type_to_Z (ct: condition_type) : Z := 
    (match ct with
      | O_ct => 0 (* overflow *)
      | NO_ct => 1 (* not overflow *)
      | B_ct => 2 (* below, not above or equal *)
      | NB_ct => 3 (* not below, above or equal *)
      | E_ct => 4 (* equal, zero *)
      | NE_ct => 5 (* not equal, not zero *)
      | BE_ct => 6 (* below or equal, not above *)
      | NBE_ct => 7 (* not below or equal, above *)
      | S_ct => 8 (* sign *)
      | NS_ct => 9 (* not sign *)
      | P_ct => 10 (* parity, parity even *)
      | NP_ct => 11 (* not parity, parity odd *)
      | L_ct => 12  (* less than, not greater than or equal to *)
      | NL_ct => 13 (* not less than, greater than or equal to *)
      | LE_ct => 14 (* less than or equal to, not greater than *)
      | NLE_ct => 15
    end)%Z.

  Definition scale_to_Z s := (match s with
                               | Scale1 => 0
                               | Scale2 => 1
                               | Scale4 => 2
                               | Scale8 => 3
                              end)%Z.


  (** ** Lemmas about the above conversion operators *)

  Lemma sig_of_bitsn_false_above n (v: [|bits_n n|]) :
    sig_false_above n (sig_of_bitsn n v).
  Proof. induction n.
    - crush.
    - unfold sig_false_above.
      intros v z H. simpl.
      destruct_head.
      + nat_to_Z; omega.
      + apply IHn. nat_to_Z; omega.
  Qed.

  Instance bitsn_of_sig_exten n:
    Proper (Word.sig_eq_below n ==> eq) (bitsn_of_sig n).
  Proof. induction n. crush.
    intros f1 f2 H.
    simpl. f_equiv.
    - apply H; nat_to_Z; omega.
    - apply IHn. apply Word.sig_eq_below_downward_step. trivial.
  Qed.

  Lemma bitsn_of_sig_inv : forall n v, bitsn_of_sig n (sig_of_bitsn n v) = v.
  Proof. induction n. crush.
    simpl; intros.
    destruct_head; try omega.
    assert (H: Word.sig_eq_below n 
              (fun x => if zeq x (Z.of_nat n) then fst v
                        else sig_of_bitsn n (snd v) x)
              (sig_of_bitsn n (snd v))).
       unfold Word.sig_eq_below.
       intros. destruct_head; try omega. trivial.
    rewrite H.
    destruct v. crush.
  Qed.

  Lemma sig_of_bitsn_inv :
    forall n f, Word.sig_eq_below n (sig_of_bitsn n (bitsn_of_sig n f)) f.
  Proof. 
    unfold Word.sig_eq_below. induction n.
    - simpl. intros. omega.
    - crush.
      destruct_head. congruence.
        rewrite Zpos_P_of_succ_nat in *.
        eapply IHn.
        omega.
  Qed.

  Hint Rewrite bitsn_of_sig_inv sig_of_bitsn_inv : inv_db.

  Lemma int_of_bitsn_range n v : (0 <= int_of_bitsn n v < two_power_nat n)%Z.
  Proof. unfold int_of_bitsn. intros.
    destruct n. 
      crush. 
      unfold two_power_nat, shift_nat. simpl. omega.
      apply Word.Z_of_bits_range.
  Qed.
  
  Lemma bitsn_of_int_inv n v: bitsn_of_int n (int_of_bitsn n v) = Some v.
  Proof. 
    unfold bitsn_of_int; intros.
    use_lemma (int_of_bitsn_range n v) by trivial.
    repeat (destruct_head; try omega).
    unfold int_of_bitsn. 
    autorewrite with inv_db. trivial.
  Qed.

  Lemma int_of_bitsn_inv : 
    forall n i v, bitsn_of_int n i = Some v -> int_of_bitsn n v = i.
  Proof.
    unfold int_of_bitsn, bitsn_of_int in *. intros.
    destruct_head in H; try congruence.
    destruct_head in H; try congruence.
    crush.
    autorewrite with inv_db.
    destruct n. 
      unfold two_power_nat, shift_nat in *. simpl in *. omega.
      apply Word.Z_of_bits_of_Z_lt_modulus.
      crush.
  Qed.

  Hint Rewrite bitsn_of_int_inv: inv_db.

  Instance intn_of_sig_exten n:
    Proper (Word.sig_eq_below (S n) ==> eq) (@intn_of_sig n).
  Proof. unfold Proper, respectful. intros.
    apply Word.mkint_eq.
    rewrite H. trivial.
  Qed.

  Lemma intn_of_sig_inv : forall n (i:Word.int n),
    @intn_of_sig n (sig_of_intn i) = i.
  Proof. unfold intn_of_sig, sig_of_intn. intros.
    destruct i. apply Word.mkint_eq.
    compute [Word.unsigned Word.intval].
    apply Word.Z_of_bits_of_Z_lt_modulus. trivial.
  Qed.

  Lemma sig_of_intn_inv: forall n f,
    Word.sig_eq_below (S n) (sig_of_intn (@intn_of_sig n f)) f.
  Proof. unfold intn_of_sig, sig_of_intn. intros.
    apply Word.bits_of_Z_of_bits.
  Qed.

  Hint Rewrite intn_of_sig_inv sig_of_intn_inv: inv_db.

  Lemma intn_of_bitsn_inv n (i:Word.int n) :
    intn_of_bitsn (bitsn_of_intn i) = i.
  Proof. unfold intn_of_bitsn, bitsn_of_intn; intros.
    autorewrite with inv_db. trivial.
  Qed.

  Lemma bitsn_of_intn_inv n (v:[|bits_n (S n)|]):
    bitsn_of_intn (intn_of_bitsn v) = v.
  Proof. unfold intn_of_bitsn, bitsn_of_intn; intros.
    autorewrite with inv_db. trivial.
  Qed.

  Hint Rewrite intn_of_bitsn_inv bitsn_of_intn_inv: inv_db.

  Local Ltac toztac := 
    repeat match goal with 
             | [w:Z |- _ ] => destruct w; (discriminate || eauto)
             | [ _ : context[match ?p with xH => _ | xI _  | xO _ => _ end] |- _ ]
               => destruct p; (discriminate || eauto)
           end.

  Lemma register_to_Z_inv : 
    forall z, (0 <= z < 8)%Z -> register_to_Z (Z_to_register z) = z.
  Proof. intros.
    remember (Z_to_register z) as r; destruct r; unfold Z_to_register in *; 
    toztac; simpl in *; pos_to_Z; omega.
  Qed.

  Lemma Z_to_register_inv : forall r, Z_to_register (register_to_Z r) = r.
  Proof. destruct r; crush. Qed.

  Lemma condition_type_to_Z_inv : 
    forall z, (0 <= z < 16)%Z -> condition_type_to_Z (Z_to_condition_type z) = z.
  Proof. intros.
    remember (Z_to_condition_type z) as ct;
    destruct ct; unfold Z_to_condition_type in *;
    toztac;
    simpl in *; pos_to_Z; omega.
  Qed.

  Lemma Z_to_condition_type_inv : 
    forall ct, Z_to_condition_type (condition_type_to_Z ct) = ct.
  Proof. destruct ct; crush. Qed.

  Lemma scale_to_Z_inv : 
    forall z, (0 <= z < 4)%Z -> scale_to_Z (Z_to_scale z) = z.
  Proof. intros.
    remember (Z_to_scale z) as r; destruct r; unfold Z_to_scale in *; 
    toztac; simpl in *; pos_to_Z; omega.
  Qed.

  Lemma Z_to_scale_inv : forall r, Z_to_scale (scale_to_Z r) = r.
  Proof. destruct r; crush. Qed.

  
  (* testing if a signed (n1+1)-bit immediate can be represented in a
     (n2+1)-bit immediate without loss of precision *)
  Definition repr_in_signed n1 n2 (w:Word.int n1) :=
    (Word.min_signed n2 <= Word.signed w <= Word.max_signed n2)%Z.

  Definition repr_in_signed_dec n1 n2 (w:Word.int n1) :
    {repr_in_signed n2 w} + {~(repr_in_signed n2 w)}.
    intros.
    refine (
      match (Z_le_dec (Word.signed w) (Word.max_signed n2)), 
            (Z_le_dec (Word.min_signed n2) (Word.signed w)) with
        | left _, left _ => left _ 
        | _, _ => right _
      end); unfold repr_in_signed; intuition.
  Defined.

  Definition repr_in_signed_byte (w:int32) := repr_in_signed 7 w.
  Definition repr_in_signed_halfword (w:int32) := repr_in_signed 15 w.

  Definition repr_in_signed_byte_dec (w:int32) :
    {repr_in_signed_byte w} + {~(repr_in_signed_byte w)} :=
    repr_in_signed_dec 7 w.

  Definition repr_in_signed_halfword_dec (w:int32) :
    {repr_in_signed_halfword w} + {~(repr_in_signed_halfword w)} :=
    repr_in_signed_dec 15 w.

  Lemma sign_extend_inv1 n1 n2 (w:Word.int n2):
    n1 <= n2 -> repr_in_signed n1 w ->
    @sign_extend n1 n2 (@sign_extend n2 n1 w) = w.
  Proof. unfold sign_extend; intros.
    rewrite Word.signed_repr by trivial.
    rewrite Word.repr_signed; trivial.
  Qed.

  Lemma sign_extend_inv2 n1 n2 (w:Word.int n2):
    n2 <= n1 -> @sign_extend n1 n2 (@sign_extend n2 n1 w) = w.
  Proof. unfold sign_extend; intros.
    assert (Word.min_signed n1 <= Word.signed w <= Word.max_signed n1)%Z.
      generalize (Word.signed_range n2 w).
      use_lemma max_signed_mono by eassumption.
      use_lemma min_signed_mono by eassumption.
      omega.
    rewrite Word.signed_repr by assumption.
    rewrite Word.repr_signed; trivial.
  Qed.

  Lemma repr_in_signed_extend n1 n2 n3 w:
    n1 <= n3 -> n1 <= n2 ->
    repr_in_signed n2 (@sign_extend n1 n3 w).
  Proof. unfold repr_in_signed, sign_extend; intros.
    generalize (Word.signed_range n1 w); intros.
    assert (Word.min_signed n3 <= Word.signed w <= Word.max_signed n3)%Z.
      use_lemma (@max_signed_mono n1 n3) by eassumption.
      use_lemma (@min_signed_mono n1 n3) by eassumption.
      omega.
    rewrite Word.signed_repr by assumption.
    use_lemma (@max_signed_mono n1 n2) by eassumption.
    use_lemma (@min_signed_mono n1 n2) by eassumption.
    omega.
  Qed.

  Definition sign_shrink32_8 := @sign_extend 31 7.
  Definition sign_shrink32_16 := @sign_extend 31 15.

  Lemma sign_extend8_32_inv (w:int32) : 
    repr_in_signed_byte w -> sign_extend8_32 (sign_shrink32_8 w) = w.
  Proof. unfold sign_extend8_32, sign_shrink32_8, repr_in_signed_byte. intros.
    apply sign_extend_inv1; [omega | trivial].
  Qed.
  
  Lemma sign_shrink32_8_inv (b:int8) : 
    sign_shrink32_8 (sign_extend8_32 b) = b.
  Proof. unfold sign_extend8_32, sign_shrink32_8. intros.
    apply sign_extend_inv2; omega.
  Qed.
  Hint Rewrite sign_shrink32_8_inv: inv_db.
  Hint Rewrite sign_extend8_32_inv using assumption: inv_db.

  Lemma repr_in_signed_byte_extend8_32 b: 
    repr_in_signed_byte (sign_extend8_32 b).
  Proof. unfold repr_in_signed_byte, sign_extend8_32; intros.
    apply repr_in_signed_extend; omega.
  Qed.

  Lemma sign_extend16_32_inv (w:int32) : 
    repr_in_signed_halfword w -> sign_extend16_32 (sign_shrink32_16 w) = w.
  Proof. unfold sign_extend16_32, sign_shrink32_16, repr_in_signed_halfword. intros.
    apply sign_extend_inv1; [omega | trivial].
  Qed.
  
  Lemma sign_shrink32_16_inv (hw:int16) : 
    sign_shrink32_16 (sign_extend16_32 hw) = hw.
  Proof. unfold sign_extend16_32, sign_shrink32_16. intros.
    apply sign_extend_inv2; omega.
  Qed.
  Hint Rewrite sign_shrink32_16_inv: inv_db.
  Hint Rewrite sign_extend16_32_inv using assumption: inv_db.

  Lemma repr_in_signed_byte_extend16_32 hw: 
    repr_in_signed_halfword (sign_extend16_32 hw).
  Proof. unfold repr_in_signed_halfword, sign_extend16_32; intros.
    apply repr_in_signed_extend; omega.
  Qed.

  Definition zero_shrink32_8 := @zero_extend 31 7.

  Definition repr_in_unsigned n1 n2 (w:Word.int n1) :=
    (Word.unsigned w <= Word.max_unsigned n2)%Z.

  Definition repr_in_unsigned_dec n1 n2 (w:Word.int n1) :
    {repr_in_unsigned n2 w} + {~(repr_in_unsigned n2 w)} :=
    Z_le_dec (Word.unsigned w) (Word.max_unsigned n2).

  Definition repr_in_unsigned_byte (w:int32) := repr_in_unsigned 7 w.
  Definition repr_in_unsigned_halfword (w:int32) := repr_in_unsigned 15 w.

  Definition repr_in_unsigned_byte_dec (w:int32) :
    {repr_in_unsigned_byte w} + {~(repr_in_unsigned_byte w)} :=
    repr_in_unsigned_dec 7 w.

  Lemma repr_in_unsigned_extend n1 n2 n3 w:
    n1 <= n3 -> n1 <= n2 ->
    repr_in_unsigned n2 (@zero_extend n1 n3 w).
  Proof. unfold repr_in_unsigned, zero_extend; intros.
    generalize (Word.unsigned_range w); intros.
    assert (0 <= Word.unsigned w <= Word.max_unsigned n3)%Z.
      use_lemma (@max_unsigned_mono n1 n3) by eassumption.
      unfold Word.max_unsigned in *.
      omega.
    rewrite Word.unsigned_repr by eassumption.
    use_lemma (@max_unsigned_mono n1 n2) by eassumption.
    unfold Word.max_unsigned in *.
    omega.
  Qed.

  Lemma repr_in_unsigned_byte_extend8_32 b: 
    repr_in_unsigned_byte (zero_extend8_32 b).
  Proof. unfold repr_in_unsigned_byte, zero_extend8_32; intros.
    apply repr_in_unsigned_extend; omega.
  Qed.

  Lemma zero_extend_inv1 n1 n2 (w:Word.int n2):
    n1 <= n2 -> repr_in_unsigned n1 w ->
    @zero_extend n1 n2 (@zero_extend n2 n1 w) = w.
  Proof. unfold zero_extend, repr_in_unsigned; intros.
    generalize (Word.unsigned_range w); intro.
    rewrite Word.unsigned_repr by omega.
    rewrite Word.repr_unsigned; trivial.
  Qed.

  Lemma zero_extend_inv2 n1 n2 (w:Word.int n2):
    n2 <= n1 -> @zero_extend n1 n2 (@zero_extend n2 n1 w) = w.
  Proof. unfold zero_extend. intros. 
    assert (0 <= Word.unsigned w <= Word.max_unsigned n1)%Z.
      generalize (Word.unsigned_range_2 n2 w); intros.
      use_lemma max_unsigned_mono by eassumption.
      omega.
    rewrite Word.unsigned_repr by assumption.
    rewrite Word.repr_unsigned; trivial.
  Qed.

  Lemma zero_extend8_32_inv (w:int32) : 
    repr_in_unsigned_byte w -> zero_extend8_32 (zero_shrink32_8 w) = w.
  Proof. unfold zero_extend8_32, zero_shrink32_8, repr_in_unsigned_byte. intros.
    apply zero_extend_inv1; [omega | trivial].
  Qed.

  Lemma zero_shrink32_8_inv (b:int8) : 
    zero_shrink32_8 (zero_extend8_32 b) = b.
  Proof. intros. apply zero_extend_inv2. omega. Qed.

  Hint Rewrite zero_shrink32_8_inv: inv_db.
  Hint Rewrite zero_extend8_32_inv using assumption: inv_db.

  Ltac bg_pf_sim :=
    repeat match goal with
      | [ |- context[repr_in_signed_byte_dec ?i]] => 
        destruct (repr_in_signed_byte_dec i)
      | [ H: context[repr_in_signed_byte_dec ?i] |- _] =>
        destruct (repr_in_signed_byte_dec i)
      | [ H: ~ (repr_in_signed_byte (sign_extend8_32 ?i)) |- _ ] =>
        contradict H; apply repr_in_signed_byte_extend8_32

      | [ |- context[repr_in_unsigned_byte_dec ?i]] => 
        destruct (repr_in_unsigned_byte_dec i) 
      | [ H: context[repr_in_unsigned_byte_dec ?i] |- _] =>
        destruct (repr_in_unsigned_byte_dec i)
      | [H: ~ (repr_in_unsigned_byte (zero_extend8_32 ?i)) |- _ ] =>
        contradict H; apply repr_in_unsigned_byte_extend8_32
      | [H: context[register_eq_dec ?r1 ?r2] |- _] => 
        destruct (register_eq_dec r1 r2); subst
      | [ |- context[register_eq_dec ?r1 ?r2]] => 
        destruct (register_eq_dec r1 r2); subst
      | [H: context[if Word.eq ?disp Word.zero then _ else _] |- _] =>
        let disp_eq := fresh "disp_eq" in
        remember_rev (Word.eq disp Word.zero) as disp_eq;
        destruct disp_eq
      | [H: ?V <> ?V |- _] => contradict H; trivial
    end.

  (** * Additional bigrammar constructors (assuming chars are bits) *)

  Program Definition bit (b:bool) : wf_bigrammar Char_t := Char b.
  Program Definition anybit : wf_bigrammar Char_t := Any.

  Lemma bit_nonempty:
    forall b, non_empty (` (bit b)).
  Proof. unfold non_empty. unfold bit. simpl. intros.
    intro Hc. in_bigrammar_inv. crush.
  Qed.
  Hint Resolve bit_nonempty: nonempty_db.

  Fixpoint bits (s:string) : wf_bigrammar (bits_n (String.length s)) := 
    match s with 
      | EmptyString => empty
      | String c s' => 
        (seq (bit (if ascii_dec c "0"%char then false else true)) (bits s'))
    end.

  (** Turn a string of 0s and 1s into a right-associated tuple of trues and
      falses *)
  Fixpoint tuples_of_string (s:string): interp (bits_n (String.length s)) := 
    match s with
      | EmptyString => tt
      | String a s' =>
        (if ascii_dec a "0"%char then false else true, tuples_of_string s')
    end.

  Lemma in_bits_intro: forall str,
    in_bigrammar (` (bits str)) (string_to_bool_list str) (tuples_of_string str).
  Proof. induction str; localsimpl. Qed.

  Lemma in_bits_elim: 
    forall str s v, in_bigrammar (` (bits str)) s v ->
                    s = string_to_bool_list str /\ v = tuples_of_string str.
  Proof. induction str; localsimpl; intros; destruct (ascii_dec a "0"); crush_hyp.
  Qed.

  Lemma bits_rng: forall str,
    in_bigrammar_rng (` (bits str)) (tuples_of_string str).
  Proof. generalize in_bits_intro; localsimpl. Qed.
  Hint Resolve bits_rng: ibr_rng_db.
 
  Lemma bits_nonempty:
    forall s:string, s <> EmptyString -> non_empty (` (bits s)).
  Proof. destruct s.
    - intro H; contradict H; trivial.
    - unfold bits; fold bits; intros.
      apply seq_nonempty1.
      nonempty_tac.
  Qed.
  Hint Resolve bits_nonempty: nonempty_db.

  Program Definition bitsmatch (s:string): wf_bigrammar Unit_t := 
    (bits s) @ (fun _ => tt:[|Unit_t|])
       & (fun _ => Some (tuples_of_string s)) & _.
  Notation "! s" := (bitsmatch s) (at level 60).

  Lemma in_bitsmatch_intro str s v: 
    in_bigrammar (` (bits str)) s v -> in_bigrammar (` (! str)) s ().
  Proof. crush. Qed.

  Lemma in_bitsmatch_elim str s:
    in_bigrammar (` (! str)) s () ->
    exists v, in_bigrammar (` (bits str)) s v.
  Proof. unfold bitsmatch. simpl.
    intros; in_bigrammar_inv. crush.
  Qed.

  Lemma bitsmatch_rng str: in_bigrammar_rng (` (! str)) (). 
  Proof. unfold in_bigrammar_rng. intros. eexists.
    eapply in_bitsmatch_intro. eapply in_bits_intro.
  Qed.
  Hint Resolve bitsmatch_rng: ibr_rng_db.

  Lemma bitsmatch_nonempty:
    forall s:string, s <> EmptyString -> non_empty (` (bitsmatch s)).
  Proof. unfold bitsmatch; intros. nonempty_tac. Qed.

  Program Definition bitsleft t (s:string) (p:wf_bigrammar t) : wf_bigrammar t :=
    (bitsmatch s $ p) @ (@snd _ _)
                      & (fun v => Some (tt, v)) & _.
  Infix "$$" := bitsleft (right associativity, at level 70).
  Extraction Implicit bitsleft [t].

  Lemma in_bitsleft_intro: forall t (g: wf_bigrammar t) str s1 s2 v1 v2,
    in_bigrammar (` (bits str)) s1 v1 -> in_bigrammar (` g) s2 v2
      -> in_bigrammar (` (str $$ g)) (s1 ++ s2)%list v2.
  Proof. crush. Qed.

  Lemma in_bitsleft_elim: forall t str (g: wf_bigrammar t) s (v:interp t),
    in_bigrammar (` (str $$ g)) s v -> 
    exists s1 s2, s = (s1 ++ s2)% list /\ in_bigrammar (` g) s2 v.
  Proof. intros.
    simpl in H. in_bigrammar_inv. crush. destruct x.
    in_bigrammar_inv. crush.
  Qed.

  Lemma in_bigrammar_rng_bitsleft t str (g:wf_bigrammar t) v: 
    in_bigrammar_rng (` (str $$ g)) v <-> in_bigrammar_rng (` g) v.
  Proof. unfold in_bigrammar_rng; split; intros.
    - (* -> *)
      destruct H as [s H]. apply in_bitsleft_elim in H.
      destruct H as [s1 [s2 [H2 H4]]].
      crush.
    - (* <- *)
      destruct H as [s H]. 
      generalize (in_bits_intro str); intro.
      eexists.
      eapply in_bitsleft_intro; eassumption.
  Qed.

  (** the instruction decoder specific version of ibr_sim *)
  Ltac ins_ibr_sim :=
    repeat match goal with 
      | [H: in_bigrammar_rng (` (_ $$ _)) _ |- _] =>
        apply in_bigrammar_rng_bitsleft in H
      | [H: in_bigrammar_rng (` (_ |\/| _)) _ |- _] =>
        apply in_bigrammar_rng_union in H
      | [ |- in_bigrammar_rng (` (_ $$ _)) _ ] =>
        rewrite -> in_bigrammar_rng_bitsleft
      | [ |- in_bigrammar_rng (` (_ |\/| _)) _ ] =>
        apply in_bigrammar_rng_union
      | [ |- in_bigrammar_rng (` (! _)) () ] =>
        apply bitsmatch_rng
      | _ => ibr_sim
    end.

  Fixpoint field'(n:nat) : wf_bigrammar (bits_n n) := 
    match n with 
      | 0%nat => empty
      | S n => seq anybit (field' n)
    end.

  Fixpoint flatten_bits_n (n:nat) : (interp (bits_n n)) -> list bool := 
    match n with
      | O => fun _ => nil
      | S n' => fun v => (fst v) :: flatten_bits_n n' (snd v)
    end.

  Lemma in_field'_intro: forall n (v: interp (bits_n n)),
    in_bigrammar (` (field' n)) (flatten_bits_n n v) v.
  Proof. induction n. crush.
    intros. simpl. destruct v.
    eapply InCat; crush.
  Qed.

  Lemma field'_rng n (v : [|bits_n n|]): 
    in_bigrammar_rng (` (field' n)) v.
  Proof. unfold in_bigrammar_rng. intros. eexists.
    eapply in_field'_intro.
  Qed.
  Hint Resolve field'_rng: ibr_rng_db.

  Program Definition field (n:nat) : wf_bigrammar int_t := 
    (field' n) @ (int_of_bitsn n) & bitsn_of_int n & _.
  Next Obligation.
    - eapply int_of_bitsn_inv. trivial.
  Defined.

  Definition int_to_bool_list n v := 
    (flatten_bits_n n (bitsn_of_sig n (Word.bits_of_Z n v))).

  Lemma in_field_intro:
    forall n i, (0 <= i < two_power_nat n)%Z ->
                in_bigrammar (` (field n)) (int_to_bool_list n i) i.
  Proof. intros.
    eapply InMap. eapply in_field'_intro.
    unfold int_of_bitsn in *. simpl.
    autorewrite with inv_db.
    destruct n.
    - unfold two_power_nat, shift_nat in *. simpl in *. omega.
    - rewrite (Word.Z_of_bits_of_Z_lt_modulus); trivial.
  Qed.

  Lemma field_rng : 
    forall n i, (0 <= i < two_power_nat n)%Z <->
                in_bigrammar_rng (` (field n)) i.
  Proof. 
    split; intros.
    - unfold in_bigrammar_rng.
      eexists. eapply in_field_intro. trivial.
    - unfold field, in_bigrammar_rng in *.
      intros. crush; in_bigrammar_inv; crush' int_of_bitsn_range fail.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` (field _)) _) =>
    apply field_rng; omega : ibr_rng_db.

  Definition reg : wf_bigrammar register_t.
    refine (field 3 @ (Z_to_register : _ -> [|register_t|])
              & (fun r => Some (register_to_Z r)) & _); 
    invertible_tac.
    - assert (0 <= v < 8)%Z.
        apply field_rng in H. lineararith.
      use_lemma register_to_Z_inv by eauto.
      crush.
    - generalize Z_to_register_inv. crush.
  Defined.

  Lemma reg_rng: forall r, in_bigrammar_rng (` reg) r.
  Proof. 
    destruct r; apply in_bigrammar_rng_map;
    [exists 0%Z | exists 1%Z | exists 2%Z | exists 3%Z |
     exists 4%Z | exists 5%Z | exists 6%Z | exists 7%Z ]; 
    (split; [(apply field_rng; lineararith) | trivial]).
  Qed.
  Hint Resolve reg_rng: ibr_rng_db.

  Definition int_n : forall n, wf_bigrammar (bitvector_t n).
    intro;
    refine ((field (S n)) @ (@Word.repr n : _ ->  [|bitvector_t n|])
              & fun b => Some (@Word.unsigned n b) & _);
    invertible_tac.
    + assert (0 <= v <= Word.max_unsigned n)%Z.
        apply field_rng in H.
        unfold Word.max_unsigned, Word.modulus.
        rewrite two_power_nat_S in *.
        omega.
      use_lemma Word.unsigned_repr by eauto.
      crush.
    + crush.
      apply Word.repr_unsigned.
  Defined.

  Lemma in_int_n_intro:
    forall n (v: Word.int n), 
      in_bigrammar (` (int_n n)) (int_to_bool_list (S n) (Word.unsigned v)) v.
  Proof. intros. 
    eapply InMap.
    eapply in_field_intro.
    eapply Word.unsigned_range. simpl.
    rewrite Word.repr_unsigned. trivial.
  Qed.

  Lemma int_n_rng:
    forall n (v: Word.int n), in_bigrammar_rng (` (int_n n)) v.
  Proof. unfold in_bigrammar_rng. intros; eexists; eapply in_int_n_intro. Qed.
  Hint Extern 1 (in_bigrammar_rng (` (int_n _)) _) => apply int_n_rng : ibr_rng_db.

  (* concatenate two bit-vector ints into a single one *)
  Definition intn_cat n m (b1:Word.int n) (b2:Word.int m) : Word.int (n+m+1) :=
    let sig1 := sig_of_intn b1 in
    let sig2 := sig_of_intn b2 in
    intn_of_sig (n+m+1) (Word.sig_cat (S m) sig1 sig2).

  (* the inverses of intn_cat *)
  Definition intn_split1 n m (b:Word.int (n+m+1)): Word.int n  :=
    intn_of_sig n (Word.sig_split1 (S m) (sig_of_intn b)).
  Definition intn_split2 n m (b:Word.int (n+m+1)): Word.int m  :=
    intn_of_sig m (Word.sig_split2 (S m) (sig_of_intn b)).

  Lemma intn_of_sig_eq_intn n (b:Word.int n) sig:
    Word.sig_eq_below (S n) sig (sig_of_intn b) ->
    intn_of_sig n sig = b.
  Proof. intros. rewrite <- (intn_of_sig_inv b).
    rewrite H. trivial.
  Qed.
         
  Lemma intn_split1_inv n m (b1:Word.int n) (b2:Word.int m):
    intn_split1 n m (intn_cat b1 b2) = b1.
  Proof. unfold intn_split1, intn_cat; intros.
    apply intn_of_sig_eq_intn.
    assert (H: Word.sig_eq_below (S n + S m)
              (sig_of_intn
                   (intn_of_sig (n + m + 1)
                      (Word.sig_cat (S m) (sig_of_intn b1) (sig_of_intn b2))))
              (Word.sig_cat (S m) (sig_of_intn b1) (sig_of_intn b2))).
      replace (S n + S m) with (S (n+m+1)) by omega.
      apply sig_of_intn_inv. 
    rewrite H.
    apply Word.sig_split1_inv.
  Qed.

  Lemma intn_split2_inv n m (b1:Word.int n) (b2:Word.int m):
    intn_split2 n m (intn_cat b1 b2) = b2.
  Proof. unfold intn_split2, intn_cat; intros.
    apply intn_of_sig_eq_intn.
    assert (H: Word.sig_eq_below (S n + S m)
              (sig_of_intn
                   (intn_of_sig (n + m + 1)
                      (Word.sig_cat (S m) (sig_of_intn b1) (sig_of_intn b2))))
              (Word.sig_cat (S m) (sig_of_intn b1) (sig_of_intn b2))).
      replace (S n + S m) with (S (n+m+1)) by omega.
      apply sig_of_intn_inv. 
    apply (@Word.sig_eq_below_downward_closed (S m)) in H; [idtac | omega].
    rewrite H.
    apply Word.sig_split2_inv.
  Qed.

  Lemma intn_cat_inv n m (b:Word.int (n+m+1)):
    intn_cat (intn_split1 n m b) (intn_split2 n m b) = b.
  Proof. unfold intn_split1, intn_split2, intn_cat; intros.
    apply intn_of_sig_eq_intn.
    replace (S (n+m+1)) with (S n + S m) by omega.
    repeat (rewrite (sig_of_intn_inv)).
    rewrite Word.sig_cat_inv. reflexivity.
  Qed.

  (** parse two bitvectors and put them together by little endian;
      that is, put the second one before the first one. *)
  Definition intn_cat_little n m
             (p1: wf_bigrammar (bitvector_t n))
             (p2: wf_bigrammar (bitvector_t m)) :
    wf_bigrammar (bitvector_t (m+n+1)).
    intros.
    refine ((p1 $ p2)
              @ (fun bs => intn_cat (snd bs) (fst bs)) :
                  _ -> [|bitvector_t (m+n+1)|]
              & (fun b =>
                   Some (intn_split2 m n b, intn_split1 m n b))
              & _). invertible_tac.
    - exists v. destruct v as [b1 b2].
      rewrite intn_split1_inv.
      rewrite intn_split2_inv. auto.
    - destruct v as [b1 b2]. inversion H0.
      apply intn_cat_inv.
  Defined.

  Definition byte : wf_bigrammar byte_t := int_n 7.

  Definition halfword : wf_bigrammar half_t := 
    intn_cat_little byte byte.

  Definition word : wf_bigrammar word_t := 
    intn_cat_little (intn_cat_little halfword byte) byte.

  Lemma intn_cat_little_rng n m 
    (p1:wf_bigrammar (bitvector_t n)) 
    (p2:wf_bigrammar (bitvector_t m)) 
    (v: [|bitvector_t (m+n+1)|]):
    in_bigrammar_rng (` p1) (intn_split2 m n v) ->
    in_bigrammar_rng (` p2) (intn_split1 m n v) ->
    in_bigrammar_rng (` (@intn_cat_little n m p1 p2)) v.
  Proof. unfold in_bigrammar_rng. intros.
    destruct H as [s1 H]. destruct H0 as [s2 H0].
    exists (s1 ++ s2)%list.
    unfold intn_cat_little. simpl.
    econstructor.
      econstructor; try eassumption; trivial.
      simpl. rewrite intn_cat_inv; trivial.
  Qed.

  Hint Extern 1 (in_bigrammar_rng (` (intn_cat_little ?p1 ?p2)) _) =>
    apply (intn_cat_little_rng p1 p2): ibr_rng_db.

  Hint Extern 1 (in_bigrammar_rng (` byte) _) => apply int_n_rng : ibr_rng_db.

  Lemma halfword_rng:
    forall v, in_bigrammar_rng (` halfword) v.
  Proof. unfold halfword. intros. ins_ibr_sim. Qed.
  Hint Extern 1 (in_bigrammar_rng (` halfword) _) => apply halfword_rng: ibr_rng_db.

  Lemma word_rng:
    forall v, in_bigrammar_rng (` word) v.
  Proof. unfold word. intros. ins_ibr_sim. Qed.
  Hint Extern 1 (in_bigrammar_rng (` word) _) => apply word_rng: ibr_rng_db.

  Definition tttn : wf_bigrammar condition_t. 
    refine ((field 4) @ (Z_to_condition_type : _ -> [|condition_t|])
              & (fun ct => Some (condition_type_to_Z ct)) & _);
    invertible_tac.
    - assert (0 <= v < 16)%Z.
        apply field_rng in H. lineararith.
      use_lemma condition_type_to_Z_inv by eauto.
      crush.
    - generalize Z_to_condition_type_inv. crush.
  Defined.

  (* speed tests *)
  Section SpeedTest.

  Definition test_env: AST_Env control_register_t :=
    {{0, ! "000", (fun v => CR0 %% control_register_t)}} :::
    {{1, ! "010", (fun v => CR2 %% control_register_t)}} :::
    {{2, ! "011", (fun v => CR3 %% control_register_t)}} :::
    {{3, ! "100", (fun v => CR4 %% control_register_t)}} :::
    (* {{4, ! "000", (fun v => CR0 %% control_register_t)}} ::: *)
    (* {{5, ! "010", (fun v => CR2 %% control_register_t)}} ::: *)
    (* {{6, ! "011", (fun v => CR3 %% control_register_t)}} ::: *)
    (* {{7, ! "100", (fun v => CR4 %% control_register_t)}} ::: *)
    (* {{8, ! "000", (fun v => CR0 %% control_register_t)}} ::: *)
    (* {{9, ! "010", (fun v => CR2 %% control_register_t)}} ::: *)
    (* {{10, ! "011", (fun v => CR3 %% control_register_t)}} ::: *)
    (* {{11, ! "100", (fun v => CR4 %% control_register_t)}} ::: *)
    (* {{12, ! "000", (fun v => CR0 %% control_register_t)}} ::: *)
    (* {{13, ! "010", (fun v => CR2 %% control_register_t)}} ::: *)
    (* {{14, ! "011", (fun v => CR3 %% control_register_t)}} ::: *)
    (* {{15, ! "100", (fun v => CR4 %% control_register_t)}} ::: *)
    (* {{16, ! "000", (fun v => CR0 %% control_register_t)}} ::: *)
    (* {{17, ! "010", (fun v => CR2 %% control_register_t)}} ::: *)
    (* {{18, ! "011", (fun v => CR3 %% control_register_t)}} ::: *)
    (* {{19, ! "100", (fun v => CR4 %% control_register_t)}} ::: *)
    (* {{20, ! "000", (fun v => CR0 %% control_register_t)}} ::: *)
    (* {{21, ! "010", (fun v => CR2 %% control_register_t)}} ::: *)
    (* {{22, ! "011", (fun v => CR3 %% control_register_t)}} ::: *)
    (* {{23, ! "100", (fun v => CR4 %% control_register_t)}} ::: *)
    (* {{24, ! "000", (fun v => CR0 %% control_register_t)}} ::: *)
    (* {{25, ! "010", (fun v => CR2 %% control_register_t)}} ::: *)
    (* {{26, ! "011", (fun v => CR3 %% control_register_t)}} ::: *)
    (* {{27, ! "100", (fun v => CR4 %% control_register_t)}} ::: *)
    (* {{28, ! "000", (fun v => CR0 %% control_register_t)}} ::: *)
    (* {{29, ! "010", (fun v => CR2 %% control_register_t)}} ::: *)
    (* {{30, ! "011", (fun v => CR3 %% control_register_t)}} ::: *)
    (* {{31, ! "100", (fun v => CR4 %% control_register_t)}} ::: *)
    ast_env_nil.
  Hint Unfold test_env: env_unfold_db.

  Definition test_b : wf_bigrammar control_register_t.
    Time gen_ast_defs test_env.
    Time refine((comb_bigrammar gt) @ (comb_map gt)
             & (fun u =>
                  match u with
                    | CR0 => inv_case_some case0 ()
                    | CR2 => inv_case_some case1 ()
                    | CR3 => inv_case_some case2 ()
                    | CR4 => inv_case_some case3 ()
                  end)
             & _); ast_invertible_tac.
  Time (destruct w; parsable_tac).
  Time Defined.

  (* Definition test_b : wf_bigrammar _register_t. *)
  (*   Time gen_ast_defs test_env. *)
  (*   Time refine(gr @ (mp: _ -> [|control_register_t|]) *)
  (*            & (fun u => *)
  (*                 match u with *)
  (*                   | CR0 => case0 () *)
  (*                   | CR2 => case1 () *)
  (*                   | CR3 => case2 () *)
  (*                   | CR4 => case3 () *)
  (*                 end) *)
  (*            & _); clear_ast_defs; invertible_tac. *)
  (*    - Time destruct w; parsable_tac. *)
  (* Time Defined. *)

  End SpeedTest.

  Definition control_reg_env: AST_Env control_register_t := 
    {{0, ! "000", (fun v => CR0 %% control_register_t)}} :::
    {{1, ! "010", (fun v => CR2 %% control_register_t)}} :::
    {{2, ! "011", (fun v => CR3 %% control_register_t)}} :::
    {{3, ! "100", (fun v => CR4 %% control_register_t)}} :::
    ast_env_nil.
  Hint Unfold control_reg_env: env_unfold_db.

  Definition control_reg_b : wf_bigrammar control_register_t.
    gen_ast_defs control_reg_env.
    refine((comb_bigrammar gt) @ (comb_map gt)
             & (fun u =>
                  match u with
                    | CR0 => inv_case_some case0 ()
                    | CR2 => inv_case_some case1 ()
                    | CR3 => inv_case_some case2 ()
                    | CR4 => inv_case_some case3 ()
                  end)
             & _); ast_invertible_tac.
     - destruct w; parsable_tac.
  Defined.

  Definition debug_reg_env : AST_Env debug_register_t := 
    {{0, ! "000", (fun _ => DR0 %% debug_register_t)}} :::
    {{1, ! "001", (fun _ => DR1 %% debug_register_t)}} :::
    {{2, ! "010", (fun _ => DR2 %% debug_register_t)}} :::
    {{3, ! "011", (fun _ => DR3 %% debug_register_t)}} :::
    {{4, ! "110", (fun _ => DR6 %% debug_register_t)}} :::
    {{5, ! "111", (fun _ => DR7 %% debug_register_t)}} :::
    ast_env_nil.
  Hint Unfold debug_reg_env: env_unfold_db.
     
  (* Note:  apparently, the bit patterns corresponding to DR4 and DR5 either
   * (a) get mapped to DR6 and DR7 respectively or else (b) cause a fault,
   * depending upon the value of some control register.  My guess is that it's
   * okay for us to just consider this a fault. Something similar seems to
   * happen with the CR registers above -- e.g., we don't have a CR1. *)
  Definition debug_reg_b : wf_bigrammar debug_register_t.
    gen_ast_defs debug_reg_env.
    refine((comb_bigrammar gt) @ (comb_map gt)
              & (fun u => 
                   match u with
                     | DR0 => inv_case_some case0 ()
                     | DR1 => inv_case_some case1 ()
                     | DR2 => inv_case_some case2 ()
                     | DR3 => inv_case_some case3 ()
                     | DR6 => inv_case_some case4 ()
                     | DR7 => inv_case_some case5 ()
                end)
              & _); ast_invertible_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition segment_reg_env : AST_Env segment_register_t := 
    {{0, ! "000", (fun _ => ES %% segment_register_t)}} :::
    {{1, ! "001", (fun _ => CS %% segment_register_t)}} :::
    {{2, ! "010", (fun _ => SS %% segment_register_t)}} :::
    {{3, ! "011", (fun _ => DS %% segment_register_t)}} :::
    {{4, ! "100", (fun _ => FS %% segment_register_t)}} :::
    {{5, ! "101", (fun _ => GS %% segment_register_t)}} :::
    ast_env_nil.
  Hint Unfold segment_reg_env: env_unfold_db.

  Definition segment_reg_b : wf_bigrammar segment_register_t.
    gen_ast_defs segment_reg_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u => 
                    match u with
                      | ES => inv_case_some case0 ()
                      | CS => inv_case_some case1 ()
                      | SS => inv_case_some case2 ()
                      | DS => inv_case_some case3 ()
                      | FS => inv_case_some case4 ()
                      | GS => inv_case_some case5 ()
                    end)
               & _); ast_invertible_tac.
     - destruct w; parsable_tac.
  Defined.
    
  (** * A bigrammar for modrm and other parsers such as immediate parsers *)

  (* Definition bitvector (n:nat) (bs:[|bits_n n|]) : Word.int n. *)

  Program Definition field_intn (n:nat) : wf_bigrammar (bitvector_t n) :=
    (field' (S n)) @ (@intn_of_bitsn n: _ -> [|bitvector_t n|])
                   & (fun i => Some (bitsn_of_intn i)) & _.

  Definition fpu_reg  : wf_bigrammar fpu_register_t := field_intn 2.
  Definition mmx_reg : wf_bigrammar mmx_register_t := field_intn 2.
  Definition sse_reg : wf_bigrammar sse_register_t := field_intn 2.

  Definition scale_b :wf_bigrammar scale_t. 
    refine ((field 2) @ (Z_to_scale : _ -> interp scale_t)
                      & (fun s => Some (scale_to_Z s)) & _);
    invertible_tac.
    - assert (0 <= v < 4)%Z.
        apply field_rng in H. lineararith.
      use_lemma scale_to_Z_inv by eauto.
      crush.
    - generalize Z_to_scale_inv. crush.
  Defined.

  Lemma scale_rng : forall s, in_bigrammar_rng (` scale_b) s.
  Proof. 
    destruct s; apply in_bigrammar_rng_map;
    [exists 0%Z | exists 1%Z | exists 2%Z | exists 3%Z];
    (split; [apply field_rng; lineararith | trivial]).
  Qed.
  Hint Resolve scale_rng: ibr_rng_db.

  Definition reg_no_esp_env: AST_Env register_t := 
    {{0, ! "000", (fun v => EAX %% register_t)}} :::
    {{1, ! "001", (fun v => ECX %% register_t)}} :::
    {{2, ! "010", (fun v => EDX %% register_t)}} :::
    {{3, ! "011", (fun v => EBX %% register_t)}} :::
    (* esp case not allowed *)
    (* {{0, ! "100", (fun v => ESX %% register_t)}} ::: *)
    {{4, ! "101", (fun v => EBP %% register_t)}} :::
    {{5, ! "110", (fun v => ESI %% register_t)}} :::
    {{6, ! "111", (fun v => EDI %% register_t)}} :::
    ast_env_nil.
  Hint Unfold reg_no_esp_env : env_unfold_db.

  (* This is used in a strange edge-case for modrm parsing. See the
     footnotes on p37 of the manual in the repo This is a case where I
     think intersections/complements would be nice operators *)
  (* JGM: we can handle this in the semantic action instead of the grammar, 
     so I replaced si, which used this and another pattern for [bits "100"]
     to the simpler case below -- helps to avoid some explosions in the 
     definitions. *)
  Definition reg_no_esp : wf_bigrammar register_t. 
    gen_ast_defs reg_no_esp_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun r => match r with
                          | EAX => inv_case_some case0 ()
                          | ECX => inv_case_some case1 ()
                          | EDX => inv_case_some case2 ()
                          | EBX => inv_case_some case3 ()
                          | ESP => None
                          | EBP => inv_case_some case4 ()
                          | ESI => inv_case_some case5 ()
                          | EDI => inv_case_some case6 ()
                        end)
               & _); ast_invertible_tac.
     - destruct w; parsable_tac.
  Defined. 

  Lemma reg_no_esp_rng r:
    r <> ESP -> in_bigrammar_rng (` reg_no_esp) r.
  Proof. intros.
    compute - [in_bigrammar_rng bitsmatch].
    destruct r;
    break_hyp;
    match goal with
      | [H: ?V <> ?V |- _] => contradiction H; trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EAX] => 
        replace EAX with (fst fi (inl (inl (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ECX] => 
        replace ECX with (fst fi (inl (inl (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EDX] => 
        replace EDX with (fst fi (inl (inr (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EBX] => 
        replace EBX with (fst fi (inl (inr (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EBP] => 
        replace EBP with (fst fi (inr (inl (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ESI] => 
        replace ESI with (fst fi (inr (inl (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EDI] => 
        replace EDI with (fst fi (inr (inr ())))
          by trivial
      | _ => idtac
    end; ins_ibr_sim; apply bitsmatch_rng.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` reg_no_esp) _) => 
    apply reg_no_esp_rng; congruence: ibr_rng_db.

  Lemma reg_no_esp_neq r: in_bigrammar_rng (` reg_no_esp) r -> r <> ESP.
  Proof. intros.
    unfold in_bigrammar_rng. 
    destruct H as [s H]. simpl in H.
    in_bigrammar_inv. destruct H as [u [_ H]]. simpl in H.
    destruct_all; crush.
  Qed.

  Definition reg_no_ebp : wf_bigrammar register_t.
    refine (((! "000" |+| ! "001" |+| ! "010") |+|
             (! "011" |+|  ! "100")  (* |+| bits "101" <- this is ebp *) |+|
             (! "110" |+| ! "111"))
            @ (fun s => match s with
                          | inl (inl _) => EAX
                          | inl (inr (inl _)) => ECX
                          | inl (inr (inr _)) => EDX
                          | inr (inl (inl _)) => EBX
                          | inr (inl (inr _)) => ESP
                          | inr (inr (inl _)) => ESI
                          | inr (inr (inr _)) => EDI
                        end : interp register_t)
            & (fun r => match r with
                          | EAX => Some (inl (inl ()))
                          | ECX => Some (inl (inr (inl ())))
                          | EDX => Some (inl (inr (inr ())))
                          | EBX => Some (inr (inl (inl ())))
                          | ESP => Some (inr (inl (inr ())))
                          | EBP => None
                          | ESI => Some (inr (inr (inl ())))
                          | EDI => Some (inr (inr (inr ())))
                        end)
            & _); invertible_tac.
     - destruct w; parsable_tac.
  Defined. 

  Lemma reg_no_ebp_rng r:
    r <> EBP -> in_bigrammar_rng (` reg_no_ebp) r.
  Proof. intros.
    compute - [in_bigrammar_rng bitsmatch].
    destruct r;
    break_hyp;
    match goal with
      | [H: ?V <> ?V |- _] => contradiction H; trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EAX] => 
        replace EAX with (fst fi (inl (inl ()))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ECX] => 
        replace ECX with (fst fi (inl (inr (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EDX] => 
        replace EDX with (fst fi (inl (inr (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EBX] => 
        replace EBX with (fst fi (inr (inl (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ESP] => 
        replace ESP with (fst fi (inr (inl (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ESI] => 
        replace ESI with (fst fi (inr (inr (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EDI] => 
        replace EDI with (fst fi (inr (inr (inr ()))))
          by trivial
      | _ => idtac
    end; ins_ibr_sim; apply bitsmatch_rng.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` reg_no_ebp) _) => 
    apply reg_no_ebp_rng; congruence: ibr_rng_db.

  Lemma reg_no_ebp_neq r: in_bigrammar_rng (` reg_no_ebp) r -> r <> EBP.
  Proof. intros.
    unfold in_bigrammar_rng. 
    destruct H as [s H]. simpl in H.
    in_bigrammar_inv. destruct H as [u [_ H]]. simpl in H.
    destruct_all; crush.
  Qed.

  Definition reg_no_esp_ebp : wf_bigrammar register_t.
    refine (((! "000" |+| ! "001" |+| ! "010")  |+|
             (! "011" |+| ! "110" |+| ! "111"))
             (* |+|  ! "100"  <- this is esp *) 
             (* |+| bits "101" <- this is ebp *) 
            @ (fun u => match u with
                          | inl (inl _) => EAX
                          | inl (inr (inl _)) => ECX
                          | inl (inr (inr _)) => EDX
                          | inr (inl _) => EBX
                          | inr (inr (inl _)) => ESI
                          | inr (inr (inr _)) => EDI
                        end : interp register_t)
            & (fun r => match r with
                          | EAX => Some (inl (inl ()))
                          | ECX => Some (inl (inr (inl ())))
                          | EDX => Some (inl (inr (inr ())))
                          | EBX => Some (inr (inl ()))
                          | ESP => None
                          | EBP => None
                          | ESI => Some (inr (inr (inl ())))
                          | EDI => Some (inr (inr (inr ())))
                        end)
            & _); invertible_tac.
     - destruct w; parsable_tac.
  Defined. 

  Lemma reg_no_esp_ebp_rng r: 
    r <> ESP /\ r <> EBP -> in_bigrammar_rng (` reg_no_esp_ebp) r.
  Proof. intros.
    compute - [in_bigrammar_rng bitsmatch].
    destruct r;
      break_hyp;
      match goal with
        | [H: ?V <> ?V |- _] => contradiction H; trivial
        | [ |- in_bigrammar_rng (Map ?fi _) EAX] => 
          replace EAX with (fst fi (inl (inl tt))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) ECX] => 
          replace ECX with (fst fi (inl (inr (inl tt)))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) EDX] => 
          replace EDX with (fst fi (inl (inr (inr tt)))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) EBX] => 
          replace EBX with (fst fi (inr (inl tt))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) ESI] => 
          replace ESI with (fst fi (inr (inr (inl tt)))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) EDI] => 
          replace EDI with (fst fi (inr (inr (inr tt))))
            by trivial
        | _ => idtac
      end; ins_ibr_sim; apply bitsmatch_rng.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` reg_no_esp_ebp) _) => 
    apply reg_no_esp_ebp_rng; split; congruence: ibr_rng_db.

  Lemma reg_no_esp_ebp_neq r: 
    in_bigrammar_rng (` reg_no_esp_ebp) r -> r <> ESP /\ r <> EBP.
  Proof. intros.
    unfold in_bigrammar_rng in H.
    destruct H as [s H]. simpl in H.
    in_bigrammar_inv.
    destruct H as [v [_ H]]. simpl in H.
    destruct_all; crush.
  Qed.

  Definition si_b: wf_bigrammar (option_t (pair_t scale_t register_t)). 
    refine ((scale_b $ reg)
            @ (fun p => match snd p with 
                          | ESP => None
                          | _ => Some p
                        end %% option_t (pair_t scale_t register_t))
            & (fun v => match v with
                          | None => Some (Scale1, ESP)
                          | Some (_, ESP) => None
                          | Some (s,p) => Some (s,p)
                        end)
            & _); invertible_tac.
    - destruct v as [s r]; destruct r; printable_tac.
    - ins_parsable_tac.
  Defined.

  Lemma si_b_rng_some sc idx: 
    in_bigrammar_rng (` si_b) (Some (sc, idx)) -> idx <> ESP.
  Proof. unfold in_bigrammar_rng. intros sc idx H.
    destruct H as [s H].
    simpl in H.
    in_bigrammar_inv.
    destruct H as [[sc' idx'] [_ H]]. simpl in H.
    destruct idx'; crush.
  Qed.

  Lemma si_b_rng_none : in_bigrammar_rng (` si_b) None.
  Proof. unfold proj1_sig at 1; compute - [in_bigrammar_rng proj1_sig scale_b reg seq].
    match goal with
      | [ |- in_bigrammar_rng (Map ?fi ?g) None] => 
        assert (H:None = (fst fi (Scale1, ESP))) by trivial;
        rewrite H; clear H; apply in_bigrammar_rng_map2
    end; ins_ibr_sim.
  Qed.
  Hint Resolve si_b_rng_none: ibr_rng_db.

  Definition sib_b := si_b $ reg.

  Lemma sib_b_rng_none r: in_bigrammar_rng (` sib_b) (None, r).
  Proof. intros; unfold sib_b. ins_ibr_sim. Qed.
  Hint Resolve sib_b_rng_none: ibr_rng_db.

  Definition Address_op_inv op := 
    match op with
      | Address_op addr => Some addr
      | _ => None
    end.

  Definition SSE_Addr_op_inv op := 
    match op with
      | SSE_Addr_op addr => Some addr
      | _ => None
    end.

  Definition MMX_Addr_op_inv op := 
    match op with
      | MMX_Addr_op addr => Some addr
      | _ => None
    end.

  Definition FPM16_op_inv op := 
    match op with
      | FPM16_op addr => Some addr
      | _ => None
    end.

  Definition FPM32_op_inv op := 
    match op with
      | FPM32_op addr => Some addr
      | _ => None
    end.

  Definition FPM64_op_inv op := 
    match op with
      | FPM64_op addr => Some addr
      | _ => None
    end.

  Definition FPM80_op_inv op := 
    match op with
      | FPM80_op addr => Some addr
      | _ => None
    end.

  Definition Reg_op_b : wf_bigrammar operand_t.
    refine(reg @ (fun r => Reg_op r : interp operand_t)
               & (fun op => match op with
                              | Reg_op r => Some r
                              | _ => None
                            end)
               & _); invertible_tac; ins_parsable_tac.
  Defined.

  (* Definition modrm_gen_noreg_env (reg_t:type) (reg_b:wf_bigrammar reg_t) *)
  (*           : AST_Env (pair_t reg_t address_t) := *)
  (*   (* mode 00 *) *)
  (*   {{0, "00" $$ reg_b $ reg_no_esp_ebp, *)
  (*    fun v => *)
  (*      let (r1,base):=v in (r1, mkAddress (Word.repr 0) (Some base) None) *)
  (*      %% pair_t reg_t address_t}} ::: *)
  (*   {{1, "00" $$ reg_b $ "100" $$ si_b $ reg_no_ebp, *)
  (*    fun v => match v with *)
  (*               | (r,(si,base)) => *)
  (*                 (r, mkAddress (Word.repr 0) (Some base) si) *)
  (*             end %% pair_t reg_t address_t}} ::: *)
  (*   {{2, "00" $$ reg_b $ "100" $$ si_b $ "101" $$ word, *)
  (*    fun v => match v with *)
  (*               | (r,(si,disp)) => (r, mkAddress disp None si) *)
  (*             end %% pair_t reg_t address_t}} ::: *)
  (*   {{3, "00" $$ reg_b $ "101" $$ word, *)
  (*    fun v => let (r,disp):=v in (r, mkAddress disp None None) *)
  (*      %% pair_t reg_t address_t}} ::: *)
  (*   (* mode 01 *) *)
  (*   {{4, "01" $$ reg_b $ reg_no_esp $ byte, *)
  (*    fun v => match v with *)
  (*               | (r,(bs,disp)) => *)
  (*                 (r, mkAddress (sign_extend8_32 disp) (Some bs) None) *)
  (*             end %% pair_t reg_t address_t}} ::: *)
  (*   {{5, "01" $$ reg_b $ "100" $$ sib_b $ byte, *)
  (*    fun v => match v with *)
  (*               | (r, ((si,bs),disp)) => *)
  (*                 (r, mkAddress (sign_extend8_32 disp) (Some bs) si) *)
  (*             end %% pair_t reg_t address_t}} ::: *)
  (*   (* mode 10 *) *)
  (*   {{6, "10" $$ reg_b $ reg_no_esp $ word, *)
  (*    fun v => match v with *)
  (*               | (r,(bs,disp)) => (r, mkAddress disp (Some bs) None) *)
  (*             end %% pair_t reg_t address_t}} ::: *)
  (*   {{7, "10" $$ reg_b $ "100" $$ sib_b $ word, *)
  (*    fun v => match v with *)
  (*               | (r,((si,bs),disp)) => (r, mkAddress disp (Some bs) si) *)
  (*             end %% pair_t reg_t address_t}} ::: *)
  (*   ast_env_nil. *)

  (* Definition modrm_gen_noreg (reg_t: type) *)
  (*   (reg_b: wf_bigrammar reg_t) : wf_bigrammar (pair_t reg_t address_t). *)
  (*   intros; gen_ast_defs (modrm_gen_noreg_env reg_b). *)
  (*   refine (gr @ (mp:_ -> [|pair_t reg_t address_t|]) *)
  (*              & (fun u:[|pair_t reg_t address_t|] => *)
  (*                   let (r,addr) := u in *)
  (*                   match addr with *)
  (*                     | {| addrDisp:=disp; addrBase:=None; addrIndex:=None |} => *)
  (*                       (* alternate encoding: mod00 case2, making reg in si_b be ESP *) *)
  (*                       inv_case_some case3 (r,disp) *)
  (*                     | {| addrDisp:=disp; addrBase:=None; addrIndex:=Some si |} => *)
  (*                       (* special case: disp32[index*scale]; *)
  (*                          the mod bits in mod/rm must be 00 *) *)
  (*                       inv_case_some case2 (r,(Some si,disp)) *)
  (*                     | {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=None |} => *)
  (*                       if (register_eq_dec bs ESP) then *)
  (*                           (* alternate encoding: when disp is not zero or cannot *)
  (*                              be represented as a byte, then case5/7 can always *)
  (*                              be used *) *)
  (*                           if (Word.eq disp Word.zero) then *)
  (*                             inv_case_some case1 (r, (None, ESP)) *)
  (*                           else *)
  (*                             if (repr_in_signed_byte_dec disp) then *)
  (*                               inv_case_some case5 (r, ((None, ESP), sign_shrink32_8 disp)) *)
  (*                             else inv_case_some case7 (r, ((None, ESP), disp)) *)
  (*                       else *)
  (*                         if (register_eq_dec bs EBP) then *)
  (*                           (* alternate encoding: case6 can always be used *) *)
  (*                           if (repr_in_signed_byte_dec disp) *)
  (*                           then inv_case_some case4 (r, (bs, sign_shrink32_8 disp)) *)
  (*                           else inv_case_some case6 (r, (bs, disp)) *)
  (*                         else *)
  (*                           (* alternate encoding: case4/6 can always be used depending *)
  (*                              on disp *) *)
  (*                           if (Word.eq disp Word.zero) then *)
  (*                             inv_case_some case0 (r, bs) *)
  (*                           else *)
  (*                             if (repr_in_signed_byte_dec disp) *)
  (*                             then inv_case_some case4 (r, (bs, sign_shrink32_8 disp)) *)
  (*                             else inv_case_some case6 (r, (bs, disp)) *)
  (*                     | {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=Some sci |} => *)
  (*                       if (register_eq_dec (snd sci) ESP) then None *)
  (*                       else if (register_eq_dec bs EBP) then *)
  (*                              (* alternate encoding: case7 can always be used *) *)
  (*                              if (repr_in_signed_byte_dec disp) then *)
  (*                                inv_case_some case5 (r, ((Some sci, bs), sign_shrink32_8 disp)) *)
  (*                              else inv_case_some case7 (r, ((Some sci, bs), disp)) *)
  (*                            else *)
  (*                              (* alternate encoding: case5/7 can be used *) *)
  (*                              if (Word.eq disp Word.zero) then *)
  (*                                inv_case_some case1 (r, (Some sci, bs)) *)
  (*                              else *)
  (*                                if (repr_in_signed_byte_dec disp) then *)
  (*                                  inv_case_some case5 (r, ((Some sci, bs), sign_shrink32_8 disp)) *)
  (*                                else inv_case_some case7 (r, ((Some sci, bs), disp)) *)
  (*                   end) *)
  (*              & _); clear_ast_defs. invertible_tac. *)
  (*   - destruct_all. *)
  (*     + (* case 0 *) *)
  (*       destruct v as [r bs]. *)
  (*       rewrite Word.int_eq_refl. *)
  (*       assert (bs<>ESP /\ bs<>EBP). *)
  (*         ins_ibr_sim. apply reg_no_esp_ebp_neq. trivial. *)
  (*       abstract (sim; bg_pf_sim; printable_tac; ins_ibr_sim). *)
  (*     + (* case 1 *) *)
  (*       destruct v as [r [si bs]]. *)
  (*       rewrite Word.int_eq_refl. *)
  (*       assert (bs <> EBP). *)
  (*         ins_ibr_sim. apply reg_no_ebp_neq. trivial. *)
  (*       destruct si as [[sc idx] | ]. *)
  (*       * assert (idx <> ESP). *)
  (*           ins_ibr_sim. eapply si_b_rng_some. eassumption. *)
  (*         abstract (bg_pf_sim; printable_tac). *)
  (*       * abstract (bg_pf_sim; printable_tac; ins_ibr_sim). *)
  (*     + (* case 2 *) *)
  (*       destruct v as [r [si disp]]. *)
  (*       abstract (destruct si as [[sc idx] | ]; printable_tac; ins_ibr_sim). *)
  (*     + (* case 3 *) *)
  (*       abstract printable_tac. *)
  (*     + (* case 4 *) *)
  (*       destruct v as [r [bs disp]]. *)
  (*       abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*     + (* case 5 *) *)
  (*       destruct v as [r [[si bs] disp]]. *)
  (*       rewrite sign_shrink32_8_inv. *)
  (*       destruct si as [[sc idx] | ]. *)
  (*       * unfold sib_b in *; *)
  (*         assert (idx <> ESP). *)
  (*           ins_ibr_sim. eapply si_b_rng_some. eassumption. *)
  (*         abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*       * abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*     + (* case 6 *) *)
  (*       destruct v as [r [bs disp]]. *)
  (*       abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*     + (* case 7 *) *)
  (*       destruct v as [r [[si bs] disp]]. *)
  (*       destruct si as [[sc idx] | ]. *)
  (*       * unfold sib_b in *; *)
  (*         assert (idx <> ESP). *)
  (*           ins_ibr_sim. eapply si_b_rng_some. eassumption. *)
  (*         abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*       * abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*   - destruct w as [r addr]. *)
  (*     destruct addr. *)
  (*     abstract (destruct addrBase as [bs | ]; *)
  (*               destruct addrIndex as [[si idx] | ]; *)
  (*               bg_pf_sim; try parsable_tac; *)
  (*               apply Word.int_eq_true_iff2 in Hdisp_eq;  *)
  (*               subst addrDisp; trivial). *)
  (* Defined. *)

  (** Moderm mode 00 *)
  Definition rm00 := 
    (* case 0 *)
    (reg_no_esp_ebp |+|
    (* case 1 *)
     "100" $$ si_b $ reg_no_ebp) |+|
    (* case 2 *)
    ("100" $$ si_b $ "101" $$ word |+|
    (* case 3 *)
     "101" $$ word).

  (** Moderm mode 01 *)
  Definition rm01 := 
    (* case 0 *)
    reg_no_esp $ byte |+|
    (* case 1 *)
    "100" $$ sib_b $ byte.

  (** Moderm mode 10 *)
  Definition rm10 := 
    (* case 0 *)
    reg_no_esp $ word |+|
    (* case 1 *)
    "100" $$ sib_b $ word.

  (** Same as modrm_gen but no mod "11" case; that is, the second must
      produce an address in a mem operand *)
  (* The old modrm_gen_noreg parser has three help parsers defined first:
     rm00, rm01, rm10; each of them constructs an address. However,
     combining those three would be difficult. In this version, we
     essentially list all possible cases of modes 00, 01, 10 and have a big
     inverse function; didn't use the gen_ast_def tactic because the following
     version using inl/inr explicitly is a bit faster for proofs. *)
  Definition modrm_gen_noreg (reg_t: type)
    (reg_b: wf_bigrammar reg_t) : wf_bigrammar (pair_t reg_t address_t).
    intros.
    refine ((    ("00" $$ reg_b $ rm00) 
             |+| ("01" $$ reg_b $ rm01)
             |+| ("10" $$ reg_b $ rm10))
              @ (fun v => 
                   match v with
                     (* mode 00 *)
                     | inl (r,v1) => 
                       let addr := 
                           match v1 with
                             (* mode 00, case 0 *)
                             | inl (inl base) =>
                               mkAddress (Word.repr 0) (Some base) None
                             (* mode 00, case 1 *)
                             | inl (inr (si,base)) =>
                               mkAddress (Word.repr 0) (Some base) si
                             (* mode 00, case 2 *)
                             | inr (inl (si,disp)) =>
                               mkAddress disp None si
                             (* mode 00, case 3 *)
                             | inr (inr disp) =>
                               mkAddress disp None None
                           end
                       in (r,addr)
                     (* mode 01 *)
                     | inr (inl (r,v1)) =>
                       let addr := 
                           match v1 with
                             (* mode 01, case 0 *)
                             | inl (bs,disp) =>
                               mkAddress (sign_extend8_32 disp) (Some bs) None
                             (* mode 01, case 1 *)
                             | inr ((si,bs),disp) =>
                               mkAddress (sign_extend8_32 disp) (Some bs) si
                           end 
                       in (r,addr)
                     (* mode 10 *)
                     | inr (inr (r,v1)) =>
                       let addr :=
                           match v1 with
                             (* mode 10, case 0 *)
                             | inl (bs,disp) =>
                               mkAddress disp (Some bs) None
                             (* mode 10, case 1 *)
                             | inr ((si,bs),disp) =>
                               mkAddress disp (Some bs) si
                           end
                       in (r,addr)
                   end %% pair_t reg_t address_t)
               & (fun u:[|pair_t reg_t address_t|] => 
                    let (r,addr) := u in
                    match addr with
                      | {| addrDisp:=disp; addrBase:=None; addrIndex:=None |} =>
                        (* alternate encoding: mod00 case2, making reg in si_b be ESP *)
                        Some (inl (r, (inr (inr disp))))
                      | {| addrDisp:=disp; addrBase:=None; addrIndex:=Some si |} =>
                        (* special case: disp32[index*scale]; 
                           the mod bits in mod/rm must be 00 *)
                        Some (inl (r, (inr (inl (Some si,disp)))))
                      | {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=None |} =>
                        if (register_eq_dec bs ESP) then
                            (* alternate encoding: when disp is not zero or cannot 
                               be represented as a byte, then mode01 case 1 and
                               mode10 case 1 can always be used *)
                            if (Word.eq disp Word.zero) then
                              Some (inl (r, (inl (inr (None, ESP)))))
                            else
                              if (repr_in_signed_byte_dec disp) then
                                Some (inr (inl (r, inr ((None, ESP), 
                                                        sign_shrink32_8 disp))))
                              else Some (inr (inr (r, inr ((None, ESP), disp))))
                        else
                          if (register_eq_dec bs EBP) then
                            (* alternate encoding: mode 10 case0 can always be used *)
                            if (repr_in_signed_byte_dec disp)
                            then Some (inr (inl (r, inl (bs, sign_shrink32_8 disp))))
                            else Some (inr (inr (r, inl (bs, disp))))
                          else
                            (* alternate encoding: mode 01 case 0 and mode 10 case 0 
                               can always be used depending on disp *)
                            if (Word.eq disp Word.zero) then
                              Some (inl (r, inl (inl bs)))
                            else
                              if (repr_in_signed_byte_dec disp)
                              then Some (inr (inl (r, inl (bs,
                                                           sign_shrink32_8 disp))))
                              else Some (inr (inr (r, inl (bs, disp))))
                      | {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=Some sci |} =>
                        if (register_eq_dec (snd sci) ESP) then None
                        else if (register_eq_dec bs EBP) then
                               (* alternate encoding: mode10 case1 *)
                               if (repr_in_signed_byte_dec disp) then
                                 Some (inr (inl (r, inr ((Some sci, bs),
                                                         sign_shrink32_8 disp))))
                               else Some (inr (inr (r, inr ((Some sci, bs), disp))))
                             else 
                               (* alternate encoding: mode01 case 1; mode10 case1 *)
                               if (Word.eq disp Word.zero) then
                                 Some (inl (r, (inl (inr (Some sci, bs)))))
                               else
                                 if (repr_in_signed_byte_dec disp) then
                                   Some (inr (inl (r, (inr ((Some sci, bs),
                                                            sign_shrink32_8 disp)))))
                                 else Some (inr (inr (r, inr ((Some sci, bs), disp))))
                    end)
               & _); invertible_tac.
    - destruct_sum.
      + (* mode 00 *)
        destruct v as [r v].
        unfold rm00 in *; destruct_sum.
        * (* case 0 *)
         rewrite Word.int_eq_refl.
         rename v into bs.
         assert (bs<>ESP /\ bs<>EBP).
           ins_ibr_sim. apply reg_no_esp_ebp_neq. trivial.
         abstract (sim; bg_pf_sim; printable_tac; ins_ibr_sim).
        * (* case 1 *)
          destruct v as [si bs].
          rewrite Word.int_eq_refl.
          assert (bs <> EBP).
            ins_ibr_sim; apply reg_no_ebp_neq; trivial.
          destruct si as [[sc idx] | ].
          { assert (idx <> ESP).
              ins_ibr_sim. eapply si_b_rng_some. eassumption.
            abstract (bg_pf_sim; printable_tac).
          }
          { abstract (bg_pf_sim; printable_tac; ins_ibr_sim). }
        * (* case 2 *)
          destruct v as [si disp].
          abstract (destruct si as [[sc idx] | ];
                    printable_tac; ins_ibr_sim).
        * (* case 3 *) abstract printable_tac.
      + (* mode 01 *)
        destruct v as [r v].
        unfold rm01 in *; destruct_sum; ins_ibr_sim.
        * (* case 0 *)
          destruct v as [bs disp].
          abstract (unfold rm00; bg_pf_sim;
                    try destruct_head; printable_tac; ins_ibr_sim).
        * (* case 1 *)
          destruct v as [[si bs] disp].
          rewrite sign_shrink32_8_inv.
          destruct si as [[sc idx] | ].
          { unfold sib_b in *; 
            assert (idx <> ESP).
              ins_ibr_sim. eapply si_b_rng_some. eassumption.
            abstract (unfold rm00; bg_pf_sim;
                      try destruct_head; printable_tac; ins_ibr_sim). }
          { abstract (unfold rm00; bg_pf_sim;
                      try destruct_head; printable_tac; ins_ibr_sim). }
       + (* mode 10 *)
        destruct v as [r v].
        unfold rm10 in *; destruct_sum; ins_ibr_sim.
        * (* case 0 *)
          destruct v as [bs disp].
         abstract (unfold rm00, rm01; bg_pf_sim; 
                   try destruct_head; printable_tac; ins_ibr_sim).
        * (* case 1 *)
          destruct v as [[si bs] disp].
          destruct si as [[sc idx] | ].
          { unfold rm00, rm01, sib_b in *; 
            assert (idx <> ESP).
              ins_ibr_sim. eapply si_b_rng_some. eassumption.
            abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim).
          }
          { abstract (unfold rm00, rm01; bg_pf_sim; 
                      try destruct_head; printable_tac; ins_ibr_sim). }
    - destruct w as [r addr].
      destruct addr.
      abstract (destruct addrBase as [bs | ];
                destruct addrIndex as [[si idx] | ];
                bg_pf_sim; try parsable_tac;
                apply Word.int_eq_true_iff2 in Hdisp_eq;
                subst addrDisp; trivial).
  Defined.
  Extraction Implicit modrm_gen_noreg [reg_t].

  (* Definition modrm_gen_noreg2 (reg_t res_t: type) *)
  (*   (reg_b: wf_bigrammar reg_t)  *)
  (*   (addr_op: funinv address_t res_t)  (* the constructor that converts an *) *)
  (*                                      (* address to result and its inverse *) *)
  (*   (pf: strong_invertible addr_op) *)
  (*   : wf_bigrammar (pair_t reg_t res_t). *)
  (*   intros. *)
  (*   refine ((modrm_gen_noreg reg_b) *)
  (*             @ (fun v => match v with *)
  (*                           | (r, addr) => (r, fst addr_op addr) *)
  (*                         end %% (pair_t reg_t res_t)) *)
  (*             & (fun u => match u with *)
  (*                           | (r, op2) => *)
  (*                             match snd addr_op op2 with *)
  (*                               | Some addr => Some (r, addr) *)
  (*                               | None => None *)
  (*                             end *)
  (*                         end) *)
  (*             & _); invertible_tac; *)
  (*   destruct addr_op as [f1 f2]; *)
  (*   unfold strong_invertible in pf; simpl in pf; *)
  (*   destruct pf as [pf1 pf2]. *)
  (*   - exists v. destruct v as [res addr]. *)
  (*     rewrite pf1. intuition. *)
  (*   - destruct v as [res addr]. *)
  (*     destruct w as [op1 op2]. *)
  (*     remember_rev (f2 op2) as fo. destruct fo. *)
  (*     + rewrite (pf2 addr op2); clear pf1 pf2 H; crush. *)
  (*     + discriminate. *)
  (* Defined. *)
  (* Arguments modrm_gen_noreg2 [reg_t res_t]. *)

  (** a general modrm grammar for integer, floating-point, sse, mmx instructions *)
  Definition modrm_gen (reg_t: type)
    (reg_b : wf_bigrammar reg_t)  (* the grammar that parse a register *)
    : wf_bigrammar (sum_t (pair_t reg_t address_t) (pair_t reg_t reg_t)) :=
    modrm_gen_noreg reg_b |+| "11" $$ reg_b $ reg_b.
  Extraction Implicit modrm_gen [reg_t].

  (* Similar to mod/rm grammar except that the register field is fixed to a
   * particular bit-pattern, and the pattern starting with "11" is excluded. *)
  Definition ext_op_modrm_noreg_ret_addr
          (bs: string) : wf_bigrammar address_t.
    intros.
    refine ((modrm_gen_noreg (! bs))
              @ (fun v => snd v %% address_t)
              & (fun u => Some ((),u))
              & _); invertible_tac.
  Defined.

  Definition ext_op_modrm_noreg (bs: string): wf_bigrammar operand_t.
    intros;
    refine(ext_op_modrm_noreg_ret_addr bs
             @ (Address_op: [|address_t|] -> [|operand_t|])
             & Address_op_inv & _); 
    unfold Address_op_inv; invertible_tac; ins_parsable_tac.
  Defined.

  (* Similar to mod/rm grammar except that the register field is fixed to a
   * particular bit-pattern*)
  Definition ext_op_modrm_gen (reg_t: type)
    (reg_b: wf_bigrammar reg_t)
    (bs:string) : wf_bigrammar (sum_t address_t reg_t) :=
    ext_op_modrm_noreg_ret_addr bs |+| "11" $$ bs $$ reg_b.

  (** modrm_reg returns a register as the first operand, and a second operand *)
  Definition modrm_ret_reg: wf_bigrammar (pair_t register_t operand_t).
    refine ((modrm_gen reg) 
            @ (fun v =>
                 match v with
                   | inl (r, addr) => (r, Address_op addr)
                   | inr (r1, r2) => (r1, Reg_op r2)
                 end %% (pair_t register_t operand_t))
            & (fun u => 
                 match u with
                   | (r, Address_op addr) => Some (inl (r, addr))
                   | (r1, Reg_op r2) => Some (inr (r1, r2))
                   | _ => None
                 end)
            & _); invertible_tac.
    - destruct_all; printable_tac.
    - ins_parsable_tac.
  Defined.

  (** this version returns two operands *)
  Definition modrm: wf_bigrammar (pair_t operand_t operand_t).
    refine (modrm_ret_reg
              @ (fun v => match v with
                            | (r1, op2) => (Reg_op r1, op2)
                          end %% (pair_t operand_t operand_t))
              & (fun u => match u with
                            | (Reg_op r1, op2) => Some (r1, op2)
                            | _ => None
                          end)
              & _); invertible_tac; ins_parsable_tac.
  Defined.

  Definition modrm_noreg : wf_bigrammar (pair_t register_t address_t) :=
    modrm_gen_noreg reg.

  Definition modrm_bv2_noreg: wf_bigrammar (pair_t (bitvector_t 2) address_t) :=
    modrm_gen_noreg (field_intn 2).

 (* note: can be replaced by modrm_noreg since it now produces register_t, address_t *)
  (* general-purpose regs used in SSE instructions *)
  (* Definition modrm_xmm_gp_noreg : wf_bigrammar (pair_t register_t address_t) := *)
  (*   modrm_gen_noreg reg. *)

  Definition ext_op_modrm (bs: string): wf_bigrammar operand_t.
    intros.
    refine ((ext_op_modrm_gen reg bs)
              @ (fun v => match v with
                            | inl addr => Address_op addr
                            | inr r => Reg_op r
                          end %% operand_t)
              & (fun u => match u with
                            | Address_op addr => Some (inl addr)
                            | Reg_op r => Some (inr r)
                            | _ => None
                          end)
              & _); invertible_tac; ins_parsable_tac.
  Defined.

  Definition seg_modrm : wf_bigrammar (pair_t segment_register_t operand_t).
    refine((modrm_gen_noreg segment_reg_b |+| "11" $$ segment_reg_b $ reg)
           @ (fun v =>
                match v with
                    | inl (sr, addr) => (sr, Address_op addr)
                    | inr (sr, r) => (sr, Reg_op r)
                end %% (pair_t segment_register_t operand_t))
           & (fun u =>
                match u with
                  | (sr, Address_op addr) => Some (inl (sr, addr))
                  | (sr, Reg_op r) => Some (inr (sr, r))
                  | _ => None
                end)
           & _); invertible_tac; ins_parsable_tac.
  Defined.

  (** An parser that parses immediates; takes the opsize override into account; 
      always returns a word *)
  Definition imm_b (opsize_override: bool) : wf_bigrammar word_t. 
    intros.
    refine(match opsize_override with
             | false => word 
             | true => halfword @ (fun w => sign_extend16_32 w %% word_t)
                                & (fun w => 
                                     if repr_in_signed_halfword_dec w then
                                       Some (sign_shrink32_16 w)
                                     else None
                                  )
                                  & _
           end); invertible_tac.
    - rewrite sign_shrink32_16_inv. 
      generalize (repr_in_signed_byte_extend16_32 v); intro.
      destruct_head; [printable_tac | intuition].
    - destruct (repr_in_signed_halfword_dec w); parsable_tac.
  Defined.

  (** ** Lemmas about previous parsers *)

  Lemma modrm_gen_noreg_rng_inv reg_t (reg_b: wf_bigrammar reg_t)
        (r:[|reg_t|]) (addr:[|address_t|]):
    in_bigrammar_rng (` (modrm_gen_noreg reg_b)) (r,addr) ->
    in_bigrammar_rng (` reg_b) r.
  Proof. intros; unfold modrm_gen_noreg in *. 
         repeat (ins_ibr_sim || destruct_pr_var); crush. Qed.

  (* can prove a more precise range lemma if necessary *)
  Lemma modrm_gen_noreg_rng reg_t (reg_b: wf_bigrammar reg_t)
        (r1 r2:[|reg_t|]) addr: 
    in_bigrammar_rng (` (modrm_gen_noreg reg_b)) (r1, addr) ->
    in_bigrammar_rng (` reg_b) r2 -> 
    in_bigrammar_rng (` (modrm_gen_noreg reg_b)) (r2, addr).
  Proof. intros; unfold modrm_gen_noreg in *. ins_ibr_sim.
    compute [fst].
    match goal with
      | [v: [|sum_t ?t1 (sum_t ?t2 ?t3)|] |- _] => 
        destruct_sum; ins_ibr_sim;
        destruct v as [r1' v];
        [exists (inl [|sum_t t2 t3|] (r2, v)) | 
         exists (inr [|t1|] (inl [|t3|] (r2,v))) |
         eexists (inr [|t1|] (inr [|t2|] (r2,v))) ]
    end;
    split; ins_ibr_sim; crush.
  Qed.

  Lemma ext_op_modrm_rng1 bs r: 
    in_bigrammar_rng (` (ext_op_modrm bs)) (Reg_op r).
  Proof. unfold ext_op_modrm; intros; ins_ibr_sim.
    exists (inr [|address_t|] r); compute [fst]. 
    split. 
    + unfold ext_op_modrm_gen; ins_ibr_sim.
    + trivial.
  Qed.
  Hint Resolve ext_op_modrm_rng1: ibr_rng_db.

  Lemma ext_op_modrm_rng_inv (bs:string) op :
    in_bigrammar_rng (` (ext_op_modrm bs)) op ->
    (exists r, op = Reg_op r) \/ (exists addr, op = Address_op addr).
  Proof. unfold ext_op_modrm; intros; ins_ibr_sim.
    destruct v; subst op; [right | left]; eexists; trivial.
  Qed.

  Lemma Reg_op_b_rng op : 
    (exists r, op = Reg_op r) <-> in_bigrammar_rng (`Reg_op_b) op.
  Proof. intros. unfold Reg_op_b; split; intro; ins_ibr_sim.
    - compute [fst]. generalize reg_rng. crush.
    - crush.
  Qed.

  Lemma Reg_op_b_rng2 r: in_bigrammar_rng (`Reg_op_b) (Reg_op r).
  Proof. intros; apply Reg_op_b_rng. eexists; trivial. Qed.
  Hint Resolve Reg_op_b_rng2: ibr_rng_db.

  Lemma modrm_ret_reg_rng_inv r op:
    in_bigrammar_rng (` modrm_ret_reg) (r,op) -> 
    (exists r, op = Reg_op r) \/ (exists addr, op = Address_op addr).
  Proof. unfold modrm_ret_reg; intros. ins_ibr_sim.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_ret_reg_rng1 r1 r2: in_bigrammar_rng (` modrm_ret_reg) (r1, Reg_op r2).
  Proof. intros. unfold modrm_ret_reg, modrm_gen. ins_ibr_sim. compute [fst].
    exists (inr [|pair_t register_t address_t|] (r1, r2)).
    split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_ret_reg_rng1: ibr_rng_db.

  (* with more work, this lemma could be made more general; will do it if necessary *)
  Lemma modrm_ret_reg_rng2 r1 r2 addr: 
    in_bigrammar_rng (` modrm_ret_reg) (r1, Address_op addr) ->
    in_bigrammar_rng (` modrm_ret_reg) (r2, Address_op addr).
  Proof. unfold modrm_ret_reg; intros; ins_ibr_sim; compute [fst].
    destruct v as [[r1' addr'] | [r1' r2']]; try congruence.
    sim; subst r1' addr'.
    unfold modrm_gen in *; ins_ibr_sim.
    exists (inl [|pair_t register_t register_t|] (r2,addr)).
    split.
    - ins_ibr_sim. eapply modrm_gen_noreg_rng. eassumption. ins_ibr_sim.
    - trivial.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` (modrm_ret_reg)) (_, Address_op _)) =>
    eapply modrm_ret_reg_rng2; eassumption : ibr_rng_db.

  Lemma imm_b_false_rng w: in_bigrammar_rng (` (imm_b false)) w.
  Proof. unfold imm_b; intros. ins_ibr_sim. Qed.

  Lemma imm_b_true_rng w:
    repr_in_signed_halfword w -> 
    in_bigrammar_rng (` (imm_b true)) w.
  Proof. unfold imm_b; intros. ins_ibr_sim. compute [fst].
    exists (sign_shrink32_16 w); split.
      - ins_ibr_sim.
      - autorewrite with inv_db. trivial.
  Qed.

  Lemma imm_b_rng w opsize_override:
    repr_in_signed_halfword w -> 
    in_bigrammar_rng (` (imm_b opsize_override)) w.
  Proof. destruct opsize_override; intros.
    - apply imm_b_true_rng; trivial.
    - apply imm_b_false_rng.
  Qed.

  Lemma field_intn_rng n i: 
    in_bigrammar_rng (` (field_intn n)) i.
  Proof. unfold field_intn; intros. ins_ibr_sim.
    exists (bitsn_of_intn i). split.
    - apply field'_rng.
    - simpl. autorewrite with inv_db. trivial.
  Qed.
    
  (** * An X86 bigrammar *)
  (* A better bigrammar for x86 instruction decoder/encoder. The encoder
     spec is more efficient:

     (1) Each individual instruction parser does not return values of
         instr, but instead returns the instruction's arguments; as a
         result, the inverse function does not need to perform a runtime
         test to see what instruction it is as the previous version
         does. At the top level, we disjoint union all instruction parsers
         and use a conversion function to convert abstract syntax trees
         (ast) produced by parsing to instructions.

     (2) The Jcc parser uses the biased union for the two sub-parsers, 
         avoiding runtime tests in those subparsers
   *)

  (* a tactic used to simplify proofs when proving bidirectional grammars about instrs *)
  Ltac ins_pf_sim :=
    ins_ibr_sim; bg_pf_sim;
    repeat match goal with
      | [H: in_bigrammar_rng (` (modrm_ret_reg)) (?r1 ?op2) |- _] => 
        let H2 := fresh "H" in
        generalize (modrm_ret_reg_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op2
      | [H: in_bigrammar_rng (` (ext_op_modrm _)) ?op |- _] => 
        let H2 := fresh "H" in
        generalize (ext_op_modrm_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op
    end.

  Ltac ins_printable_tac := printable_tac_gen ins_pf_sim.
  Ltac ins_invertible_tac := 
    invertible_tac_gen unfold_invertible_ast ins_pf_sim ins_destruct_var.

  Definition AAA_b : wf_bigrammar unit_t := ! "00110111".
  Definition AAD_b : wf_bigrammar unit_t := ! "1101010100001010".
  Definition AAM_b : wf_bigrammar unit_t := ! "1101010000001010".
  Definition AAS_b : wf_bigrammar unit_t := ! "00111111".

  Definition logic_or_arith_env (opsize_override: bool) (opcode1 opcode2: string) : 
    AST_Env (pair_t bool_t (pair_t operand_t operand_t)) :=
    (* register/memory to register and vice versa -- the d bit specifies
       the direction. *)
    {{0, opcode1 $$ "0" $$ anybit $ anybit $ modrm_ret_reg,
     fun v => match v with
                | (d, (w, (r1, op2))) => 
                  if (d:bool) then (w, (Reg_op r1, op2)) else (w, (op2, Reg_op r1))
              end %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* sign extend immediate byte to register *)
    {{1, "1000" $$ "0011" $$ "11" $$ opcode2 $$ reg $ byte,
     fun v => let (r, imm) := v in
                  (true, (Reg_op r, Imm_op (sign_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* zero-extend immediate byte to register *)
    {{2, "1000" $$ "0000" $$ "11" $$ opcode2 $$ reg $ byte,
     fun v => let (r,imm) := v in
                  (false, (Reg_op r, Imm_op (zero_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* immediate word to register *)
    {{3, "1000" $$ "0001" $$ "11" $$ opcode2 $$ reg $ imm_b opsize_override,
     fun v => let (r, imm) := v in (true, (Reg_op r, Imm_op imm))
              %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* zero-extend immediate byte to EAX *)
    {{4, opcode1 $$ "100" $$ byte,
     fun imm => (false, (Reg_op EAX, Imm_op (zero_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* word to EAX *)
    {{5, opcode1 $$ "101" $$ imm_b opsize_override,
     fun imm => (true, (Reg_op EAX, Imm_op imm))
              %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* zero-extend immediate byte to memory *)
    {{6, "1000" $$ "0000" $$ ext_op_modrm_noreg_ret_addr opcode2 $ byte,
     fun v => let (addr,imm) := v in 
              (false, (Address_op addr, Imm_op (zero_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* sign-extend immediate byte to memory *)
    {{7, "1000" $$ "0011" $$ ext_op_modrm_noreg_ret_addr opcode2 $ byte,
     fun v => let (addr,imm) := v in 
              (true, (Address_op addr, Imm_op (sign_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* immediate word to memory *)
    {{8, "1000" $$ "0001" $$ ext_op_modrm_noreg_ret_addr opcode2 $
               imm_b opsize_override,
     fun v => let (addr,imm) := v in 
              (true, (Address_op addr, Imm_op imm))
              %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    ast_env_nil.
  Hint Unfold logic_or_arith_env : env_unfold_db.

  (* The parsing for ADC, ADD, AND, CMP, OR, SBB, SUB, and XOR can be shared *)
  Definition logic_or_arith_b (opsize_override: bool)
    (opcode1 : string) (* first 5 bits for most cases *)
    (opcode2 : string) (* when first 5 bits are 10000, the next byte has 3 bits
                      that determine the opcode *)
    : wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    intros.
    gen_ast_defs (logic_or_arith_env opsize_override opcode1 opcode2).
    refine(
        ((comb_bigrammar gt) @ (comb_map gt)
            & (fun u: [|pair_t bool_t (pair_t operand_t operand_t)|] =>
               let (w, ops) := u in
               let (op1, op2) := ops in
               match op1 with
                 | Reg_op r1 => 
                   match op2 with
                     | Reg_op r2 =>
                       (* alternate encoding:  
                          set the d bit false and reverse the two regs *)
                       inv_case_some case0 (true, (w, (r1, Reg_op r2)))
                     | Address_op a =>
                       inv_case_some case0 (true, (w, (r1, Address_op a)))
                     | Imm_op imm => 
                       match r1 with
                         | EAX =>
                           (* alternate encoding: use inv_case_some case 1, 2 and 3 above *)
                           if w then inv_case_some case5 imm
                           else
                             if (repr_in_unsigned_byte_dec imm) then
                               inv_case_some case4 (zero_shrink32_8 imm)
                             else None
                         | _ =>
                           if w then
                             if (repr_in_signed_byte_dec imm) then
                               inv_case_some case1 (r1, (sign_shrink32_8 imm))
                             else
                               inv_case_some case3 (r1, imm)
                           else
                             if (repr_in_unsigned_byte_dec imm) then
                               inv_case_some case2 (r1, (zero_shrink32_8 imm))
                             else None
                       end
                     | _ => None
                   end
                 | Address_op a =>
                   match op2 with
                     | Reg_op r2 =>
                       inv_case_some case0 (false, (w, (r2, Address_op a)))
                     | Imm_op imm => 
                       if w then
                         if (repr_in_signed_byte_dec imm) then
                           inv_case_some case7 (a, (sign_shrink32_8 imm))
                         else
                           inv_case_some case8 (a, imm)
                       else 
                         if (repr_in_unsigned_byte_dec imm) then
                           inv_case_some case6 (a, (zero_shrink32_8 imm))
                         else None
                     | _ => None
                   end
                 | _ => None
               end)
            & _)); ins_invertible_tac.
  - destruct_sum.
    + (* case 0 *)
      destruct v as [d [w [r1 op2]]].  destruct d; ins_printable_tac.
    + (* case 1 *)
      destruct v as [r b]. 
      destruct r; ins_printable_tac.
      (* EAX case *)
      apply imm_b_rng; apply repr_in_signed_extend; omega.
    + (* case 2 *)
      destruct v as [r b]; destruct r; ins_printable_tac.
    + (* case 3 *)
      destruct v as [r op2]; 
      destruct r; ins_printable_tac.
    + (* case 4 *)
      ins_printable_tac.
    + (* case 5 *)
      ins_printable_tac.
    + (* case 6 *)
      destruct v as [op b]; ins_printable_tac.
    + (* case 7 *)
      destruct v as [op b]; ins_printable_tac.
    + (* case 8 *)
      destruct v as [op1 op2]; ins_printable_tac.
  - destruct w as [wd [op1 op2]]. 
    destruct op1; try parsable_tac.
    + (* op1 = Reg_op _ *)
      destruct op2; try parsable_tac.
      destruct r; destruct wd; ins_pf_sim; parsable_tac.
    + (* op1 = Address_op _ *)
      destruct op2; try parsable_tac.
      destruct wd; ins_pf_sim; parsable_tac.
  Defined.

  Definition ADC_b s := logic_or_arith_b s "00010" "010".
  Definition ADD_b s := logic_or_arith_b s "00000" "000".
  Definition AND_b s := logic_or_arith_b s "00100" "100".
  Definition CMP_b s := logic_or_arith_b s "00111" "111".
  Definition OR_b  s := logic_or_arith_b s "00001" "001".
  Definition SBB_b s := logic_or_arith_b s "00011" "011".
  Definition SUB_b s := logic_or_arith_b s "00101" "101".
  Definition XOR_b s := logic_or_arith_b s "00110" "110".

  Definition ARPL_b := "0110" $$ "0011" $$ modrm.
  Definition BOUND_b := "0110" $$ "0010" $$ modrm.
  Definition BSF_b := "0000" $$ "1111" $$ "1011" $$ "1100" $$ modrm.
  Definition BSR_b := "0000" $$ "1111" $$ "1011" $$ "1101" $$ modrm.
  Definition BSWAP_b : wf_bigrammar register_t := 
    "0000" $$ "1111" $$ "1100" $$ "1" $$ reg.

  Definition bit_test_env (opcode1 opcode2: string) : 
    AST_Env (pair_t operand_t operand_t) :=
    (* bit base a reg; bit offset a byte *)
    {{0, "0000" $$ "1111" $$ "1011" $$ "1010" $$ "11" $$ opcode1 $$ reg $ byte,
     fun v => let (r1,b):=v in (Reg_op r1, Imm_op (zero_extend8_32 b))
                %% pair_t operand_t operand_t}} :::
    (* bit base an address; bit offset a byte *)
    {{1, "0000" $$ "1111" $$ "1011" $$ "1010"
               $$ ext_op_modrm_noreg_ret_addr opcode1 $ byte,
     fun v => let (addr,b):=v in (Address_op addr, Imm_op (zero_extend8_32 b))
                %% pair_t operand_t operand_t}} :::
    (* bit base a reg or an address; bit offset a reg *)
    {{2, "0000" $$ "1111" $$ "101" $$ opcode2 $$ "011" $$ modrm_ret_reg,
     fun v => let (r2,op1):=v in (op1, Reg_op r2)
                %% pair_t operand_t operand_t}} :::
    ast_env_nil.
  Hint Unfold bit_test_env : env_unfold_db.

  Definition bit_test_b (opcode1:string) (opcode2:string) : 
    wf_bigrammar (pair_t operand_t operand_t).
    intros. gen_ast_defs (bit_test_env opcode1 opcode2).
    refine ((comb_bigrammar gt) @ (comb_map gt)
              & (fun u: [|pair_t operand_t operand_t|] =>
                   let (op1,op2):=u in
                   match op1 with
                     | Reg_op r1 =>
                       match op2 with
                         | Imm_op b =>
                           if repr_in_unsigned_byte_dec b
                           then inv_case_some case0 (r1, zero_shrink32_8 b)
                           else None
                           (* alternative encoding possible: switch the two register operands *)
                         | Reg_op r2 => inv_case_some case2 (r2,op1)
                         | _ => None
                       end
                     | Address_op addr =>
                       match op2 with
                         | Imm_op b =>
                           if repr_in_unsigned_byte_dec b
                           then inv_case_some case1 (addr, zero_shrink32_8 b)
                           else None
                         | Reg_op r2 => inv_case_some case2 (r2,op1)
                         | _ => None
                       end
                     | _ => None
                   end)
              & _). ins_invertible_tac.
  Defined.

  Definition BT_b := bit_test_b "100" "00".
  Definition BTC_b := bit_test_b "111" "11".
  Definition BTR_b := bit_test_b "110" "10".
  Definition BTS_b := bit_test_b "101" "01".

  Definition CALL_b : 
    wf_bigrammar (pair_t bool_t (pair_t bool_t (pair_t operand_t
                                                  (option_t selector_t)))).
    set (t:= (pair_t bool_t (pair_t bool_t (pair_t operand_t
                                              (option_t selector_t))))).
    refine((((* case 0 *)
             "1110" $$ "1000" $$ word |+|
             (* case 1 *)
             "1111" $$ "1111" $$ ext_op_modrm "010")
              |+|
            ((* case 2 *)
             "1001" $$ "1010" $$ word $ halfword |+|
             (* case 3 *)
             "1111" $$ "1111" $$ ext_op_modrm "011"))
             @ (fun v =>
                  match v with
                    | inl (inl w) => (true, (false, (Imm_op w, None)))
                    | inl (inr op) => (true, (true, (op, None)))
                    | inr (inl (w,hw)) => (false, (true, (Imm_op w, Some hw)))
                    | inr (inr op) => (false, (true, (op, None)))
                  end %% t)
             & (fun u: [|t|] => 
                  let (near, u1) := u in
                  let (absolute,opsel) := u1 in
                  match near, absolute with
                    | true, false => 
                      match opsel with
                        | (Imm_op w, None) => Some (inl (inl w))
                        | _ => None
                      end
                    | true, true =>
                      match opsel with
                        | (Reg_op _, None) 
                        | (Address_op _, None) => Some (inl (inr (fst opsel)))
                        | _ => None
                      end
                    | false, true =>
                      match opsel with
                        | (Imm_op w, Some hw) => Some (inr (inl (w,hw)))
                        | (Reg_op _, None) 
                        | (Address_op _, None) => Some (inr (inr (fst opsel)))
                        | _ => None
                      end
                    | _, _ => None
                  end)
             & _); unfold t. ins_invertible_tac.
  Defined.

  Definition CDQ_b : wf_bigrammar unit_t := "1001" $$  ! "1001".
  Definition CLC_b : wf_bigrammar unit_t := "1111" $$ ! "1000".
  Definition CLD_b : wf_bigrammar unit_t := "1111" $$ ! "1100".
  Definition CLI_b : wf_bigrammar unit_t := "1111" $$ ! "1010".
  Definition CLTS_b : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0000" $$ ! "0110".
  Definition CMC_b : wf_bigrammar unit_t := "1111" $$ ! "0101".
  Definition CMPS_b : wf_bigrammar Char_t := "1010" $$ "011" $$ anybit.

  Definition CMPXCHG_b := 
    "0000" $$ "1111" $$ "1011" $$ "000" $$ anybit $ modrm.

  Definition CPUID_b : wf_bigrammar unit_t := "0000" $$ "1111" $$ "1010" $$ ! "0010".
  Definition CWDE_b : wf_bigrammar unit_t := "1001" $$ ! "1000".
  Definition DAA_b : wf_bigrammar unit_t := "0010" $$ ! "0111".
  Definition DAS_b : wf_bigrammar unit_t := "0010" $$ ! "1111".

  Definition DEC_b: wf_bigrammar (pair_t bool_t operand_t).
    refine(((* case 0 *)
            "1111" $$ "111" $$ anybit $ "11001" $$ reg |+|
            (* case 1 *)
            "0100" $$ "1" $$ reg |+|
            (* case 2 *)
            "1111" $$ "111" $$ anybit $ ext_op_modrm_noreg_ret_addr "001")
             @ (fun v =>
                  match v with
                    | inl (w,r) => (w, Reg_op r)
                    | inr (inl r) => (true, Reg_op r)
                    | inr (inr (w,addr)) => (w, Address_op addr)
                  end %% pair_t bool_t operand_t)
             & (fun u : [| pair_t bool_t operand_t |] => 
                  let (b,op):=u in
                  match op with
                    | Reg_op r => 
                      (* alternate encoding possible, when "fst u" is true.
                         use case 1 above *)
                      Some (inl (fst u, r))
                    | Address_op addr => Some (inr (inr (fst u, addr)))
                    | _ => None
                  end)
             & _); ins_invertible_tac.
  Defined.

  Definition DIV_b: wf_bigrammar (pair_t bool_t operand_t).
    refine (("1111" $$ "011" $$ anybit $ "11110" $$ reg |+|
             "1111" $$ "011" $$ anybit $ ext_op_modrm_noreg_ret_addr "110")
              @ (fun v =>
                   match v with
                     | inl (w,r) => (w, Reg_op r)
                     | inr (w,addr) => (w, Address_op addr)
                   end %% pair_t bool_t operand_t)
              & (fun u: [|pair_t bool_t operand_t|] =>
                   let (b,op):=u in
                   match op with
                     | Reg_op r => Some (inl (fst u, r))
                     | Address_op addr => Some (inr (fst u, addr))
                     | _ => None
                   end)
              & _); ins_invertible_tac.
  Defined.

  Definition HLT_b : wf_bigrammar unit_t := "1111" $$ ! "0100".

  Definition IDIV_b: wf_bigrammar (pair_t bool_t operand_t).
    refine (("1111" $$ "011" $$ anybit $ "11111" $$ reg |+|
             "1111" $$ "011" $$ anybit $ ext_op_modrm_noreg_ret_addr "111")
              @ (fun v =>
                   match v with
                     | inl (w,r) => (w, Reg_op r)
                     | inr (w, addr) => (w, Address_op addr)
                   end %% pair_t bool_t operand_t)
              & (fun u: [|pair_t bool_t operand_t|] =>
                   let (b,op):=u in
                   match op with
                     | Reg_op r => Some (inl (fst u, r))
                     | Address_op addr => Some (inr (fst u, addr))
                     | _ => None
                   end)
              & _); ins_invertible_tac.
  Defined.


  Definition IMUL_b (opsize_override:bool): 
    wf_bigrammar (pair_t bool_t (pair_t operand_t (pair_t (option_t operand_t)
                                                     (option_t word_t)))).
    intros.
    refine((((* case 0 *)
             "1111" $$ "011" $$ anybit $ ext_op_modrm "101" |+|
             (* case 1 *)
             "0000" $$ "1111" $$ "1010" $$ "1111" $$ modrm_ret_reg)
              |+|
            ((* case 2 *)
              "0110" $$ "1011" $$ modrm_ret_reg $ byte |+|
             (* case 3 *)
              "0110" $$ "1001" $$ modrm_ret_reg $ imm_b opsize_override))
             @ (fun u =>
                  match u with
                    | inl (inl (w,op1)) => (w, (op1, (None, None)))
                    | inl (inr (r1,op2)) => (false, (Reg_op r1, (Some op2, None)))
                    | inr (inl ((r1,op2),b)) =>
                      (true, (Reg_op r1, (Some op2, Some (sign_extend8_32 b))))
                    | inr (inr ((r1,op2),imm)) =>
                      (negb opsize_override, (Reg_op r1, (Some op2, Some imm)))
                  end %%
                  pair_t bool_t (pair_t operand_t (pair_t (option_t operand_t) (option_t word_t))))
             & (fun u:[|pair_t bool_t
                          (pair_t operand_t (pair_t (option_t operand_t) (option_t word_t)))|] => 
                  let (w,u1):= u in
                  let (op1,u2):= u1 in
                  match u2 with
                    | (None,None) => 
                      match op1 with
                        | Reg_op _ | Address_op _ => Some (inl (inl (w,op1)))
                        | _ => None
                      end
                    | (Some op2, None) => 
                      match w,op1,op2 with
                        | false,Reg_op r1,Reg_op _ 
                        | false,Reg_op r1,Address_op _ => Some (inl (inr (r1, op2)))
                        | _,_,_=> None
                      end
                    | (Some op2, Some imm) =>
                      match op1, op2 with
                        | Reg_op r1, Reg_op _ | Reg_op r1, Address_op _ =>
                          if w then                                                 
                            if repr_in_signed_byte_dec imm then
                              (* alternate encoding possible when imm is a byte; use case 3 *)
                              Some (inr (inl ((r1,op2), sign_shrink32_8 imm)))
                            else if opsize_override then None
                                 else Some (inr (inr ((r1,op2),imm)))
                          else if opsize_override then Some (inr (inr ((r1,op2),imm)))
                               else None
                        | _,_ => None
                      end
                    | _ => None
                  end)
             & _); ins_invertible_tac.
    - destruct_sum; try ins_printable_tac.
      + (* case 3 *)
        destruct v as [[r1 op2] imm].
        destruct opsize_override; compute [negb];
        ins_printable_tac.
    -  abstract (destruct w as [bl [op1 [w1 w2]]];
         destruct op1; destruct bl;
         destruct w1 as [op2 | ];
         destruct w2; try parsable_tac;
         destruct op2; destruct opsize_override;
         ins_pf_sim; parsable_tac).
  Qed.

  Definition IN_b: wf_bigrammar (pair_t char_t (option_t byte_t)).
    refine (("1110" $$ "010" $$ anybit $ byte |+| 
             "1110" $$ "110" $$ anybit)
              @ (fun v => 
                   match v with
                     | inl (w,b) => (w, Some b)
                     | inr w => (w, None)
                   end %% (pair_t char_t (option_t byte_t)))
              & (fun u => 
                   match u with
                     | (w, Some b) => Some (inl (w,b))
                     | (w, None) => Some (inr w)
                   end)
              & _); ins_invertible_tac.
  Defined.

  Definition INC_b: wf_bigrammar (pair_t bool_t operand_t).
    refine (("1111" $$ "111" $$ anybit $ "11000" $$ reg |+|
             "0100" $$ "0" $$ reg |+|
             "1111" $$ "111" $$ anybit $ ext_op_modrm_noreg_ret_addr "000")
              @ (fun v => 
                   match v with
                     | inl (w,r) => (w, Reg_op r)
                     | inr (inl r) => (true, Reg_op r)
                     | inr (inr (w,addr)) => (w,Address_op addr)
                   end %% pair_t bool_t operand_t)
              & (fun u: [|pair_t bool_t operand_t|] =>
                   let (w,op):=u in
                   match op with
                     | Reg_op r => 
                       if w then Some (inr (inl r)) (* alternate encoding: case 0 *)
                       else Some (inl (w,r))
                     | Address_op addr => Some (inr (inr (w,addr)))
                     | _ => None
                   end)
              & _); ins_invertible_tac.
    - destruct_sum; try ins_printable_tac.
      + (* case 0 *)
        destruct v as [w r].
        destruct w; ins_printable_tac.
  Defined.

  Definition INS_b : wf_bigrammar Char_t := "0110" $$ "110" $$ anybit.
  
  Definition INTn_b : wf_bigrammar byte_t := "1100" $$ "1101" $$ byte.
  Definition INT_b : wf_bigrammar unit_t := "1100" $$ ! "1100".
  Definition INTO_b : wf_bigrammar unit_t := "1100" $$ ! "1110".
  
  Definition INVD_b : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0000" $$ ! "1000".

  Definition INVLPG_b: wf_bigrammar operand_t :=
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg "111".

  Definition IRET_b: wf_bigrammar unit_t := "1100" $$ ! "1111".

  Definition Jcc_b: wf_bigrammar (pair_t condition_t word_t). 
    refine (("0111" $$ tttn $ byte |+|
             "0000" $$ "1111" $$ "1000" $$ tttn $ word)
              @ (fun v => 
                   match v with
                     | inl (ct,b) => (ct, sign_extend8_32 b)
                     | inr (ct,imm) => (ct, imm)
                   end %% pair_t condition_t word_t)
              & (fun u: [|pair_t condition_t word_t|] => 
                   let (ct,imm) := u in
                   if repr_in_signed_byte_dec imm then
                     (* alternate encoding possible: case 1 *)
                     Some (inl (ct, sign_shrink32_8 imm))
                   else Some (inr (ct, imm)))
              & _); ins_invertible_tac.
  Defined.

  Definition JCXZ_b := "1110" $$ "0011" $$ byte.

  Definition JMP_env :
    AST_Env (pair_t bool_t
                    (pair_t bool_t (pair_t operand_t (option_t selector_t)))) :=
    (* near relative jump; sign extend byte *)
    {{0, "1110" $$ "1011" $$ byte,
     fun b => (true, (false, (Imm_op (sign_extend8_32 b), None)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))}} :::
    (* near relative jump via a word *)
    {{1, "1110" $$ "1001" $$ word,
     fun imm => (true, (false, (Imm_op imm, None)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))}} :::
    (* near absolute jump via an operand *)
    {{2, "1111" $$ "1111" $$ ext_op_modrm "100",
     fun op => (true, (true, (op, None)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))}} :::
    (* far absolute jump via base and offset *) 
    {{3, "1110" $$ "1010" $$ word $ halfword,
     fun v => let (base,offset):=v in 
              (false, (true, (Imm_op base, Some offset)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))}} :::
    (* far abslute jump via operand *)
    {{4, "1111" $$ "1111" $$ ext_op_modrm "101",
     fun op => (false, (true, (op, None)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))}} :::
    ast_env_nil.
  Hint Unfold JMP_env : env_unfold_db.

  Definition JMP_b: 
    wf_bigrammar (pair_t bool_t
                         (pair_t bool_t (pair_t operand_t (option_t selector_t)))).
    gen_ast_defs JMP_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
              & (fun u: [|pair_t bool_t
                           (pair_t bool_t (pair_t operand_t (option_t selector_t)))|]
                 =>
                   let (near,u1):=u in
                   let (absolute,u2):=u1 in
                   match near, absolute with
                     | true,false =>
                       match u2 with
                         | (Imm_op imm, None) =>
                           if (repr_in_signed_byte_dec imm) then
                             (* alternate encoding: case 1 *)
                             inv_case_some case0 (sign_shrink32_8 imm)
                           else inv_case_some case1 imm
                         | _ => None
                       end
                     | true,true => 
                       match u2 with
                         | (Reg_op _, None)
                         | (Address_op _, None) => inv_case_some case2 (fst u2)
                         | _ => None
                       end
                     | false,true =>
                       match u2 with
                         | (Imm_op base, Some offset) =>
                           inv_case_some case3 (base,offset)
                         | (Reg_op _, None)
                         | (Address_op _, None) =>
                           inv_case_some case4 (fst u2)
                         | _ => None
                       end
                     | _,_ => None
                   end)
              & _); clear_ast_defs; ins_invertible_tac.
  Defined.

  Definition LAHF_b := "1001" $$ ! "1111".
  Definition LAR_b := 
    "0000" $$ "1111" $$ "0000" $$ "0010" $$ modrm.
  Definition LDS_b := "1100" $$ "0101" $$ modrm.
  Definition LEA_b: wf_bigrammar (pair_t operand_t operand_t).
    refine ("1000" $$ "1101" $$ modrm_noreg
             @ (fun v => (Reg_op (fst v), Address_op (snd v))
                           %% pair_t operand_t operand_t)
             & (fun u: [|pair_t operand_t operand_t|] => 
                  match u with
                    | (Reg_op r, Address_op addr) => Some (r,addr)
                    | _ => None
                  end)
             & _); ins_invertible_tac.
  Defined.

  Definition LEAVE_b := "1100" $$ !"1001".
  Definition LES_b := "1100" $$ "0100" $$ modrm.
  Definition LFS_b := "0000" $$ "1111" $$ "1011" $$ "0100" $$ modrm.
  Definition LGDT_b : wf_bigrammar operand_t := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg "010".
  Definition LGS_b := "0000" $$ "1111" $$ "1011" $$ "0101" $$ modrm.
  Definition LIDT_b := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg "011".

  Definition LLDT_b: wf_bigrammar operand_t. 
    refine(("0000" $$ "1111" $$ "0000" $$ "0000" $$ "11" $$ "010" $$ reg 
             |+|
            "0000" $$ "1111" $$ "0000" $$ "0000"
               $$ ext_op_modrm_noreg_ret_addr "010")
             @ (fun v =>
                  match v with
                    | inl r => Reg_op r
                    | inr addr => Address_op addr
                  end %% operand_t)
             & (fun u =>
                  match u with
                    | Reg_op r => Some (inl r)
                    | Address_op addr => Some (inr addr)
                    | _ => None
                  end)
             & _); ins_invertible_tac.
  Defined.

  Definition LMSW_b : wf_bigrammar operand_t.
    refine (("0000" $$ "1111" $$ "0000" $$ "0001" $$ "11" $$ "110" $$ reg
             |+|
             "0000" $$ "1111" $$ "0000" $$ "0001"
                $$ ext_op_modrm_noreg_ret_addr "110" )
             @ (fun v =>
                  match v with
                    | inl r => Reg_op r
                    | inr addr => Address_op addr
                  end %% operand_t)
             & (fun u =>
                  match u with
                    | Reg_op r => Some (inl r)
                    | Address_op addr => Some (inr addr)
                    | _ => None
                  end)
             & _); ins_invertible_tac.
  Defined.

  (* JGM: note, this isn't really an instruction, but rather a prefix.  So it
     shouldn't be included in the list of instruction grammars. *)
(*  Definition LOCK_b := "1111" $$ ! "0000" *)

  Definition LODS_b := "1010" $$ "110" $$ anybit.
  Definition LOOP_b := "1110" $$ "0010" $$ byte.
  Definition LOOPZ_b := "1110" $$ "0001" $$ byte.
  Definition LOOPNZ_b := "1110" $$ "0000" $$ byte.

  Definition LSL_b := "0000" $$ "1111" $$ "0000" $$ "0011" $$ modrm.
  Definition LSS_b := "0000" $$ "1111" $$ "1011" $$ "0010" $$ modrm.
  Definition LTR_b := "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "011".

  (* This may not be right. Need to test this thoroughly. 
     There is no 8bit mode for CMOVcc *)
  Definition CMOVcc_b := "0000" $$ "1111" $$ "0100" $$ tttn $ modrm.

  Definition MOV_env (opsize_override:bool):
    AST_Env (pair_t bool_t (pair_t operand_t operand_t)) :=
    (* op2 to op1 *)
    {{0, "1000" $$ "101" $$ anybit $ modrm_ret_reg,
     fun v => match v with (w,(r1,op2)) => (w,(Reg_op r1,op2)) end
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* op1 to op2 *)
    {{1, "1000" $$ "100" $$ anybit $ modrm_ret_reg,
     fun v => match v with (w,(r1,op2)) => (w,(op2,Reg_op r1)) end
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* immediate to reg *)
    {{2, "1100" $$ "0111" $$ "11" $$ "000" $$ reg $ imm_b opsize_override,
     fun v => match v with (r,imm) => (true, (Reg_op r, Imm_op imm)) end
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* zero-extend byte to reg *)
    {{3, "1100" $$ "0110" $$ "11" $$ "000" $$ reg $ byte,
     fun v => match v with
                  (r,b) => (false, (Reg_op r, Imm_op (zero_extend8_32 b)))
              end
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* immediate to reg; alternate encoding*)
    {{4, "1011" $$ "1" $$ reg $ imm_b opsize_override,
     fun v => match v with (r,imm) => (true, (Reg_op r, Imm_op imm)) end
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* zero-extend byte to reg; alternate encoding *)
    {{5, "1011" $$ "0" $$ reg $ byte,
     fun v => match v with
                  (r,b) => (false, (Reg_op r, Imm_op (zero_extend8_32 b)))
              end
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* immediate to mem *)
    {{6, "1100" $$ "0111" $$ ext_op_modrm_noreg_ret_addr "000"
               $ imm_b opsize_override,
     fun v => match v with
                  (addr,imm) => (true, (Address_op addr, Imm_op imm))
              end
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* zero-extend byte to mem *)
    {{7, "1100" $$ "0110" $$ ext_op_modrm_noreg_ret_addr "000" $ byte,
     fun v => match v with
                  (addr,b) => (false, (Address_op addr, Imm_op (zero_extend8_32 b)))
              end
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* 32-bit memory to EAX *)
    {{8, "1010" $$ "0001" $$ word,
     fun imm => (true, (Reg_op EAX, Offset_op imm))
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* 8-bit memory to EAX *)
    {{9, "1010" $$ "0000" $$ word,
     fun imm => (false, (Reg_op EAX, Offset_op imm))
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* EAX to memory (update 32 bits in mem) *)
    {{10, "1010" $$ "0011" $$ word,
     fun imm => (true, (Offset_op imm, Reg_op EAX))
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    (* EAX to memory (update 8 bits in mem) *)
    {{11, "1010" $$ "0010" $$ word,
     fun imm => (false, (Offset_op imm, Reg_op EAX))
        %% pair_t bool_t (pair_t operand_t operand_t)}} :::
    ast_env_nil.
  Hint Unfold MOV_env : env_unfold_db.

  Definition MOV_b (opsize_override:bool): 
    wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    intros. gen_ast_defs (MOV_env opsize_override).
    refine ((comb_bigrammar gt) @ (comb_map gt)
              & (fun u: [|pair_t bool_t (pair_t operand_t operand_t)|] => 
                   let (w,u1):=u in
                   let (op1,op2):=u1 in
                   match op1 with
                     | Reg_op r1 => 
                       match op2 with
                         | Reg_op _
                         | Address_op _ =>
                           (* alternate encoding when both op1 and op2 are Reg_op: 
                              case1 and swap op1 and op2 *)
                           inv_case_some case0 (w, (r1, op2))
                         | Imm_op imm => 
                           if w then (* use case 4; alternate encoding: case 2 *)
                             inv_case_some case4 (r1,imm)
                           else
                             if (repr_in_unsigned_byte_dec imm)
                             then
                             (* use case 5; alternate encoding: case 3 *)
                               inv_case_some case5 (r1, zero_shrink32_8 imm)
                             else None
                         | Offset_op imm => 
                           match r1 with
                             | EAX => if w then inv_case_some case8 imm
                                      else inv_case_some case9 imm
                             | _ => None
                           end
                       end
                     | Address_op addr =>
                       match op2 with
                         | Reg_op r => 
                           inv_case_some case1 (w,(r, Address_op addr))
                         | Imm_op imm =>
                           if w then inv_case_some case6 (addr,imm)
                           else 
                             if (repr_in_unsigned_byte_dec imm)
                             then inv_case_some case7 (addr, zero_shrink32_8 imm)
                             else None
                         | _ => None
                       end
                     | Offset_op imm => 
                       match op2 with
                         | Reg_op EAX => 
                           if w then inv_case_some case10 imm else inv_case_some case11 imm
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); ins_invertible_tac.
    - abstract 
        (destruct w as [wd [op1 op2]]; destruct op1; try parsable_tac;
         destruct op2; ins_pf_sim; try parsable_tac;
         destruct wd; try parsable_tac;
         destruct r; parsable_tac).
  Defined.

  Definition MOVCR_b :=
    "0000" $$ "1111" $$ "0010" $$ "00" $$ anybit $ "0" $$ "11"
           $$ control_reg_b $ reg.

  Definition MOVDR_b := 
    "0000" $$ "1111" $$ "0010" $$ "00" $$ anybit $ "111" $$ debug_reg_b $ reg.

  Definition MOVSR_b := "1000" $$ "11" $$ anybit $ "0" $$ seg_modrm.
  
  Definition MOVBE_b : wf_bigrammar (pair_t operand_t operand_t). 
    refine ("0000" $$ "1111" $$ "0011" $$ "1000" $$ "1111" $$ "000"
                   $$ anybit $ modrm_ret_reg
             @ (fun v: [|pair_t bool_t (pair_t register_t operand_t)|] => 
                  match v with
                    | (w,(r1,op2)) =>
                      if w then (op2, Reg_op r1) else (Reg_op r1, op2)
                  end %% pair_t operand_t operand_t)
             & (fun u => 
                  match u with
                    | (Reg_op r1, Reg_op r2) =>
                      (* alternate encoding: make w false and swap the two operands *)
                      Some (true, (r2, Reg_op r1)) 
                    | (Reg_op r1, Address_op _) => 
                      Some (false, (r1, snd u))
                    | (Address_op _, Reg_op r1) => 
                      Some (true, (r1, fst u))
                    | _ => None
                  end)
             & _); ins_invertible_tac.
    - destruct v as [w [r1 op2]]. 
      destruct w; ins_pf_sim; printable_tac; ins_ibr_sim.
  Defined.
                                             
  Definition MOVS_b := "1010" $$ "010" $$ anybit. 
  Definition MOVSX_b := "0000" $$ "1111" $$ "1011" $$ "111" $$ anybit $ modrm.
  Definition MOVZX_b := "0000" $$ "1111" $$ "1011" $$ "011" $$ anybit $ modrm.

  Definition MUL_b := "1111" $$ "011" $$ anybit $ ext_op_modrm "100". 
  Definition NEG_b := "1111" $$ "011" $$ anybit $ ext_op_modrm "011".

  Definition NOP_b := 
  (* The following is the same as the encoding of "XCHG EAX, EAX"
    "1001" $$ bits "0000" @ (fun _ => NOP None %% instruction_t)
  |+| *)
    "0000" $$ "1111" $$ "0001" $$ "1111" $$ ext_op_modrm "000". 

  Definition NOT_b := "1111" $$ "011" $$ anybit $ ext_op_modrm "010".

  Definition OUT_b :wf_bigrammar (pair_t bool_t (option_t byte_t)).
    refine ((("1110" $$ "011" $$ anybit $ byte) |+|
             ("1110" $$ "111" $$ anybit))
              @ (fun v =>
                   match v with
                     | inl (w, b) => (w, Some b)
                     | inr w => (w, None)
                   end %% pair_t bool_t (option_t byte_t))
              & (fun u:[|pair_t bool_t (option_t byte_t)|] => 
                   match u with
                     | (w, Some b) => Some (inl (w,b))
                     | (w, None) => Some (inr w)
                   end)
              & _); ins_invertible_tac.
  Defined.

  Definition OUTS_b := "0110" $$ "111" $$ anybit.

  Definition POP_b : wf_bigrammar operand_t. 
    refine (("1000" $$ "1111" $$ ext_op_modrm "000" |+|
             "0101" $$ "1" $$ reg) 
              @ (fun v => 
                   match v with
                     | inl op => op
                     | inr r => Reg_op r
                   end %% operand_t)
              & (fun u =>
                   match u with
                     | Reg_op r => Some (inr r) (* alterante encoding: the first case *)
                     | Address_op addr => Some (inl u)
                     | _ => None
                   end)
              & _); ins_invertible_tac.
  Defined.

  Definition POPSR_env : AST_Env segment_register_t :=
    {{0, "000" $$ "00" $$ ! "111", (fun v => ES %% segment_register_t)}} :::
    {{1, "000" $$ "10" $$ ! "111", (fun v => SS %% segment_register_t)}} :::
    {{2, "000" $$ "11" $$ ! "111", (fun v => DS %% segment_register_t)}} :::
    {{3, "0000" $$ "1111" $$ "10" $$ "100" $$ ! "001",
     (fun _ => FS %% segment_register_t)}} :::
    {{4, "0000" $$ "1111" $$ "10" $$ "101" $$ ! "001",
     (fun _ => GS %% segment_register_t)}} :::
    ast_env_nil.
  Hint Unfold POPSR_env : env_unfold_db.

  Definition POPSR_b : wf_bigrammar segment_register_t.
    gen_ast_defs POPSR_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u => match u with
                             | ES => inv_case_some case0 ()
                             | SS => inv_case_some case1 ()
                             | DS => inv_case_some case2 ()
                             | FS => inv_case_some case3 ()
                             | GS => inv_case_some case4 ()
                             | _ => None
                           end)
               & _); ins_invertible_tac.
  Defined.

  Definition POPA_b := "0110" $$ ! "0001".
  Definition POPF_b := "1001" $$ ! "1101".

  Definition PUSH_env : AST_Env (pair_t bool_t operand_t) :=
    {{0, "1111" $$ "1111" $$ ext_op_modrm_noreg_ret_addr "110", 
     (fun addr => (true, Address_op addr) %% pair_t bool_t operand_t)}} :::
    {{1, "0101" $$ "0" $$ reg, 
     (fun r => (true, Reg_op r) %% pair_t bool_t operand_t)}} :::
    {{2, "0110" $$ "1010" $$ byte,
     (fun b => (false, Imm_op (sign_extend8_32 b)) %% pair_t bool_t operand_t)}} :::
    {{3, "0110" $$ "1000" $$ word,
     (fun w => (true, Imm_op w) %% pair_t bool_t operand_t)}} :::
    ast_env_nil.
  Hint Unfold PUSH_env : env_unfold_db.

  Definition PUSH_b : wf_bigrammar (pair_t bool_t operand_t).
    gen_ast_defs PUSH_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | (true, Address_op addr) => inv_case_some case0 addr
                      | (true, Reg_op r) => inv_case_some case1 r
                      | (true, Imm_op w) => inv_case_some case3 w
                      | (false, Imm_op w) =>
                        if (repr_in_signed_byte_dec w) then inv_case_some case2 (sign_shrink32_8 w)
                        else None
                      | _ => None
                    end)
               & _); ins_invertible_tac.
  Defined.

  Definition PUSHSR_env : AST_Env segment_register_t :=
    {{0, "000" $$ "00" $$ ! "110", (fun v => ES %% segment_register_t)}} :::
    {{1, "000" $$ "01" $$ ! "110", (fun v => CS %% segment_register_t)}} :::
    {{2, "000" $$ "10" $$ ! "110", (fun v => SS %% segment_register_t)}} :::
    {{3, "000" $$ "11" $$ ! "110", (fun v => DS %% segment_register_t)}} :::
    {{4, "0000" $$ "1111" $$ "10" $$ "100" $$ ! "000", 
     (fun v => FS %% segment_register_t)}} :::
    {{5, "0000" $$ "1111" $$ "10" $$ "101" $$ ! "000",
     (fun v => GS %% segment_register_t)}} :::
    ast_env_nil.
  Hint Unfold PUSHSR_env : env_unfold_db.

  Definition PUSHSR_b : wf_bigrammar segment_register_t.
    gen_ast_defs PUSHSR_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u => 
                    match u with
                      | ES => inv_case_some case0 ()
                      | CS => inv_case_some case1 ()
                      | SS => inv_case_some case2 ()
                      | DS => inv_case_some case3 ()
                      | FS => inv_case_some case4 ()
                      | GS => inv_case_some case5 ()
                    end)
               & _); clear_ast_defs; ins_invertible_tac.
  Defined.

  Definition PUSHA_b := "0110" $$ ! "0000".
  Definition PUSHF_b := "1001" $$ ! "1100".

  Definition rotate_b (extop:string): 
    wf_bigrammar (pair_t bool_t (pair_t operand_t reg_or_immed_t)).
    intros.
    refine (("1101" $$ "000" $$ anybit $ ext_op_modrm extop |+|
             "1101" $$ "001" $$ anybit $ ext_op_modrm extop |+|
             "1100" $$ "000" $$ anybit $ ext_op_modrm extop $ byte)
              @ (fun v => 
                   match v with
                     | inl (w, op) => (w, (op, Imm_ri (Word.repr 1)))
                     | inr (inl (w, op)) => (w, (op, Reg_ri ECX))
                     | inr (inr (w, (op, b))) => (w, (op, Imm_ri b))
                   end %% pair_t bool_t (pair_t operand_t reg_or_immed_t))
              & (fun u: [|pair_t bool_t (pair_t operand_t reg_or_immed_t)|] => 
                   let (w,u1) := u in
                   match u1 with
                     | (Reg_op _, Imm_ri b) 
                     | (Address_op _, Imm_ri b) => Some (inr (inr (w,(fst u1,b))))
                     | (Reg_op _, Reg_ri ECX)
                     | (Address_op _, Reg_ri ECX) => Some (inr (inl (w, fst u1)))
                     | _ => None
                   end)
              & _); ins_invertible_tac.
    - ins_parsable_tac;
      match goal with
      | [ H: match ?r with | EAX => _ | ECX => _ | EDX => _ | EBX => _
                     | ESP => _ | EBP => _ | ESI => _ | EDI => _ end
             = _ |- _ ] => destruct r
      end; ins_parsable_tac.
  Defined.
                                    
  Definition RCL_b := rotate_b "010".
  Definition RCR_b := rotate_b "011".

  Definition RDMSR_b := "0000" $$ "1111" $$ "0011" $$ ! "0010".
  Definition RDPMC_b := "0000" $$ "1111" $$ "0011" $$ ! "0011".
  Definition RDTSC_b := "0000" $$ "1111" $$ "0011" $$ ! "0001".
  Definition RDTSCP_b := "0000" $$ "1111" $$ "0000" $$ "0001" $$ "1111"
                                $$ ! "1001".

  (*
  Definition REPINS_b := "1111" $$ "0011" $$ "0110" $$ "110" $$ anybit @ 
    (fun x => REPINS x %% instruction_t).
  Definition REPLODS_b := "1111" $$ "0011" $$ "1010" $$ "110" $$ anybit @ 
    (fun x => REPLODS x %% instruction_t).
  Definition REPMOVS_b := "1111" $$ "0011" $$ "1010" $$ "010" $$ anybit @ 
    (fun x => REPMOVS x %% instruction_t).
  Definition REPOUTS_b := "1111" $$ "0011" $$ "0110" $$ "111" $$ anybit @ 
    (fun x => REPOUTS x %% instruction_t).
  Definition REPSTOS_b := "1111" $$ "0011" $$ "1010" $$ "101" $$ anybit @ 
    (fun x => REPSTOS x %% instruction_t).
  Definition REPECMPS_b := "1111" $$ "0011" $$ "1010" $$ "011" $$ anybit @ 
    (fun x => REPECMPS x %% instruction_t).
  Definition REPESCAS_b := "1111" $$ "0011" $$ "1010" $$ "111" $$ anybit @ 
    (fun x => REPESCAS x %% instruction_t).
  Definition REPNECMPS_b := "1111" $$ "0010" $$ "1010" $$ "011" $$ anybit @ 
    (fun x => REPNECMPS x %% instruction_t).
  Definition REPNESCAS_b := "1111" $$ "0010" $$ "1010" $$ "111" $$ anybit @ 
    (fun x => REPNESCAS x %% instruction_t).
  *)

  Definition RET_env : AST_Env (pair_t bool_t (option_t half_t)) := 
    {{0, "1100" $$ ! "0011", 
     (fun v => (true, None) %% pair_t bool_t (option_t half_t))}} :::
    {{1, "1100" $$ "0010" $$ halfword,
     (fun h => (true, Some h) %% pair_t bool_t (option_t half_t))}} :::
    {{2, "1100" $$ ! "1011",
     (fun h => (false, None) %% pair_t bool_t (option_t half_t))}} :::
    {{3, "1100" $$ "1010" $$ halfword,
     (fun h => (false, Some h) %% pair_t bool_t (option_t half_t))}} :::
    ast_env_nil.
  Hint Unfold RET_env : env_unfold_db.

  Definition RET_b : wf_bigrammar (pair_t bool_t (option_t half_t)).
    gen_ast_defs RET_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u => 
                    match u with
                      | (true, None) => inv_case_some case0 ()
                      | (true, Some h) => inv_case_some case1 h
                      | (false, None) => inv_case_some case2 ()
                      | (false, Some h) => inv_case_some case3 h
                    end)
               & _); ins_invertible_tac.
  Defined.

  Definition ROL_b := rotate_b "000".
  Definition ROR_b := rotate_b "001".
  Definition RSM_b := "0000" $$ "1111" $$ "1010" $$ ! "1010".
  Definition SAHF_b := "1001" $$ ! "1110".
  Definition SAR_b := rotate_b "111".
  Definition SCAS_b := "1010" $$ "111" $$ anybit.

  (* Intel manual says the reg field in modrm_ret_reg must be 000; however, it
     seems that an x86 processor accepts any combination in the reg field *)
  Definition SETcc_b : wf_bigrammar (pair_t condition_t operand_t).
    refine("0000" $$ "1111" $$ "1001" $$ tttn $ modrm_ret_reg
             @ (fun v => (fst v, snd (snd v)) %% pair_t condition_t operand_t)
             & (fun u:condition_type*operand => 
                  let (ct,op):=u in
                  match op with
                    | Reg_op _ | Address_op _ =>
                      (* alternate encoding: the reg can be any register *)
                      Some (fst u, (EAX, snd u))
                    | _ => None
                  end)
             & _); ins_invertible_tac.
  Defined.

  Definition SGDT_b := "0000" $$ "1111" $$ "0000" $$ "0001"
                              $$ ext_op_modrm_noreg "000".
  Definition SHL_b := rotate_b "100".

  Definition shiftdouble_env (opcode:string) : 
    AST_Env (pair_t operand_t (pair_t register_t reg_or_immed_t)) :=
    {{0, "0000" $$ "1111" $$ "1010" $$ opcode $$ "00" $$ "11" $$ reg $ reg $ byte,
     (fun v => match v with | (r2,(r1,b)) => (Reg_op r1, (r2, Imm_ri b)) end
                 %% pair_t operand_t (pair_t register_t reg_or_immed_t))}} :::
    {{1, "0000" $$ "1111" $$ "1010" $$ opcode $$ "00" $$ modrm_noreg $ byte,
     (fun v => match v with
                 | ((r,addr), b) => (Address_op addr, (r, Imm_ri b)) end
                 %% pair_t operand_t (pair_t register_t reg_or_immed_t))}} :::
    {{2, "0000" $$ "1111" $$ "1010" $$ opcode $$ "01" $$ "11" $$ reg $ reg,
    (fun v => match v with | (r2,r1) => (Reg_op r1, (r2, Reg_ri ECX)) end
                 %% pair_t operand_t (pair_t register_t reg_or_immed_t))}} :::
    {{3, "0000" $$ "1111" $$ "1010" $$ opcode $$ "01" $$ modrm_noreg,
    (fun v => match v with
                | (r,addr) => (Address_op addr, (r, Reg_ri ECX)) end
                 %% pair_t operand_t (pair_t register_t reg_or_immed_t))}} :::
    ast_env_nil.
  Hint Unfold shiftdouble_env : env_unfold_db.

  Definition shiftdouble_b (opcode:string) :
    wf_bigrammar (pair_t operand_t (pair_t register_t reg_or_immed_t)).
    intros; gen_ast_defs (shiftdouble_env opcode).
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u:[|pair_t operand_t (pair_t register_t reg_or_immed_t)|] => 
                    let (op1,u1):=u in
                    let (r2,ri):=u1 in
                    match op1 with
                      | Reg_op r1 => 
                        match ri with
                          | Imm_ri b => inv_case_some case0 (r2,(r1,b))
                          | Reg_ri ECX => inv_case_some case2 (r2,r1)
                          | _ => None
                        end
                      | Address_op addr =>
                        match ri with
                          | Imm_ri b => inv_case_some case1 ((r2,addr),b)
                          | Reg_ri ECX => inv_case_some case3 (r2,addr)
                          | _ => None
                        end
                      | _ => None
                    end)
               & _); ins_invertible_tac.
    - destruct w as [op [r2 ri]]. 
      destruct op; destruct ri as [r3 | addr]; try parsable_tac;
      destruct r3; parsable_tac.
  Defined.
        
  Definition SHLD_b := shiftdouble_b "01".
  Definition SHR_b := rotate_b "101".
  Definition SHRD_b := shiftdouble_b "11".

  Definition SIDT_b := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg "001".
  Definition SLDT_b := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "000".
  Definition SMSW_b := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm "100".
  Definition STC_b := "1111" $$ ! "1001".
  Definition STD_b := "1111" $$ ! "1101".
  Definition STI_b := "1111" $$ ! "1011".
  Definition STOS_b := "1010" $$ "101" $$ anybit.
  Definition STR_b := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "001".

  Definition TEST_env (opsize_override:bool) : 
    AST_Env (pair_t bool_t (pair_t operand_t operand_t)) :=
    {{0, "1111" $$ "0111" $$ ext_op_modrm "000" $ imm_b opsize_override,
     (fun v => (true, (fst v, Imm_op (snd v)))
                 %% pair_t bool_t (pair_t operand_t operand_t))}} :::
    {{1, "1111" $$ "0110" $$ ext_op_modrm "000" $ byte,
     (fun v => (false, (fst v, Imm_op (zero_extend8_32 (snd v))))
                 %% pair_t bool_t (pair_t operand_t operand_t))}} :::
    {{2, "1000" $$ "010" $$ anybit $ modrm_ret_reg,
     (fun v => 
        match v with
          | (w,(r1,op2)) => (w, (Reg_op r1, op2))
        end %% pair_t bool_t (pair_t operand_t operand_t))}} :::
    {{3, "1010" $$ "1001" $$ imm_b opsize_override,
     (fun v => (true, (Imm_op v, Reg_op EAX))
                 %% pair_t bool_t (pair_t operand_t operand_t))}} :::
    {{4, "1010" $$ "1000" $$ byte,
     (fun b => (false, (Reg_op EAX, Imm_op (zero_extend8_32 b)))
                 %% pair_t bool_t (pair_t operand_t operand_t))}} :::
    ast_env_nil.
  Hint Unfold TEST_env : env_unfold_db.

  Definition TEST_b (opsize_override: bool) : 
    wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    intros; gen_ast_defs (TEST_env opsize_override).
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u:[|pair_t bool_t (pair_t operand_t operand_t)|] => 
                    let (w,u1) := u in
                    let (op1,op2):=u1 in
                    match op2 with
                      | Imm_op imm =>
                        match op1 with
                          | Reg_op _ | Address_op _ => 
                            if w then 
                              inv_case_some case0 (op1, imm)
                            else
                              if repr_in_unsigned_byte_dec imm then
                                (* alternate encoding: case4 when op1 is EAX
                                   and imm within a byte *)
                                inv_case_some case1 (op1, zero_shrink32_8 imm)
                              else None
                          | _ => None
                        end
                      | Reg_op r2 =>
                        match op1 with
                          | Reg_op r1 => inv_case_some case2 (w, (r1, op2))
                          | Imm_op i => 
                            if (register_eq_dec r2 EAX) then
                              if w then inv_case_some case3 i
                              else None
                            else None
                          | _ => None
                        end
                      | Address_op _ =>
                        match op1 with
                          | Reg_op r1 => inv_case_some case2 (w, (r1, op2))
                          | _ => None
                        end
                      | _ => None
                    end)
               & _); ast_invertible_tac.
    - abstract (destruct_all; ins_printable_tac).
    - abstract 
        (destruct w as [b [op1 op2]]; destruct op2; destruct op1; destruct b;
         ins_pf_sim; parsable_tac).
  Defined.

  Definition UD2_b := "0000" $$ "1111" $$ "0000" $$ ! "1011".
  Definition VERR_b := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "100".
  Definition VERW_b := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "101".
  Definition WBINVD_b := "0000" $$ "1111" $$ "0000" $$ ! "1001".
  Definition WRMSR_b := "0000" $$ "1111" $$ "0011" $$ ! "0000".

  Definition XADD_b : 
    wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    refine("0000" $$ "1111" $$ "1100" $$ "000" $$ anybit $ modrm
            @ (fun v => 
                 match v with | (w,(op1,op2)) => (w, (op2, op1))
                 end %% pair_t bool_t (pair_t operand_t operand_t))
            & (fun u =>
                 match u with | (w,(op2,op1)) => Some (w, (op1, op2))
                 end)
            & _); invertible_tac.
  Defined.

  Definition XCHG_b : 
    wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    refine (("1000" $$ "011" $$ anybit $ modrm_ret_reg |+|
             "1001" $$ "0" $$ reg)
              @ (fun v => 
                   match v with
                     | inl (w,(r1,op2)) => (w, (op2, Reg_op r1))
                     | inr r1 => (true, (Reg_op EAX, Reg_op r1))
                   end %% pair_t bool_t (pair_t operand_t operand_t))
              & (fun u:[|pair_t bool_t (pair_t operand_t operand_t)|] => 
                   let (w,u1):=u in
                   let (op2,op1):=u1 in
                   match op2 with
                     | Reg_op r2 =>
                       match op1 with
                         | Reg_op r1 =>
                           if (register_eq_dec r2 EAX) then
                             if w then Some (inr r1)
                             else Some (inl (w,(r1,op2)))
                           else Some (inl (w,(r1,op2)))
                         | _ => None
                       end
                     | Address_op addr =>
                       match op1 with
                         | Reg_op r1 => Some (inl (w,(r1,op2)))
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); ins_invertible_tac.
    - destruct_sum.
      + destruct v as [w [r1 op2]]; ins_pf_sim; bg_pf_sim;
        destruct w; printable_tac; ins_ibr_sim.
      + ins_printable_tac.
  Defined.

  Definition XLAT_b := "1101" $$ ! "0111".

  (** ** Defs used in grammars for floating-point instructions *)

  Local Ltac fp_destruct_var v := 
    match goal with
      | [ H: match v with | FPS_op _ => _ | FPM16_op _ => _ | FPM32_op _ => _
                       | FPM64_op _ => _ | FPM80_op _ => _ end
             = _ |- _ ] =>
        destruct v
      | _ => ins_destruct_var v
    end.

  Local Ltac fp_parsable_tac := parsable_tac_gen ins_pf_sim fp_destruct_var.
  Local Ltac fp_invertible_tac := 
    invertible_tac_gen unfold_invertible_ast ins_pf_sim fp_destruct_var.

  Definition fpu_reg_op_b : wf_bigrammar fp_operand_t.
    refine (fpu_reg @ (fun v => FPS_op v %% fp_operand_t)
                    & (fun u => match u with | FPS_op v => Some v | _ => None end)
                    & _); fp_invertible_tac.
  Defined.

  Definition ext_op_modrm_FPM32_noreg (bs:string) : wf_bigrammar fp_operand_t.
    intros.
    refine ((ext_op_modrm_noreg_ret_addr bs)
              @ (fun v => FPM32_op v %% fp_operand_t)
              & (fun u => match u with | FPM32_op v => Some v | _ => None end)
                    & _); fp_invertible_tac.
  Defined.

  Definition ext_op_modrm_FPM64_noreg (bs:string) : wf_bigrammar fp_operand_t.
    intros.
    refine ((ext_op_modrm_noreg_ret_addr bs)
              @ (fun v => FPM64_op v %% fp_operand_t)
              & (fun u => match u with | FPM64_op v => Some v | _ => None end)
                    & _); fp_invertible_tac.
  Defined.
  
  Definition fp_condition_type_to_Z (ct: fp_condition_type) : Z :=
    (match ct with
      | B_fct => 0
      | E_fct => 1
      | BE_fct => 2
      | U_fct => 3
      | NB_fct => 4
      | NE_fct => 5
      | NBE_fct => 6
      | NU_fct => 7
     end)%Z.

  Lemma fp_condition_type_to_Z_inv z:
    (0 <= z < 8)%Z -> 
    fp_condition_type_to_Z (Z_to_fp_condition_type z) = z.
  Proof. intros.
    remember (Z_to_fp_condition_type z) as ct;
    destruct ct; unfold Z_to_fp_condition_type in *;
    toztac;
    simpl in *; pos_to_Z; omega.
  Qed.

  Lemma Z_to_fp_condition_type_inv ct :
    Z_to_fp_condition_type (fp_condition_type_to_Z ct) = ct.
  Proof. destruct ct; crush. Qed.

  Hint Rewrite fp_condition_type_to_Z_inv
       using (apply int_of_bitsn_range): inv_db.
  Hint Rewrite Z_to_fp_condition_type_inv: inv_db.

  (** ** Grammars for floating-point instructions, based on tables B.17 and B-39*)
  Definition F2XM1_b := "11011" $$ "001111" $$ ! "10000".
  Definition FABS_b :=  "11011" $$ "001111" $$ ! "00001".

  Definition fp_arith_env (bs0 bs1: string) :
    AST_Env (pair_t bool_t fp_operand_t) :=
    {{0, "11011" $$ "000" $$ ext_op_modrm_noreg_ret_addr bs0,
     (fun addr => (true, FPM32_op addr) %% pair_t bool_t fp_operand_t)}} :::
    {{1, "11011" $$ "100" $$ ext_op_modrm_noreg_ret_addr bs0,
     (fun addr => (true, FPM64_op addr) %% pair_t bool_t fp_operand_t)}} :::
    {{2, "11011" $$ "0" $$ "0011" $$ bs0 $$ fpu_reg,
     (fun fr => (true, FPS_op fr) %% pair_t bool_t fp_operand_t)}} :::
    {{3, "11011" $$ "1" $$ "0011" $$ bs1 $$ fpu_reg,
     (fun fr => (false, FPS_op fr) %% pair_t bool_t fp_operand_t)}} :::
    ast_env_nil.
  Hint Unfold fp_arith_env : env_unfold_db.

  Definition fp_arith_b (bs0 bs1: string) : 
    wf_bigrammar (pair_t bool_t fp_operand_t).
    intros; gen_ast_defs (fp_arith_env bs0 bs1).
    refine ((comb_bigrammar gt) @ (comb_map gt)
              & (fun u =>
                   match u with
                     | (true, FPM32_op addr) => inv_case_some case0 addr
                     | (true, FPM64_op addr) => inv_case_some case1 addr
                     | (true, FPS_op fr) => inv_case_some case2 fr
                     | (false, FPS_op fr) => inv_case_some case3 fr
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FADD_b := fp_arith_b "000" "000".

  (* Possible todos: FADDP allows a fpu reg as an operand; can change the
     syntax of FADDP to take a fpureg as the argument, instead of
     fpu_operand; the same applies to many FPU instructions *)
  Definition FADDP_b := "11011" $$ "110" $$ "11000" $$ fpu_reg_op_b.

  Definition FBLD_b := "11011" $$ "111" $$ ext_op_modrm_FPM64_noreg "100".
  Definition FBSTP_b := "11011" $$ "111" $$ ext_op_modrm_FPM64_noreg "110".
  Definition FCHS_b := "11011" $$ "001111" $$ ! "00000".

  Definition FCMOVcc_b : 
    wf_bigrammar (pair_t fp_condition_t fp_operand_t).
    refine (("11011" $$ "01" $$ anybit $ "110" $$ anybit $ anybit $ fpu_reg_op_b)
              @ (fun v => 
                   match v with 
                       (b2, (b1, (b0, op))) => 
                       let n := int_of_bitsn 3 (b2, (b1, (b0, tt))) in
                       (Z_to_fp_condition_type n, op)
                   end %% pair_t fp_condition_t fp_operand_t)
              & (fun u:[|pair_t fp_condition_t fp_operand_t|] =>
                   let (ct,op) := u in
                   let bs :=
                       bitsn_of_int 3 (fp_condition_type_to_Z ct)
                   in
                   match bs with
                     | Some (b2,(b1,(b0,()))) => Some (b2,(b1,(b0,op)))
                     | None => None (* impossible case *)
                   end)
              & _); ast_invertible_tac.
    - repeat (ibr_sim || destruct_pr_var);
      autorewrite with inv_db;
      printable_tac.
    - destruct w as [ct op].
      remember_rev (bitsn_of_int 3 (fp_condition_type_to_Z ct)) as u.
      destruct u as [[b2 [b1 [b0 b]]] | ]; try parsable_tac.
      destruct b. sim.
      erewrite int_of_bitsn_inv by eassumption.
      autorewrite with inv_db. trivial.
  Defined.

  Definition FCOM_b: wf_bigrammar fp_operand_t.
    refine (("11011" $$ "000" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "100" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "000" $$ "11010" $$ fpu_reg) 
              @ (fun v => 
                   match v with
                     | inl addr => FPM32_op addr
                     | inr (inl addr) => FPM64_op addr
                     | inr (inr fr) => FPS_op fr
                   end %% fp_operand_t)
              & (fun u => 
                   match u with
                     | FPS_op fr => Some (inr (inr fr))
                     | FPM32_op addr => Some (inl addr)
                     | FPM64_op addr => Some (inr (inl addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FCOMP_b : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "000" $$ ext_op_modrm_noreg_ret_addr "011" |+|
             "11011" $$ "100" $$ ext_op_modrm_noreg_ret_addr "011" |+|
             "11011" $$ "000" $$ "11011" $$ fpu_reg)
              @ (fun v => 
                   match v with
                     | inl addr => FPM32_op addr
                     | inr (inl addr) => FPM64_op addr
                     | inr (inr fr) => FPS_op fr
                   end %% fp_operand_t)
              & (fun u => 
                   match u with
                     | FPS_op fr => Some (inr (inr fr))
                     | FPM32_op addr => Some (inl addr)
                     | FPM64_op addr => Some (inr (inl addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FCOMPP_b := "11011" $$ "110" $$ "11011" $$ ! "001".
  Definition FCOMIP_b := "11011" $$ "111" $$ "11110" $$ fpu_reg_op_b. 
  Definition FCOS_b := "11011" $$ "001" $$ "111" $$ ! "11111".
  Definition FDECSTP_b := "11011" $$ "001" $$ "111" $$ ! "10110".

  Definition FDIV_b := fp_arith_b "110" "111".
  Definition FDIVP_b := "11011" $$ "110" $$ "11111" $$ fpu_reg_op_b.
  Definition FDIVR_b := fp_arith_b "111" "110".
  Definition FDIVRP_b := "11011" $$ "110" $$ "11110" $$ fpu_reg_op_b.
  Definition FFREE_b := "11011" $$ "101" $$ "11000" $$ fpu_reg_op_b.

  (* floating-point arith involving an integer as one of the operands *)
  Definition fp_iarith_b (bs: string) : wf_bigrammar fp_operand_t.
    intros.
    refine (("11011" $$ "110" $$ ext_op_modrm_noreg_ret_addr bs |+|
             "11011" $$ "010" $$ ext_op_modrm_noreg_ret_addr bs)
              @ (fun v => 
                   match v with
                     | inl addr => FPM16_op addr
                     | inr addr => FPM32_op addr
                   end %% fp_operand_t)
              & (fun u =>
                   match u with
                     | FPM16_op addr => Some (inl addr)
                     | FPM32_op addr => Some (inr addr)
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FIADD_b := fp_iarith_b "000".
  Definition FICOM_b  := fp_iarith_b "010".
  Definition FICOMP_b  := fp_iarith_b "011".
  Definition FIDIV_b  := fp_iarith_b "110".
  Definition FIDIVR_b  := fp_iarith_b "111".

  Definition FILD_b : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "000" |+|
             "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "000" |+|
             "11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "101")
              @ (fun v =>
                   match v with
                     | inl addr => FPM16_op addr
                     | inr (inl addr) => FPM32_op addr
                     | inr (inr addr) => FPM64_op addr
                   end %% fp_operand_t)
              & (fun u => 
                   match u with
                     | FPM16_op addr => Some (inl addr)
                     | FPM32_op addr => Some (inr (inl addr))
                     | FPM64_op addr => Some (inr (inr addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FIMUL_b := fp_iarith_b "001".
  Definition FINCSTP_b := "11011" $$ "001111" $$ ! "10111".

  Definition FIST_b : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "010")
              @ (fun v => 
                   match v with
                     | inl addr => FPM16_op addr
                     | inr addr => FPM32_op addr
                   end %% fp_operand_t)
              & (fun u =>
                   match u with
                     | FPM16_op addr => Some (inl addr)
                     | FPM32_op addr => Some (inr addr)
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FISTP_b : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "011" |+|
             "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "011" |+|
             "11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "111")
              @ (fun v =>
                   match v with
                     | inl addr => FPM16_op addr
                     | inr (inl addr) => FPM32_op addr
                     | inr (inr addr) => FPM64_op addr
                   end %% fp_operand_t)
              & (fun u => 
                   match u with
                     | FPM16_op addr => Some (inl addr)
                     | FPM32_op addr => Some (inr (inl addr))
                     | FPM64_op addr => Some (inr (inr addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FISUB_b := fp_iarith_b "100".
  Definition FISUBR_b := fp_iarith_b "101".

  Definition FLD_env : AST_Env fp_operand_t :=
    {{0, "11011" $$ "001" $$ ext_op_modrm_noreg_ret_addr "000",
     (fun addr => FPM32_op addr %% fp_operand_t)}} :::
    {{1, "11011" $$ "101" $$ ext_op_modrm_noreg_ret_addr "000",
     (fun addr => FPM64_op addr %% fp_operand_t)}} :::
    {{2, "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "101",
     (fun addr => FPM80_op addr %% fp_operand_t)}} :::
    {{3, "11011" $$ "001" $$ "11000" $$ fpu_reg,
     (fun fr => FPS_op fr %% fp_operand_t)}} :::
    ast_env_nil.
  Hint Unfold FLD_env : env_unfold_db.

  Definition FLD_b: wf_bigrammar fp_operand_t.
    gen_ast_defs FLD_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | FPM32_op addr => inv_case_some case0 addr
                      | FPM64_op addr => inv_case_some case1 addr
                      | FPM80_op addr => inv_case_some case2 addr
                      | FPS_op fr => inv_case_some case3 fr
                      | _ => None
                    end)
               & _); fp_invertible_tac.
  Defined.

  Definition FLD1_b := "11011" $$ "001111" $$ ! "01000".
  Definition FLDCW_b := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "101".

  Definition FLDENV_b := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "100". 
  Definition FLDL2E_b := "11011" $$ "001111" $$ ! "01010".
  Definition FLDL2T_b := "11011" $$ "001111" $$ ! "01001".
  Definition FLDLG2_b := "11011" $$ "001111" $$ ! "01100".
  Definition FLDLN2_b := "11011" $$ "001111" $$ ! "01101". 
  Definition FLDPI_b := "11011" $$ "001111" $$ ! "01011".
  Definition FLDZ_b := "11011" $$ "001111" $$ ! "01110".

  Definition FMUL_b := fp_arith_b "001" "001".

  Definition FMULP_b := "11011" $$ "110" $$ "11001" $$ fpu_reg_op_b. 
  Definition FNCLEX_b := "11011" $$ "011111" $$ ! "00010".
  Definition FNINIT_b := "11011" $$ "011111" $$ ! "00011".
  Definition FNOP_b := "11011" $$ "001110" $$ ! "10000".
  Definition FNSAVE_b := "11011101" $$ ext_op_modrm_FPM64_noreg "110".
  Definition FNSTCW_b := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "111".

  Definition FNSTSW_b : wf_bigrammar (option_t fp_operand_t).
    refine (("11011" $$ "111" $$ "111" $$ ! "00000" |+|
             "11011" $$ "101" $$ ext_op_modrm_FPM32_noreg "111")
              @ (fun v =>
                   match v with
                     | inl () => None
                     | inr op => Some op
                   end %% option_t fp_operand_t)
              & (fun u:[|option_t fp_operand_t|] =>
                   match u with
                     | Some op => Some (inr op)
                     | None => Some (inl ())
                   end)
              & _); invertible_tac.
  Defined.

  Definition FPATAN_b := "11011" $$ "001111" $$ ! "10011".
  Definition FPREM_b := "11011" $$ "001111" $$ ! "11000".
  Definition FPREM1_b := "11011" $$ "001111" $$ ! "10101".
  Definition FPTAN_b := "11011" $$ "001111" $$ ! "10010".
  Definition FRNDINT_b := "11011" $$ "001111" $$ ! "11100".

  Definition FRSTOR_b := "11011" $$ "101" $$ ext_op_modrm_FPM32_noreg "100".

  Definition FSCALE_b := "11011" $$ "001111" $$ ! "11101".
  Definition FSIN_b := "11011" $$ "001111" $$ ! "11110".
  Definition FSINCOS_b := "11011" $$ "001111" $$ ! "11011".
  Definition FSQRT_b := "11011" $$ "001111" $$ ! "11010".

  Definition FST_b : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "001" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "101" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "101" $$ "11010" $$ fpu_reg)
              @ (fun v =>
                   match v with
                     | inl addr => FPM32_op addr
                     | inr (inl addr) => FPM64_op addr
                     | inr (inr fr) => FPS_op fr
                   end %% fp_operand_t)
              & (fun u =>
                   match u with
                     | FPS_op fr => Some (inr (inr fr))
                     | FPM32_op addr => Some (inl addr)
                     | FPM64_op addr => Some (inr (inl addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  (* FSTCW's encoding is the same as FWAIT followed by FNSTCW *)
  (* Definition FSTCW_b := "10011011" $$ "11011" $$ "001" $$ ext_op_modrm_FPM32 "111". *)
  Definition FSTENV_b := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "110".

  Definition FSTP_env : AST_Env fp_operand_t :=
    {{0, "11011" $$ "001" $$ ext_op_modrm_noreg_ret_addr "011",
     (fun addr => FPM32_op addr %% fp_operand_t)}} :::
    {{1, "11011" $$ "101" $$ ext_op_modrm_noreg_ret_addr "011",
     (fun addr => FPM64_op addr %% fp_operand_t)}} :::
    {{2, "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "111",
     (fun addr => FPM80_op addr %% fp_operand_t)}} :::
    {{3, "11011" $$ "101" $$ "11011" $$ fpu_reg,
     (fun fr => FPS_op fr %% fp_operand_t)}} :::
    ast_env_nil.
  Hint Unfold FSTP_env : env_unfold_db.

  Definition FSTP_b: wf_bigrammar fp_operand_t.
    gen_ast_defs FSTP_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | FPM32_op addr => inv_case_some case0 addr
                      | FPM64_op addr => inv_case_some case1 addr
                      | FPM80_op addr => inv_case_some case2 addr
                      | FPS_op fr => inv_case_some case3 fr
                      | _ => None
                    end)
               & _); fp_invertible_tac.
  Defined.

  Definition FSUB_b := fp_arith_b "100" "101".
  Definition FSUBP_b := "11011" $$ "110" $$ "11101" $$ fpu_reg_op_b. 
  Definition FSUBR_b := fp_arith_b "101" "100".

  Definition FSUBRP_b := "11011" $$ "110" $$ "11100" $$ fpu_reg_op_b. 
  Definition FTST_b := "11011" $$ "001111" $$ ! "00100".
  Definition FUCOM_b := "11011" $$ "101" $$ "11100" $$ fpu_reg_op_b. 
  Definition FUCOMP_b := "11011" $$ "101" $$ "11101" $$ fpu_reg_op_b. 
  Definition FUCOMPP_b := "11011" $$ "010111" $$ ! "01001".
  Definition FUCOMI_b := "11011" $$ "011" $$ "11101" $$ fpu_reg_op_b. 
  Definition FUCOMIP_b := "11011" $$ "111" $$ "11101" $$ fpu_reg_op_b.
  Definition FXAM_b := "11011" $$ "001111" $$ ! "00101".
  Definition FXCH_b := "11011" $$ "001" $$ "11001" $$ fpu_reg_op_b.

  Definition FXTRACT_b := "11011" $$ "001" $$ "1111" $$ ! "0100".
  Definition FYL2X_b := "11011" $$ "001111" $$ ! "10001".
  Definition FYL2XP1_b := "11011" $$ "001111" $$ ! "11001".
  Definition FWAIT_b := ! "10011011".

  (** ** Definitions used in bigrammars for MMX instructions *)

  Local Ltac mmx_destruct_var v := 
    match goal with
      | [ H: match v with | GP_Reg_op _ => _ | MMX_Addr_op _ => _
                       | MMX_Reg_op _ => _ | MMX_Imm_op _ => _ end
             = _ |- _ ] =>
        destruct v
      | [ H: match v with | MMX_8 => _ | MMX_16 => _
                       | MMX_32 => _ | MMX_64 => _ end
             = _ |- _ ] =>
        destruct v
      | _ => ins_destruct_var v
    end.

  Local Ltac mmx_parsable_tac := 
    parsable_tac_gen ins_pf_sim mmx_destruct_var.

  Definition MMX_Reg_op_b: wf_bigrammar mmx_operand_t.
    refine (mmx_reg @ (fun r => MMX_Reg_op r : interp mmx_operand_t)
                    & (fun op => match op with 
                                   | MMX_Reg_op r => Some r
                                   | _ => None
                                 end)
                    & _); ins_invertible_tac; mmx_parsable_tac.
  Defined.

  Definition modrm_mmx_noreg : wf_bigrammar (pair_t mmx_register_t address_t) := 
    modrm_gen_noreg mmx_reg.

  Definition modrm_mmx_ret_reg : wf_bigrammar (pair_t mmx_register_t mmx_operand_t).
    refine ((modrm_gen mmx_reg)
            @ (fun v =>
                 match v with
                   | inl (r, addr) => (r, MMX_Addr_op addr)
                   | inr (r1, r2) => (r1, MMX_Reg_op r2)
                 end %% (pair_t mmx_register_t mmx_operand_t))
            & (fun u =>
                 match u with
                   | (r, MMX_Addr_op addr) => Some (inl (r, addr))
                   | (r1, MMX_Reg_op r2) => Some (inr (r1, r2))
                   | _ => None
                 end)
            & _); invertible_tac.
    - destruct_all; printable_tac.
    - mmx_parsable_tac.
  Defined.

  Definition modrm_mmx : wf_bigrammar (pair_t mmx_operand_t mmx_operand_t).
    refine (modrm_mmx_ret_reg
              @ (fun v => match v with
                            | (r1, op2) => (MMX_Reg_op r1, op2)
                          end %% (pair_t mmx_operand_t mmx_operand_t))
              & (fun u => match u with
                            | (MMX_Reg_op r1, op2) => Some (r1, op2)
                            | _ => None
                          end)
              & _); invertible_tac; mmx_parsable_tac.
  Defined.

  (* grammar for the mmx granularity bits, allowing 8, 16, 32 bits. *)
  Definition mmx_gg_b_8_16_32 : wf_bigrammar mmx_granularity_t.
    refine ((! "00" |+| ! "01" |+| ! "10")
              @ (fun v => 
                   match v with
                     | inl () => MMX_8
                     | inr (inl ()) => MMX_16
                     | inr (inr ()) => MMX_32
                   end %% mmx_granularity_t)
              & (fun u => 
                   match u with
                     | MMX_8 => Some (inl ())
                     | MMX_16 => Some (inr (inl ()))
                     | MMX_32 => Some (inr (inr ()))
                     | _ => None
                   end)
              & _); ins_invertible_tac; mmx_parsable_tac.
  Defined.

  Definition mmx_gg_b_8_16 : wf_bigrammar mmx_granularity_t.
    refine ((! "00" |+| ! "01")
              @ (fun v => 
                   match v with
                     | inl () => MMX_8
                     | inr () => MMX_16
                   end %% mmx_granularity_t)
              & (fun u => 
                   match u with
                     | MMX_8 => Some (inl ())
                     | MMX_16 => Some (inr ())
                     | _ => None
                   end)
              & _); ins_invertible_tac; mmx_parsable_tac.
  Defined.

  Definition mmx_gg_b_16_32_64 : wf_bigrammar mmx_granularity_t.
    refine ((! "01" |+| ! "10" |+| ! "11")
              @ (fun v => 
                   match v with
                     | inl () => MMX_16
                     | inr (inl ()) => MMX_32
                     | inr (inr ()) => MMX_64
                   end %% mmx_granularity_t)
              & (fun u => 
                   match u with
                     | MMX_16 => Some (inl ())
                     | MMX_32 => Some (inr (inl ()))
                     | MMX_64 => Some (inr (inr ()))
                     | _ => None
                   end)
              & _); ins_invertible_tac; mmx_parsable_tac.
  Defined.

  Definition mmx_gg_b_16_32 : wf_bigrammar mmx_granularity_t.
    refine ((! "01" |+| ! "10")
              @ (fun v => 
                   match v with
                     | inl () => MMX_16
                     | inr () => MMX_32
                   end %% mmx_granularity_t)
              & (fun u => 
                   match u with
                     | MMX_16 => Some (inl ())
                     | MMX_32 => Some (inr ())
                     | _ => None
                   end)
              & _); ins_invertible_tac; mmx_parsable_tac.
  Defined.

  Lemma mmx_reg_rng: forall mr, in_bigrammar_rng (` mmx_reg) mr.
  Proof. intros; unfold mmx_reg.  apply field_intn_rng. Qed.
  Hint Resolve mmx_reg_rng: ibr_rng_db.

  Lemma modrm_mmx_ret_reg_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mmx_ret_reg) (mr1, MMX_Reg_op mr2).
  Proof. intros. unfold modrm_mmx_ret_reg, modrm_gen. ins_ibr_sim. compute [fst].
    exists (inr [|pair_t mmx_register_t address_t|] (mr1, mr2)).
    split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_mmx_ret_reg_rng1: ibr_rng_db.

  Lemma modrm_mmx_ret_reg_rng_inv mr op:
    in_bigrammar_rng (` modrm_mmx_ret_reg) (mr,op) -> 
    (exists mr, op = MMX_Reg_op mr) \/ (exists addr, op = MMX_Addr_op addr).
  Proof. unfold modrm_mmx_ret_reg; intros. ins_ibr_sim.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_mmx_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mmx) (MMX_Reg_op mr1, MMX_Reg_op mr2).
  Proof. unfold modrm_mmx; intros; ins_ibr_sim. compute [fst].
     exists (mr1, MMX_Reg_op mr2); split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_mmx_rng1: ibr_rng_db.

  Lemma modrm_mmx_rng_inv1 op1 op2: 
    in_bigrammar_rng (` modrm_mmx) (op1,op2) -> exists mr, op1 = MMX_Reg_op mr.
  Proof. unfold modrm_mmx; intros; ins_ibr_sim.
    destruct v as [mr op]. exists mr; congruence.
  Qed.

  Lemma modrm_mmx_rng_inv2 op1 op2: 
    in_bigrammar_rng (` modrm_mmx) (op1,op2) -> 
    (exists mr, op2 = MMX_Reg_op mr) \/ (exists addr, op2 = MMX_Addr_op addr).
  Proof. unfold modrm_mmx; intros; ins_ibr_sim.
    destruct v as [mr op]. eapply modrm_mmx_ret_reg_rng_inv.
    sim; subst. eassumption.
  Qed.

  Local Ltac mmx_pf_sim :=
    ins_ibr_sim; bg_pf_sim;
    repeat match goal with
      | [H: in_bigrammar_rng (` modrm_mmx) (?op1 ?op2) |- _] => 
        let H2 := fresh "H" in
        let H3 := fresh "H" in
        generalize (modrm_mmx_rng_inv1 H) (modrm_mmx_rng_inv2 H); intros H2 H3;
        destruct H2; subst;
        destruct H3 as [H3 | H3]; destruct H3; subst op2
      | [H: in_bigrammar_rng (` modrm_mmx_ret_reg) (?r1 ?op2) |- _] =>
        let H2 := fresh "H" in
        generalize (modrm_mmx_ret_reg_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op2
    end.

  Local Ltac mmx_invertible_tac := 
    invertible_tac_gen unfold_invertible_ast mmx_pf_sim mmx_destruct_var.

  (** ** Bigrammars for MMX instructions *)

  Definition EMMS_b := "0000" $$ "1111" $$ "0111" $$ ! "0111".

  Definition MOVD_env : AST_Env (pair_t mmx_operand_t mmx_operand_t) :=
    (* gpreg to and from mmxreg *)
    {{0, "0000" $$ "1111" $$ "011" $$ anybit $ "1110" $$ "11" $$ mmx_reg $ reg,
    (fun v => let (d,v1):=v in let (mr,r):=v1 in
              (if d then (MMX_Reg_op mr, GP_Reg_op r)
               else (GP_Reg_op r, MMX_Reg_op mr))
              %% pair_t mmx_operand_t mmx_operand_t) }} :::
    (* mem to and from mmxreg *)
    {{1, "0000" $$ "1111" $$ "011" $$ anybit $ "1110" $$ modrm_mmx_noreg,
     (fun v => let (d,v1):=v in let (mr,addr):=v1 in
               (if d then (MMX_Addr_op addr, MMX_Reg_op mr)
                else (MMX_Reg_op mr, MMX_Addr_op addr))
               %% pair_t mmx_operand_t mmx_operand_t) }} :::
    ast_env_nil.
  Hint Unfold MOVD_env : env_unfold_db.

  Definition MOVD_b : wf_bigrammar (pair_t mmx_operand_t mmx_operand_t).
    gen_ast_defs MOVD_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | (MMX_Reg_op mr, GP_Reg_op r) => inv_case_some case0 (true,(mr,r))
                      | (GP_Reg_op r, MMX_Reg_op mr) => inv_case_some case0 (false,(mr,r))
                      | (MMX_Addr_op addr, MMX_Reg_op mr) => inv_case_some case1 (true,(mr,addr))
                      | (MMX_Reg_op mr, MMX_Addr_op addr) => inv_case_some case1 (false,(mr,addr))
                      | _ => None
                    end)
               & _); mmx_invertible_tac.
    - destruct_sum;
      destruct v as [d [mr r]]; destruct d; printable_tac; ins_ibr_sim.
  Defined.

  Definition MOVQ_b : wf_bigrammar (pair_t mmx_operand_t mmx_operand_t).
    refine (("0000" $$ "1111" $$ "011" $$ anybit $ "1111" $$ modrm_mmx)
             @ (fun v: [|pair_t char_t (pair_t mmx_operand_t mmx_operand_t)|] =>
                  let (d,v1):=v in let (op1,op2) :=v1 in
                    (if d then (op2, op1) else (op1, op2))
                      %% pair_t mmx_operand_t mmx_operand_t)
             & (fun u:[|pair_t mmx_operand_t mmx_operand_t|] =>
                  let (op1,op2):=u in
                  match op1 with
                    | MMX_Reg_op _ => 
                      (* alternate encoding: when op2 is also MMX_Reg_op *)
                      Some (false, (op1, op2))
                    | _ =>
                      match op2 with
                        | MMX_Reg_op _ => Some (true, (op2, op1))
                        | _ => None
                      end
                  end)
             & _); mmx_invertible_tac.
    - destruct v as [d [op1 op2]]; destruct d;
      mmx_pf_sim; printable_tac; ins_ibr_sim. 
  Defined.

  Definition PACKSSDW_b := 
    "0000" $$ "1111" $$ "0110" $$ "1011" $$ modrm_mmx.

  Definition PACKSSWB_b := 
    "0000" $$ "1111" $$ "0110" $$ "0011" $$ modrm_mmx.

  Definition PACKUSWB_b := 
    "0000" $$ "1111" $$ "0110" $$ "0111" $$ modrm_mmx.

  Definition PADD_b := 
    "0000" $$ "1111" $$ "1111" $$ "11" $$ mmx_gg_b_8_16_32 $ modrm_mmx. 

  Definition PADDS_b := 
    "0000" $$ "1111" $$ "1110" $$ "11" $$ mmx_gg_b_8_16 $ modrm_mmx.

  Definition PADDUS_b := 
    "0000" $$ "1111" $$ "1101" $$ "11" $$ mmx_gg_b_8_16 $ modrm_mmx. 

  Definition PAND_b := 
    "0000" $$ "1111" $$ "1101" $$ "1011" $$ modrm_mmx. 

  Definition PANDN_b := 
    "0000" $$ "1111" $$ "1101" $$ "1111" $$ modrm_mmx. 

  Definition PCMPEQ_b :=
    "0000" $$ "1111" $$ "0111" $$ "01" $$ mmx_gg_b_8_16_32 $ modrm_mmx.

  Definition PCMPGT_b := 
    "0000" $$ "1111" $$ "0110" $$ "01" $$ mmx_gg_b_8_16_32 $ modrm_mmx. 

  Definition PMADDWD_b := 
    "0000" $$ "1111" $$ "1111" $$ "0101" $$ modrm_mmx. 

  Definition PMULHUW_b := 
    "0000" $$ "1111" $$ "1110" $$ "0100" $$ modrm_mmx.

  Definition PMULHW_b := 
    "0000" $$ "1111" $$ "1110" $$ "0101" $$ modrm_mmx.

  Definition PMULLW_b := 
    "0000" $$ "1111" $$ "1101" $$ "0101" $$ modrm_mmx.

  Definition POR_b := 
    "0000" $$ "1111" $$ "1110" $$ "1011" $$ modrm_mmx.

  Definition pshift_b (bs:string) (gg_b:wf_bigrammar mmx_granularity_t) :
    wf_bigrammar (pair_t mmx_granularity_t
                         (pair_t mmx_operand_t mmx_operand_t)).
    intros.    
    refine (("0000" $$ "1111" $$ "11" $$ bs $$ "00"
                $$ gg_b $ modrm_mmx_ret_reg |+|
             "0000" $$ "1111" $$ "0111" $$ "00"
                $$ gg_b $ "11" $$ bs $$ "0" $$ mmx_reg $ byte)
              @ (fun v =>
                   match v with
                     | inl (gg,(r1,op2)) => (gg,(MMX_Reg_op r1, op2))
                     | inr (gg,(r1,imm)) => 
                       (gg, (MMX_Reg_op r1, MMX_Imm_op (zero_extend8_32 imm)))
                   end
                   %% pair_t mmx_granularity_t (pair_t mmx_operand_t mmx_operand_t))
              & (fun u: mmx_granularity * (mmx_operand * mmx_operand) => 
                   let (gg,u1):=u in
                   let (op1,op2):=u1 in
                   match op1 with
                     | MMX_Reg_op r1 =>
                       match op2 with
                         | MMX_Reg_op _ | MMX_Addr_op _ => Some (inl(gg,(r1,op2)))
                         | MMX_Imm_op imm => 
                           if (repr_in_unsigned_byte_dec imm) then
                               Some (inr(gg,(r1, zero_shrink32_8 imm)))
                           else None
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); mmx_invertible_tac.
  Defined.

  Definition PSLL_b := pshift_b "11" mmx_gg_b_16_32_64.
  Definition PSRA_b := pshift_b "10" mmx_gg_b_16_32.
  Definition PSRL_b := pshift_b "01" mmx_gg_b_16_32_64.

  Definition PSUB_b := 
    "0000" $$ "1111" $$ "1111" $$ "10" $$ mmx_gg_b_8_16_32 $ modrm_mmx. 

  Definition PSUBS_b := 
    "0000" $$ "1111" $$ "1110" $$ "10" $$ mmx_gg_b_8_16 $ modrm_mmx. 

  Definition PSUBUS_b := 
    "0000" $$ "1111" $$ "1101" $$ "10" $$ mmx_gg_b_8_16 $ modrm_mmx. 

  Definition PUNPCKH_b := 
    "0000" $$ "1111" $$ "0110" $$ "10" $$ mmx_gg_b_8_16_32 $ modrm_mmx. 

  Definition PUNPCKL_b := 
    "0000" $$ "1111" $$ "0110" $$ "00" $$ mmx_gg_b_8_16_32 $ modrm_mmx. 

  Definition PXOR_b := 
    "0000" $$ "1111" $$ "1110" $$ "1111" $$ modrm_mmx. 

  (** ** Bigrammars for SSE instructions *)

  Local Ltac sse_destruct_var v := 
    match goal with
      | [ H: match v with | SSE_XMM_Reg_op _ => _ | SSE_MM_Reg_op _ => _
                       | SSE_Addr_op _ => _ | SSE_GP_Reg_op _ => _
                       | SSE_Imm_op _ => _ end
             = _ |- _ ] =>
        destruct v
      | _ => ins_destruct_var v
    end.

  Local Ltac sse_parsable_tac := parsable_tac_gen ins_pf_sim sse_destruct_var.

  Definition SSE_XMM_Reg_op_b: wf_bigrammar sse_operand_t.
    refine (sse_reg @ (fun r => SSE_XMM_Reg_op r : interp sse_operand_t)
                    & (fun op => match op with
                                   | SSE_XMM_Reg_op r => Some r
                                   | _ => None
                                 end)
                    & _); invertible_tac; sse_parsable_tac.
  Defined.

  Definition SSE_GP_Reg_op_b: wf_bigrammar sse_operand_t.
    refine (reg @ (fun r => SSE_GP_Reg_op r : interp sse_operand_t)
                & (fun op => match op with
                               | SSE_GP_Reg_op r => Some r
                               | _ => None
                             end)
                & _); invertible_tac; sse_parsable_tac.
  Defined.

  Definition SSE_MM_Reg_op_b: wf_bigrammar sse_operand_t.
    refine (mmx_reg @ (fun r => SSE_MM_Reg_op r : interp sse_operand_t)
                & (fun op => match op with
                               | SSE_MM_Reg_op r => Some r
                               | _ => None
                             end)
                & _); invertible_tac; sse_parsable_tac.
  Defined.

  (* mod xmmreg r/m in manual*)
  Definition modrm_xmm_ret_reg : 
    wf_bigrammar (pair_t sse_register_t sse_operand_t).
    refine ((modrm_gen sse_reg)
            @ (fun v =>
                 match v with
                   | inl (r, addr) => (r, SSE_Addr_op addr)
                   | inr (r1, r2) => (r1, SSE_XMM_Reg_op r2)
                 end %% (pair_t sse_register_t sse_operand_t))
            & (fun u => 
                 match u with
                   | (r, SSE_Addr_op addr) => Some (inl (r, addr))
                   | (r1, SSE_XMM_Reg_op r2) => Some (inr (r1, r2))
                   | _ => None
                 end)
            & _); invertible_tac.
    - destruct_all; printable_tac.
    - sse_parsable_tac.
  Defined.

  Definition modrm_xmm : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine (modrm_xmm_ret_reg
              @ (fun v => match v with
                            | (sr1, op2) => (SSE_XMM_Reg_op sr1, op2)
                          end %% (pair_t sse_operand_t sse_operand_t))
              & (fun u => match u with
                            | (SSE_XMM_Reg_op sr1, op2) => Some (sr1, op2)
                            | _ => None
                          end)
              & _); invertible_tac; sse_parsable_tac.
  Defined.

  (* mod mmreg r/m (no x) in manual; this uses mmx regs in sse instrs *)
  Definition modrm_mm_ret_reg : wf_bigrammar (pair_t mmx_register_t sse_operand_t).
    refine ((modrm_gen mmx_reg)
            @ (fun v =>
                 match v with
                   | inl (r, addr) => (r, SSE_Addr_op addr)
                   | inr (r1, r2) => (r1, SSE_MM_Reg_op r2)
                 end %% (pair_t mmx_register_t sse_operand_t))
            & (fun u => 
                 match u with
                   | (r, SSE_Addr_op addr) => Some (inl (r, addr))
                   | (r1, SSE_MM_Reg_op r2) => Some (inr (r1, r2))
                   | _ => None
                 end)
            & _); invertible_tac.
    - destruct_all; printable_tac.
    - sse_parsable_tac.
  Defined.

  Definition modrm_mm : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine (modrm_mm_ret_reg
              @ (fun v => match v with
                            | (mr1, op2) => (SSE_MM_Reg_op mr1, op2)
                          end %% (pair_t sse_operand_t sse_operand_t))
              & (fun u => match u with
                            | (SSE_MM_Reg_op mr1, op2) => Some (mr1, op2)
                            | _ => None
                          end)
              & _); invertible_tac; sse_parsable_tac.
  Defined.

  Notation modrm_xmm_noreg := modrm_bv2_noreg.
  Notation modrm_mm_noreg := modrm_bv2_noreg.

  Lemma modrm_xmm_ret_reg_rng1 sr1 sr2: 
    in_bigrammar_rng (` modrm_xmm_ret_reg) (sr1, SSE_XMM_Reg_op sr2).
  Proof. intros. unfold modrm_xmm_ret_reg, modrm_gen. ins_ibr_sim. compute [fst].
    exists (inr [|pair_t sse_register_t address_t|] (sr1, sr2)).
    split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_xmm_ret_reg_rng1: ibr_rng_db.

  Lemma modrm_xmm_ret_reg_rng_inv sr op:
    in_bigrammar_rng (` modrm_xmm_ret_reg) (sr,op) -> 
    (exists sr, op = SSE_XMM_Reg_op sr) \/ (exists addr, op = SSE_Addr_op addr).
  Proof. unfold modrm_xmm_ret_reg; intros. ins_ibr_sim.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_xmm_rng1 sr1 sr2: 
    in_bigrammar_rng (` modrm_xmm) (SSE_XMM_Reg_op sr1, SSE_XMM_Reg_op sr2).
  Proof. unfold modrm_xmm; intros; ins_ibr_sim. compute [fst].
     exists (sr1, SSE_XMM_Reg_op sr2); split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_xmm_rng1: ibr_rng_db.

  Lemma modrm_xmm_rng_inv1 op1 op2: 
    in_bigrammar_rng (` modrm_xmm) (op1,op2) -> 
    exists sr, op1 = SSE_XMM_Reg_op sr.
  Proof. unfold modrm_xmm; intros; ins_ibr_sim.
    destruct v as [sr op]. exists sr; congruence.
  Qed.

  Lemma modrm_xmm_rng_inv2 op1 op2: 
    in_bigrammar_rng (` modrm_xmm) (op1,op2) -> 
    (exists sr, op2 = SSE_XMM_Reg_op sr) \/ (exists addr, op2 = SSE_Addr_op addr).
  Proof. unfold modrm_xmm; intros; ins_ibr_sim.
    destruct v as [sr op]. eapply modrm_xmm_ret_reg_rng_inv.
    sim; subst. eassumption.
  Qed.

  Lemma modrm_mm_ret_reg_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mm_ret_reg) (mr1, SSE_MM_Reg_op mr2).
  Proof. intros. unfold modrm_mm_ret_reg, modrm_gen. ins_ibr_sim. compute [fst].
    exists (inr [|pair_t sse_register_t address_t|] (mr1, mr2)).
    split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_mm_ret_reg_rng1: ibr_rng_db.

  Lemma modrm_mm_ret_reg_rng_inv mr op:
    in_bigrammar_rng (` modrm_mm_ret_reg) (mr,op) -> 
    (exists mr, op = SSE_MM_Reg_op mr) \/ (exists addr, op = SSE_Addr_op addr).
  Proof. unfold modrm_mm_ret_reg; intros. ins_ibr_sim.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_mm_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mm) (SSE_MM_Reg_op mr1, SSE_MM_Reg_op mr2).
  Proof. unfold modrm_mm; intros; ins_ibr_sim. compute [fst].
     exists (mr1, SSE_MM_Reg_op mr2); split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_mm_rng1: ibr_rng_db.

  Lemma modrm_mm_rng_inv1 op1 op2: 
    in_bigrammar_rng (` modrm_mm) (op1,op2) -> 
    exists mr, op1 = SSE_MM_Reg_op mr.
  Proof. unfold modrm_mm; intros; ins_ibr_sim.
    destruct v as [mr op]. exists mr; congruence.
  Qed.

  Lemma modrm_mm_rng_inv2 op1 op2: 
    in_bigrammar_rng (` modrm_mm) (op1,op2) -> 
    (exists mr, op2 = SSE_MM_Reg_op mr) \/ (exists addr, op2 = SSE_Addr_op addr).
  Proof. unfold modrm_mm; intros; ins_ibr_sim.
    destruct v as [mr op]. eapply modrm_mm_ret_reg_rng_inv.
    sim; subst. eassumption.
  Qed.

  Definition modrm_xmm_byte :
    wf_bigrammar (pair_t sse_operand_t (pair_t sse_operand_t byte_t)). 
    refine ((modrm_xmm $ byte)
              @ (fun v => 
                   match v with 
                     | ((op1, op2), b) => (op1,(op2,b))
                   end %% pair_t sse_operand_t (pair_t sse_operand_t byte_t))
              & (fun u:sse_operand*(sse_operand*int8) => 
                   let (op1,u1):=u in
                   let (op2,b):=u1 in
                   Some ((op1,op2),b))
              & _); invertible_tac.
  Defined.

  Definition ext_op_modrm_sse_noreg (bs: string): wf_bigrammar sse_operand_t.
    intros;
    refine(ext_op_modrm_noreg_ret_addr bs
             @ (SSE_Addr_op: [|address_t|] -> [|sse_operand_t|])
             & SSE_Addr_op_inv & _); unfold SSE_Addr_op_inv; invertible_tac;
    sse_parsable_tac.
  Defined.

  Local Ltac sse_pf_sim :=
    ins_ibr_sim; bg_pf_sim;
    repeat match goal with
      | [H: in_bigrammar_rng (` modrm_xmm) (?op1 ?op2) |- _] => 
        let H2 := fresh "H" in
        let H3 := fresh "H" in
        generalize (modrm_xmm_rng_inv1 H) (modrm_xmm_rng_inv2 H); intros H2 H3;
        destruct H2; subst;
        destruct H3 as [H3 | H3]; destruct H3; subst op2
      | [H: in_bigrammar_rng (` modrm_xmm_ret_reg) (?r1 ?op2) |- _] =>
        let H2 := fresh "H" in
        generalize (modrm_xmm_ret_reg_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op2
      | [H: in_bigrammar_rng (` modrm_mm) (?op1 ?op2) |- _] => 
        let H2 := fresh "H" in
        let H3 := fresh "H" in
        generalize (modrm_mm_rng_inv1 H) (modrm_mm_rng_inv2 H); intros H2 H3;
        destruct H2; subst;
        destruct H3 as [H3 | H3]; destruct H3; subst op2
      | [H: in_bigrammar_rng (` modrm_mm_ret_reg) (?r1 ?op2) |- _] =>
        let H2 := fresh "H" in
        generalize (modrm_mm_ret_reg_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op2
    end.

  Local Ltac sse_invertible_tac := 
    invertible_tac_gen unfold_invertible_ast sse_pf_sim sse_destruct_var.

  Definition ADDPS_b := 
    "0000" $$ "1111" $$ "0101" $$ "1000" $$ modrm_xmm. 

  Definition ADDSS_b := 
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1000" $$ modrm_xmm. 

  Definition ANDNPS_b := 
    "0000" $$ "1111" $$ "0101" $$ "0101" $$ modrm_xmm. 

  Definition ANDPS_b := 
    "0000" $$ "1111" $$ "0101" $$ "0100" $$ modrm_xmm. 

  Definition CMPPS_b := 
    "0000" $$ "1111" $$ "1100" $$ "0010" $$ modrm_xmm_byte.

  Definition CMPSS_b := 
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "1100" $$ "0010" $$ modrm_xmm_byte.

  Definition COMISS_b :=
    "0000" $$ "1111" $$ "0010" $$ "1111" $$ modrm_xmm. 

  Definition CVTPI2PS_b :=
    "0000" $$ "1111" $$ "0010" $$ "1010" $$ modrm_xmm.

  Definition CVTPS2PI_b : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine (("0000" $$ "1111" $$ "0010" $$ "1101" $$ "11" $$ sse_reg $ mmx_reg |+|
             "0000" $$ "1111" $$ "0010" $$ "1101" $$ modrm_xmm_noreg)
              @ (fun v => 
                   match v with
                     | inl (sr,mr) => (SSE_XMM_Reg_op sr, SSE_MM_Reg_op mr)
                     | inr (sr,addr) => (SSE_XMM_Reg_op sr, SSE_Addr_op addr)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u:sse_operand*sse_operand=> 
                   let (op1,op2):=u in
                   match op1 with
                     | SSE_XMM_Reg_op sr =>
                       match op2 with
                         | SSE_MM_Reg_op mr => Some (inl(sr,mr))
                         | SSE_Addr_op addr => Some (inr(sr,addr))
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); sse_invertible_tac.
  Defined.

  Definition CVTSI2SS_b : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine(("1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010"
                   $$ "1010" $$ "11" $$ sse_reg $ reg |+|
            "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010"
                   $$ "1010" $$ modrm_xmm_noreg)
             @ (fun v =>
                  match v with
                    | inl (sr,r) => (SSE_XMM_Reg_op sr, SSE_GP_Reg_op r)
                    | inr (sr,addr) => (SSE_XMM_Reg_op sr, SSE_Addr_op addr)
                  end %% pair_t sse_operand_t sse_operand_t)
             & (fun u:sse_operand*sse_operand=> 
                   let (op1,op2):=u in
                   match op1 with
                     | SSE_XMM_Reg_op sr =>
                       match op2 with
                         | SSE_GP_Reg_op r => Some (inl(sr,r))
                         | SSE_Addr_op addr => Some (inr(sr,addr))
                         | _ => None
                       end
                     | _ => None
                   end)
             & _); sse_invertible_tac.
  Defined.

  Definition ss2si_b (bs:string) :
    wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    intros.
    refine (("1111" $$ "0011" $$ "0000" $$ "1111"
                    $$ "0010" $$ bs $$ "11" $$ reg $ sse_reg |+|
             "1111" $$ "0011" $$ "0000" $$ "1111"
                    $$ "0010" $$ bs $$ modrm_noreg)
              @ (fun v =>
                  match v with
                    | inl (r,sr) => (SSE_GP_Reg_op r, SSE_XMM_Reg_op sr)
                    | inr (r,addr) => (SSE_GP_Reg_op r, SSE_Addr_op addr)
                  end %% pair_t sse_operand_t sse_operand_t)
             & (fun u:sse_operand*sse_operand=> 
                   let (op1,op2):=u in
                   match op1 with
                     | SSE_GP_Reg_op r =>
                       match op2 with
                         | SSE_XMM_Reg_op sr => Some (inl(r,sr))
                         | SSE_Addr_op addr => Some (inr(r,addr))
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); sse_invertible_tac.
  Defined.

  Definition CVTSS2SI_b := ss2si_b "1101".

  Definition CVTTPS2PI_b :=
    "0000" $$ "1111" $$ "0010" $$ "1100" $$ modrm_xmm. 

  Definition CVTTSS2SI_b := ss2si_b "1100".

  Definition DIVPS_b := 
    "0000" $$ "1111" $$ "0101" $$ "1110" $$ modrm_xmm.

  Definition DIVSS_b :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1110" $$ modrm_xmm. 

  Definition LDMXCSR_b := 
    "0000" $$ "1111" $$ "1010" $$ "1110" $$ ext_op_modrm_sse_noreg "010". 

  Definition MAXPS_b := 
    "0000" $$ "1111" $$ "0101" $$ "1111" $$ modrm_xmm. 

  Definition MAXSS_b := 
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1111" $$ modrm_xmm. 

  Definition MINPS_b := 
    "0000" $$ "1111" $$ "0101" $$ "1101" $$ modrm_xmm. 

  Definition MINSS_b :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1101" $$ modrm_xmm. 

  Definition sse_mov_b (bs:string) : 
    wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    intros.
    refine(bs $$ anybit $ modrm_xmm
             @ (fun v: bool*(sse_operand*sse_operand) =>
                  match v with
                    | (d,(op1,op2)) => 
                      if d then (op2,op1) else (op1,op2)
                  end %% pair_t sse_operand_t sse_operand_t)
             & (fun u => 
                  match u with
                    | (SSE_XMM_Reg_op _, SSE_XMM_Reg_op _)
                    | (SSE_XMM_Reg_op _, SSE_Addr_op _) =>
                      (* alternate encoding when both are regs: 
                         reverse the operands and made d true *)
                      Some (false,u)
                    | (SSE_Addr_op _, SSE_XMM_Reg_op _) =>
                      Some (true, (snd u, fst u))
                    | _ => None
                  end)
             & _); sse_invertible_tac.
    - destruct v as [d [op1 op2]]; 
      destruct d; sse_pf_sim; printable_tac; ins_ibr_sim.
  Defined.

  Definition MOVAPS_b := sse_mov_b "000011110010100".

  Definition MOVHLPS_b :=
    "0000" $$ "1111" $$ "0001" $$ "0010" $$ "11"
           $$ SSE_XMM_Reg_op_b $ SSE_XMM_Reg_op_b.

  Definition sse_mov_ps_b (bs:string) : 
    wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    intros.
    refine ("0000" $$ "1111" $$ "0001" $$ bs $$ anybit $ modrm_xmm_noreg
              @ (fun v:bool*_ =>
                   match v with
                     | (d,(sr,addr)) =>
                       if d then (SSE_Addr_op addr, SSE_XMM_Reg_op sr)
                       else (SSE_XMM_Reg_op sr, SSE_Addr_op addr)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u => 
                   match u with
                     | (SSE_XMM_Reg_op sr, SSE_Addr_op addr) =>
                       Some (false,(sr,addr))
                     | (SSE_Addr_op addr, SSE_XMM_Reg_op sr) =>
                       Some (true,(sr,addr))
                     | _ => None
                   end)
              & _); sse_invertible_tac.
    - destruct v as [d [op1 op2]]; 
      destruct d; sse_pf_sim; printable_tac; ins_ibr_sim.
  Defined.

  Definition MOVHPS_b := sse_mov_ps_b "011".

  Definition MOVLHPS_b :=
    "0000" $$ "1111" $$ "0001" $$ "0110" $$ "11"
           $$ SSE_XMM_Reg_op_b $ SSE_XMM_Reg_op_b.

  Definition MOVLPS_b := sse_mov_ps_b "001".

  Definition MOVMSKPS_b :=
    "0000" $$ "1111" $$ "0001" $$ "0110" $$ "11"
           $$ SSE_GP_Reg_op_b $ SSE_XMM_Reg_op_b.
  
  Definition MOVSS_b := sse_mov_b "11110011000011110001000".
  Definition MOVUPS_b := sse_mov_b "000011110001000".

  Definition MULPS_b :=
    "0000" $$ "1111" $$ "0101" $$ "1001" $$ modrm_xmm. 

  Definition MULSS_b :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1001" $$ modrm_xmm.

  Definition ORPS_b :=
    "0000" $$ "1111" $$ "0101" $$ "0110" $$ modrm_xmm.

  Definition RCPPS_b :=
    "0000" $$ "1111" $$ "0101" $$ "0011" $$ modrm_xmm. 

  Definition RCPSS_b :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "0011" $$ modrm_xmm.

  Definition RSQRTPS_b :=
    "0000" $$ "1111" $$ "0101" $$ "0010" $$ modrm_xmm.

  Definition RSQRTSS_b :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "0010" $$ modrm_xmm.

  Definition SHUFPS_b :=
    "0000" $$ "1111" $$ "1100" $$ "0110" $$ modrm_xmm_byte.

  Definition SQRTPS_b :=
    "0000" $$ "1111" $$ "0101" $$ "0001" $$ modrm_xmm.

  Definition SQRTSS_b :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "0001" $$ modrm_xmm.

  Definition STMXCSR_b := 
    "0000" $$ "1111" $$ "1010" $$ "1110" $$ ext_op_modrm_sse_noreg "011".

  Definition SUBPS_b :=
    "0000" $$ "1111" $$ "0101" $$ "1100" $$ modrm_xmm.

  Definition SUBSS_b :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1100" $$ modrm_xmm.

  Definition UCOMISS_b :=
    "0000" $$ "1111" $$ "0010" $$ "1110" $$ modrm_xmm.

  Definition UNPCKHPS_b :=
    "0000" $$ "1111" $$ "0001" $$ "0101" $$ modrm_xmm.

  Definition UNPCKLPS_b :=
    "0000" $$ "1111" $$ "0001" $$ "0100" $$ modrm_xmm.

  Definition XORPS_b :=
    "0000" $$ "1111" $$ "0101" $$ "0111" $$ modrm_xmm.

  (* possible todo: this needs to take operand-override prefix into account *)
  Definition PAVGB_b : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine (("0000" $$ "1111" $$ "1110" $$ "0000" $$ modrm_mm_ret_reg |+|
             "0000" $$ "1111" $$ "1110" $$ "0011" $$ modrm_mm_ret_reg)
              @ (fun v =>
                   match v with
                     | inl (mr1,op2) => (SSE_MM_Reg_op mr1,op2)
                     | inr (mr1,op2) => (op2,SSE_MM_Reg_op mr1)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u => 
                   match u with
                     | (SSE_MM_Reg_op mr1, SSE_MM_Reg_op _)
                     | (SSE_MM_Reg_op mr1, SSE_Addr_op _) =>
                       (* alternate encoding when two regs: swap the operands *)
                       Some (inl (mr1, snd u))
                     | (SSE_Addr_op addr, SSE_MM_Reg_op mr1) =>
                       Some (inr (mr1, fst u))
                     | _ => None
                   end)
              & _); sse_invertible_tac.
  Defined.

  Definition PEXTRW_b :=
    "0000" $$ "1111" $$ "1100" $$ "0101" $$ "11"
           $$ SSE_GP_Reg_op_b $ SSE_MM_Reg_op_b $ byte.

  Definition PINSRW_b : 
    wf_bigrammar (pair_t sse_operand_t (pair_t sse_operand_t byte_t)).
    refine (("0000" $$ "1111" $$ "1100" $$ "0100" $$ "11"
                    $$ mmx_reg $ reg $ byte |+|
             "0000" $$ "1111" $$ "1100" $$ "0100" $$ modrm_mm_noreg $ byte)
              @ (fun v =>
                   match v with
                     | inl (mr,(r,imm)) =>
                       (SSE_MM_Reg_op mr, (SSE_GP_Reg_op r, imm))
                     | inr ((mr,addr),imm) =>
                       (SSE_MM_Reg_op mr, (SSE_Addr_op addr, imm))
                   end %% pair_t sse_operand_t (pair_t sse_operand_t byte_t))
              & (fun u => 
                   match u with
                     | (SSE_MM_Reg_op mr, (SSE_GP_Reg_op r, imm)) =>
                       Some (inl (mr,(r,imm)))
                     | (SSE_MM_Reg_op mr, (SSE_Addr_op addr, imm)) =>
                       Some (inr ((mr,addr),imm))
                     | _ => None
                   end)
              & _); sse_invertible_tac.
  Defined.

  Definition PMAXSW_b :=
    "0000" $$ "1111" $$ "1110" $$ "1110" $$ modrm_mm.

  Definition PMAXUB_b :=
    "0000" $$ "1111" $$ "1101" $$ "1110" $$ modrm_mm. 

  Definition PMINSW_b :=
    "0000" $$ "1111" $$ "1110" $$ "1010" $$ modrm_mm. 

  Definition PMINUB_b :=
    "0000" $$ "1111" $$ "1101" $$ "1010" $$ modrm_mm. 

  Definition PMOVMSKB_b :=
    "0000" $$ "1111" $$ "1101" $$ "0111" $$ "11"
           $$ SSE_GP_Reg_op_b $ SSE_MM_Reg_op_b.

(*
  Already done in MMX grammar section

 Definition PMULHUW_b :=
  "0000" $$ "1111" $$ "1110" $$ "0100" $$ "11" $$ mmx_reg $ mmx_reg @
    (fun p => let (a, b) := p in PMULHUW (SSE_MM_Reg_op a) (SSE_MM_Reg_op b) %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "1110" $$ "0100" $$ modrm_mm @ 
    (fun p => let (mem, mmx) := p in PMULHUW mem mmx %% instruction_t).
*)

  Definition PSADBW_b :=
    "0000" $$ "1111" $$ "1111" $$ "0110" $$ modrm_mm.

  Definition PSHUFW_b : 
    wf_bigrammar (pair_t sse_operand_t (pair_t sse_operand_t byte_t)).
    refine ("0000" $$ "1111" $$ "0111" $$ "0000" $$ modrm_mm $ byte 
              @ (fun v => 
                   match v with
                     | ((op1, op2), imm) => (op1, (op2, imm))
                   end %% pair_t sse_operand_t (pair_t sse_operand_t byte_t))
              & (fun u => 
                   match u with
                     | (op1,(op2,imm)) => Some ((op1,op2),imm)
                   end)
              & _); sse_invertible_tac.
  Defined.

  Definition MASKMOVQ_b :=
    "0000" $$ "1111" $$ "1111" $$ "0111" $$ "11"
           $$ SSE_MM_Reg_op_b $ SSE_MM_Reg_op_b.

  Definition MOVNTPS_b : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine ("0000" $$ "1111" $$ "0010" $$ "1011" $$ modrm_xmm_noreg
              @ (fun v =>
                   match v with
                     | (mr, addr) => (SSE_Addr_op addr, SSE_XMM_Reg_op mr)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u => 
                   match u with
                     | (SSE_Addr_op addr, SSE_XMM_Reg_op mr) =>
                       Some (mr,addr)
                     | _ => None
                   end)
              & _); sse_invertible_tac.
  Defined.

  Definition MOVNTQ_b : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine ("0000" $$ "1111" $$ "1110" $$ "0111" $$ modrm_mm_noreg
              @ (fun v =>
                   match v with
                     | (mr, addr) => (SSE_Addr_op addr, SSE_MM_Reg_op mr)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u => 
                   match u with
                     | (SSE_Addr_op addr, SSE_MM_Reg_op mr) =>
                       Some (mr,addr)
                     | _ => None
                   end)
              & _); sse_invertible_tac.
  Defined.

  Definition PREFETCHT0_b :=
    "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "001".

  Definition PREFETCHT1_b :=
    "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "010". 

  Definition PREFETCHT2_b := 
    "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "011". 

  Definition PREFETCHNTA_b :=
    "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "000". 

  Definition SFENCE_b := "0000" $$ "1111" $$ "1010" $$ "1110" $$ "1111"
                                $$ ! "1000".


(* End X86_PARSER. *)

