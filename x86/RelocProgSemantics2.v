(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 6, 2019  *)
(* *******************  *)

(** * The semantics of relocatable program after instruction and data encoding *)

(** The key feature of this semantics: it first decode the instructions and
    then use RelocProgsemantics1; moreover, the encoded data is used directly
    in the initialization of the data section *)

Require Import Coqlib Maps AST Integers Values.
Require Import Events Floats Memory Smallstep.
Require Import Asm RelocProgram RawAsm Globalenvs.
Require Import Stacklayout Conventions EraseArgs.
Require Import Linking SeqTable Errors.
Require Import RelocBinDecode.
Require RelocProgSemantics1.

Local Open Scope error_monad_scope.


Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

(** Initialization of memory *)
Section WITHGE.

Variable ge:RelocProgSemantics1.Genv.t.

Definition store_init_data_bytes (m: mem) (b: block) (p: Z) (bytes: list byte)
                              : option mem :=
  let memvals := List.map Byte bytes in
  Mem.storebytes m b p memvals.

Definition alloc_data_section (t:sectable) (m:mem) : option mem :=
  match SeqTable.get sec_data_id t with
  | None => None
  | Some sec =>
    let sz := (sec_size sec) in
    match sec with
    | sec_bytes init =>
      let '(m1, b) := Mem.alloc m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
        match store_init_data_bytes m2 b 0 init with
        | None => None
        | Some m3 => Mem.drop_perm m3 b 0 sz Writable
        end
      end
    | _ => None
    end
  end.

End WITHGE.

Definition init_mem (p: program) :=
  let ge := RelocProgSemantics1.globalenv p in
  let stbl := prog_sectable p in
  match RelocProgSemantics1.alloc_data_section ge stbl Mem.empty with
  | None => None
  | Some m1 =>
    match RelocProgSemantics1.alloc_code_section stbl m1 with
    | None => None
    | Some m2 =>
      RelocProgSemantics1.alloc_external_symbols m2 (prog_symbtable p)
    end
  end.

Section WITHMAPS.

Variable rtbl_ofs_map: reloc_ofs_map_type.

Variable symtbl : symbtable.

Fixpoint decode_instrs (fuel:nat) (ofs: Z) (bytes: list byte) (instrs: list instruction) : res (list instruction) :=
  match bytes with
  | nil => OK (rev instrs)
  | _ =>
    match fuel with
    | O => Error (msg "instruction decoding failed: run out of fuel")
    | S fuel' =>
      do r <- fmc_instr_decode rtbl_ofs_map symtbl ofs bytes;
      let '(instr, bytes') := r in
      decode_instrs fuel' (ofs + instr_size instr) bytes' (instr :: instrs)
    end
  end.

Definition decode_instrs' (bytes: list byte) :=
  decode_instrs (length bytes) 0 bytes nil.
  
Definition decode_code_section (s:section) : res section :=
  match s with
  | sec_bytes bs =>
    do instrs <- decode_instrs' bs;
    OK (sec_text instrs)
  | _ =>
    Error (msg "Code section is not encoded into bytes")
  end.
    
End WITHMAPS.

Definition decode_prog_code_section (p:program) : res program :=
  let t := (prog_sectable p) in
  match SeqTable.get sec_code_id t with
  | None => Error (msg "Cannot find a code section in the program")
  | Some sec =>
    match get_reloctable sec_code_id (prog_reloctables p) with
    | None => Error (msg "Cannot find a relocation table for code section in the program")
    | Some rtbl =>
      let rofsmap := gen_reloc_ofs_map rtbl in
      let stbl := prog_symbtable p in
      do sec' <- decode_code_section rofsmap stbl sec;
        match SeqTable.set sec_code_id sec' t with
        | None => Error (msg "Cannot find a code section in the program")
        | Some t' =>
          OK {| prog_defs      := prog_defs p;
                prog_public    := prog_public p;
                prog_main      := prog_main p;
                prog_sectable  := t';
                prog_symbtable := prog_symbtable p;
                prog_strtable  := prog_strtable p;
                prog_reloctables := prog_reloctables p;
                prog_senv        := prog_senv p; 
             |}
        end
    end
  end.
    

Inductive initial_state (prog: program) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall m prog',
    decode_prog_code_section prog = OK prog' ->
    init_mem prog' = Some m ->
    RelocProgSemantics1.initial_state_gen prog' rs m s ->
    initial_state prog rs s.

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen RelocProgSemantics1.step 
                (initial_state p rs) RelocProgSemantics1.final_state 
                (RelocProgSemantics1.globalenv p) 
                (RelocProgSemantics1.genv_senv (RelocProgSemantics1.globalenv p)).


(** Determinacy of the semantics. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  intros.
  destruct (RelocProgSemantics1.semantics_determinate p rs).
  constructor; simpl; auto.
- (* initial states *)
  intros. inv H; inv H0. 
  assert (prog' = prog'0) by congruence. subst.
  assert (m = m0) by congruence. subst. inv H3; inv H5.
  assert (m1 = m5 /\ bstack = bstack0) by intuition congruence. destruct H0; subst.
  assert (m2 = m6) by congruence. subst.
  f_equal. congruence.
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  destruct (RelocProgSemantics1.reloc_prog_receptive p rs).
  split; auto.
Qed.

End WITHEXTERNALCALLS.