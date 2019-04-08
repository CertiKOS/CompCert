Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs Errors.
Require Import Num Segment.
Require Import Asm SegAsm TransSegAsm FlatAsm FlatBinary.
Require Import TAsmlabelgen TAsmcallgen TAsmgidgen FlatAsmgen FlatBingen.

Local Open Scope error_monad_scope.

Definition dummy_segblock := 
  {| segblock_id := 1%positive; segblock_start := Ptrofs.zero; segblock_size := Ptrofs.zero |}.
Definition dummy_id := 1%positive.
Definition dummy_lbl_map : SegAsmProgram.LABEL_MAP_TYPE :=
  fun _ _ => Some (dummy_id, Ptrofs.zero).
Definition dummy_gid_map : SegAsmProgram.GID_MAP_TYPE :=
  fun _ => Some (dummy_id, Ptrofs.zero).
Definition dummy_smap : SMAP_TYPE := (fun _ => Some Ptrofs.zero).

Definition transl_asm_instr (i:Asm.instruction) : res (list byte) :=
  let ii := (i, dummy_segblock, dummy_id) in
  do ii1 <- TAsmlabelgen.transl_instr dummy_lbl_map dummy_id ii;
  let ii2 := TAsmcallgen.transl_instr' dummy_gid_map ii1 in
  let ii3 := TAsmgidgen.transl_instr'' dummy_gid_map ii2 in
  do ii4 <- FlatAsmgen.transl_instr' dummy_smap ii3;
  FlatBingen.transl_instr' ii4.

Definition asm_instr_size (i:Asm.instruction) : res Z :=
  match transl_asm_instr i with
  | OK bytes => OK (Z.of_nat (length bytes))
  | Error msg => Error msg
  end.

Definition dummy_lbl : label := 1%positive.
Definition dummy_sig : signature :=
  {|
    sig_args := nil;
    sig_res := None;
    sig_cc := mkcallconv false false false;
  |}.

Definition am1 := Asm.Addrmode None None (inl 0).
Definition am2 := Asm.Addrmode (Some RAX) None (inl 0).
Definition am3 := Asm.Addrmode (Some RSP) None (inl 0).
Definition am4 := Asm.Addrmode (Some RBX) (Some (RAX, 1)) (inl 0).
Definition am5 := Asm.Addrmode (Some RSP) (Some (RAX, 1)) (inl 0).

  
Compute (asm_instr_size (Pjmp_l dummy_lbl)).
Compute (asm_instr_size (Pjcc Cond_e dummy_lbl)).
Compute (asm_instr_size (Pcall (inr 1%positive) dummy_sig)).
Compute (asm_instr_size (Pleal RAX am1)).
Compute (asm_instr_size (Pleal RAX am2)).
Compute (asm_instr_size (Pleal RAX am3)).
Compute (asm_instr_size (Pleal RAX am4)).
Compute (asm_instr_size (Pleal RAX am5)).


