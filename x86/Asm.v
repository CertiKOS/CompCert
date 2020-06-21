(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for IA32 assembly language *)

Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

(** * Abstract syntax *)

(** ** Registers. *)

(** Integer registers. *)

Inductive ireg: Type :=
  | RAX | RBX | RCX | RDX | RSI | RDI | RBP | RSP
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

(** Floating-point registers, i.e. SSE2 registers *)

Inductive freg: Type :=
  | XMM0  | XMM1  | XMM2  | XMM3  | XMM4  | XMM5  | XMM6  | XMM7
  | XMM8  | XMM9  | XMM10 | XMM11 | XMM12 | XMM13 | XMM14 | XMM15.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Bits of the flags register. *)

Inductive crbit: Type :=
  | ZF | CF | PF | SF | OF.

(** All registers modeled here. *)

Inductive preg: Type :=
  | PC: preg                            (**r program counter *)
  | IR: ireg -> preg                    (**r integer register *)
  | FR: freg -> preg                    (**r XMM register *)
  | ST0: preg                           (**r top of FP stack *)
  | CR: crbit -> preg                   (**r bit of the flags register *)
  | RA: preg.                   (**r pseudo-reg representing return address *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.
Coercion CR: crbit >-> preg.

(** Conventional names for stack pointer ([SP]) and return address ([RA]) *)

Notation SP := RSP (only parsing).

(** ** Instruction set. *)

Definition label := positive.

(** General form of an addressing mode. *)

Inductive addrmode: Type :=
  | Addrmode (base: option ireg)
             (ofs: option (ireg * Z))
             (const: Z + ident * ptrofs).

(** Testable conditions (for conditional jumps and more). *)

Inductive testcond: Type :=
  | Cond_e | Cond_ne
  | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g
  | Cond_p | Cond_np.

(** Instructions.  IA32 instructions accept many combinations of
  registers, memory references and immediate constants as arguments.
  Here, we list only the combinations that we actually use.

  Naming conventions for types:
- [b]: 8 bits
- [w]: 16 bits ("word")
- [l]: 32 bits ("longword")
- [q]: 64 bits ("quadword")
- [d] or [sd]: FP double precision (64 bits)
- [s] or [ss]: FP single precision (32 bits)

  Naming conventions for operands:
- [r]: integer register operand
- [f]: XMM register operand
- [m]: memory operand
- [i]: immediate integer operand
- [s]: immediate symbol operand
- [l]: immediate label operand
- [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.
*)

Inductive instruction: Type :=
  (** Moves *)
  | Pmov_rr (rd: ireg) (r1: ireg)       (**r [mov] (integer) *)
  | Pmovl_ri (rd: ireg) (n: int)
  | Pmovq_ri (rd: ireg) (n: int64)
  | Pmov_rs (rd: ireg) (id: ident)
  | Pmovl_rm (rd: ireg) (a: addrmode)
  | Pmovq_rm (rd: ireg) (a: addrmode)
  | Pmovl_mr (a: addrmode) (rs: ireg)
  | Pmovq_mr (a: addrmode) (rs: ireg)
  | Pmovsd_ff (rd: freg) (r1: freg)     (**r [movsd] (single 64-bit float) *)
  | Pmovsd_fi (rd: freg) (n: float)     (**r (pseudo-instruction) *)
  | Pmovsd_fm (rd: freg) (a: addrmode)
  | Pmovsd_mf (a: addrmode) (r1: freg)
  | Pmovss_fi (rd: freg) (n: float32)   (**r [movss] (single 32-bit float) *)
  | Pmovss_fm (rd: freg) (a: addrmode)
  | Pmovss_mf (a: addrmode) (r1: freg)
  | Pfldl_m (a: addrmode)               (**r [fld] double precision *)
  | Pfstpl_m (a: addrmode)              (**r [fstp] double precision *)
  | Pflds_m (a: addrmode)               (**r [fld] simple precision *)
  | Pfstps_m (a: addrmode)              (**r [fstp] simple precision *)
  (*SACC:*)
  | Pxchg_rr (r1: ireg) (r2: ireg)      (**r register-register exchange *)
  (** Moves with conversion *)
  | Pmovb_mr (a: addrmode) (rs: ireg)   (**r [mov] (8-bit int) *)
  | Pmovw_mr (a: addrmode) (rs: ireg)   (**r [mov] (16-bit int) *)
  | Pmovzb_rr (rd: ireg) (rs: ireg)     (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm (rd: ireg) (a: addrmode)
  | Pmovsb_rr (rd: ireg) (rs: ireg)     (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm (rd: ireg) (a: addrmode)
  | Pmovzw_rr (rd: ireg) (rs: ireg)     (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm (rd: ireg) (a: addrmode)
  | Pmovsw_rr (rd: ireg) (rs: ireg)     (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm (rd: ireg) (a: addrmode)
  | Pmovzl_rr (rd: ireg) (rs: ireg)     (**r [movzl] (32-bit zero-extension) *)
  | Pmovsl_rr (rd: ireg) (rs: ireg)     (**r [movsl] (32-bit sign-extension) *)
  | Pmovls_rr (rd: ireg)                (** 64 to 32 bit conversion (pseudo) *)
  | Pcvtsd2ss_ff (rd: freg) (r1: freg)  (**r conversion to single float *)
  | Pcvtss2sd_ff (rd: freg) (r1: freg)  (**r conversion to double float *)
  | Pcvttsd2si_rf (rd: ireg) (r1: freg) (**r double to signed int *)
  | Pcvtsi2sd_fr (rd: freg) (r1: ireg)  (**r signed int to double *)
  | Pcvttss2si_rf (rd: ireg) (r1: freg) (**r single to signed int *)
  | Pcvtsi2ss_fr (rd: freg) (r1: ireg)  (**r signed int to single *)
  | Pcvttsd2sl_rf (rd: ireg) (r1: freg) (**r double to signed long *)
  | Pcvtsl2sd_fr (rd: freg) (r1: ireg)  (**r signed long to double *)
  | Pcvttss2sl_rf (rd: ireg) (r1: freg) (**r single to signed long *)
  | Pcvtsl2ss_fr (rd: freg) (r1: ireg)  (**r signed long to single *)
  (** Integer arithmetic *)
  | Pleal (rd: ireg) (a: addrmode)
  | Pleaq (rd: ireg) (a: addrmode)
  | Pnegl (rd: ireg)
  | Pnegq (rd: ireg)
  | Paddl_ri (rd: ireg) (n: int)
  | Paddq_ri (rd: ireg) (n: int64)
  | Psubl_rr (rd: ireg) (r1: ireg)
  | Psubq_rr (rd: ireg) (r1: ireg)
  | Pimull_rr (rd: ireg) (r1: ireg)
  | Pimulq_rr (rd: ireg) (r1: ireg)
  | Pimull_ri (rd: ireg) (n: int)
  | Pimulq_ri (rd: ireg) (n: int64)
  | Pimull_r (r1: ireg)
  | Pimulq_r (r1: ireg)
  | Pmull_r (r1: ireg)
  | Pmulq_r (r1: ireg)
  | Pcltd
  | Pcqto
  | Pdivl (r1: ireg)
  | Pdivq (r1: ireg)
  | Pidivl (r1: ireg)
  | Pidivq (r1: ireg)
  | Pandl_rr (rd: ireg) (r1: ireg)
  | Pandq_rr (rd: ireg) (r1: ireg)
  | Pandl_ri (rd: ireg) (n: int)
  | Pandq_ri (rd: ireg) (n: int64)
  | Porl_rr (rd: ireg) (r1: ireg)
  | Porq_rr (rd: ireg) (r1: ireg)
  | Porl_ri (rd: ireg) (n: int)
  | Porq_ri (rd: ireg) (n: int64)
  | Pxorl_r (rd: ireg)                  (**r [xor] with self = set to zero *)
  | Pxorq_r (rd: ireg)
  | Pxorl_rr (rd: ireg) (r1: ireg)
  | Pxorq_rr (rd: ireg) (r1: ireg)
  | Pxorl_ri (rd: ireg) (n: int)
  | Pxorq_ri (rd: ireg) (n: int64)
  | Pnotl (rd: ireg)
  | Pnotq (rd: ireg)
  | Psall_rcl (rd: ireg)
  | Psalq_rcl (rd: ireg)
  | Psall_ri (rd: ireg) (n: int)
  | Psalq_ri (rd: ireg) (n: int)
  | Pshrl_rcl (rd: ireg)
  | Pshrq_rcl (rd: ireg)
  | Pshrl_ri (rd: ireg) (n: int)
  | Pshrq_ri (rd: ireg) (n: int)
  | Psarl_rcl (rd: ireg)
  | Psarq_rcl (rd: ireg)
  | Psarl_ri (rd: ireg) (n: int)
  | Psarq_ri (rd: ireg) (n: int)
  | Pshld_ri (rd: ireg) (r1: ireg) (n: int)
  | Prorl_ri (rd: ireg) (n: int)
  | Prorq_ri (rd: ireg) (n: int)
  | Pcmpl_rr (r1 r2: ireg)
  | Pcmpq_rr (r1 r2: ireg)
  | Pcmpl_ri (r1: ireg) (n: int)
  | Pcmpq_ri (r1: ireg) (n: int64)
  | Ptestl_rr (r1 r2: ireg)
  | Ptestq_rr (r1 r2: ireg) 
  | Ptestl_ri (r1: ireg) (n: int)
  | Ptestq_ri (r1: ireg) (n: int64)
  | Pcmov (c: testcond) (rd: ireg) (r1: ireg)
  | Psetcc (c: testcond) (rd: ireg)
  (** Floating-point arithmetic *)
  | Paddd_ff (rd: freg) (r1: freg)
  | Psubd_ff (rd: freg) (r1: freg)
  | Pmuld_ff (rd: freg) (r1: freg)
  | Pdivd_ff (rd: freg) (r1: freg)
  | Pnegd (rd: freg)
  | Pabsd (rd: freg)
  | Pcomisd_ff (r1 r2: freg)
  | Pxorpd_f (rd: freg)	              (**r [xor] with self = set to zero *)
  | Padds_ff (rd: freg) (r1: freg)
  | Psubs_ff (rd: freg) (r1: freg)
  | Pmuls_ff (rd: freg) (r1: freg)
  | Pdivs_ff (rd: freg) (r1: freg)
  | Pnegs (rd: freg)
  | Pabss (rd: freg)
  | Pcomiss_ff (r1 r2: freg)
  | Pxorps_f (rd: freg)	              (**r [xor] with self = set to zero *)
  (** Branches and calls *)
  | Pjmp_l (l: label)
  (*SACC:*)
  | Pjmp (ros: ireg + ident) (sg: signature)
  (*SACC: uses Pjmp instead*)(*
  | Pjmp_s (symb: ident) (sg: signature)
  | Pjmp_r (r: ireg) (sg: signature)*)
  | Pjcc (c: testcond)(l: label)
  | Pjcc2 (c1 c2: testcond)(l: label)   (**r pseudo *)
  | Pjmptbl (r: ireg) (tbl: list label) (**r pseudo *)
  (*SACC:*)
  | Pcall (ros: ireg + ident) (sg: signature)
  (*SACC: uses Pcall instead *)(*
  | Pcall_s (symb: ident) (sg: signature)
  | Pcall_r (r: ireg) (sg: signature)*)
  | Pret
  (** Saving and restoring registers *)
  | Pmov_rm_a (rd: ireg) (a: addrmode)  (**r like [Pmov_rm], using [Many64] chunk *)
  | Pmov_mr_a (a: addrmode) (rs: ireg)  (**r like [Pmov_mr], using [Many64] chunk *)
  | Pmovsd_fm_a (rd: freg) (a: addrmode) (**r like [Pmovsd_fm], using [Many64] chunk *)
  | Pmovsd_mf_a (a: addrmode) (r1: freg) (**r like [Pmovsd_mf], using [Many64] chunk *)
  (** Pseudo-instructions *)
  | Plabel(l: label)
  | Pallocframe(sz: Z)(ofs_ra (*SACC:*)(*ofs_link*): ptrofs)
  | Pfreeframe(sz: Z)(ofs_ra (*SACC:*)(*ofs_link*): ptrofs)
  (*SACC:*)
  | Pload_parent_pointer (rd: ireg) (sz:Z)
  | Pbuiltin(ef: external_function)(args: list (builtin_arg preg))(res: builtin_res preg)
  (**SACC: Local jumps using relative offsets *)
  | Pjmp_l_rel (ofs: Z)
  | Pjcc_rel (c: testcond)(ofs: Z)
  | Pjcc2_rel (c1 c2: testcond)(ofs: Z)   (**r pseudo *)
  | Pjmptbl_rel (r: ireg) (tbl: list Z) (**r pseudo *)
  (**SACC: Nop *)
  | Pnop
  (** Instructions not generated by [Asmgen] -- TO CHECK *)
  | Padcl_ri (rd: ireg) (n: int)
  | Padcl_rr (rd: ireg) (r2: ireg)
  | Paddl_mi (a: addrmode) (n: int)
  | Paddl_rr (rd: ireg) (r2: ireg)
  | Pbsfl (rd: ireg) (r1: ireg)
  | Pbsfq (rd: ireg) (r1: ireg)
  | Pbsrl (rd: ireg) (r1: ireg)
  | Pbsrq (rd: ireg) (r1: ireg)
  | Pbswap64 (rd: ireg)
  | Pbswap32 (rd: ireg)
  | Pbswap16 (rd: ireg)
  | Pcfi_adjust (n: int)
  | Pfmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pmaxsd (rd: freg) (r2: freg)
  | Pminsd (rd: freg) (r2: freg)
  | Pmovb_rm (rd: ireg) (a: addrmode)
  | Pmovsq_mr  (a: addrmode) (rs: freg)
  | Pmovsq_rm (rd: freg) (a: addrmode)
  | Pmovsb
  | Pmovsw
  | Pmovw_rm (rd: ireg) (ad: addrmode)
  | Prep_movsl
  | Psbbl_rr (rd: ireg) (r2: ireg)
  | Psqrtsd (rd: freg) (r1: freg)
  | Psubl_ri (rd: ireg) (n: int)
  | Psubq_ri (rd: ireg) (n: int64).

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code; (*SACC:*)fn_stacksize: Z}.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(*SACC:* Instruction sizes *)
Section SACC_INSTR_SIZE.

Definition addrmode_size_aux (a:addrmode) : Z :=
  let '(Addrmode base ofs const) := a in
  match ofs, base with
  | None, None => 1
  | None, Some rb =>
    if ireg_eq rb RSP then 2 else 1
  | Some _, _ => 2
  end.

Definition addrmode_size (a:addrmode) : Z :=
  addrmode_size_aux a + 4.

(* [addrmode_size] properties *)

Lemma addrmode_size_aux_pos: forall a, addrmode_size_aux a > 0.
Proof.
  intros. unfold addrmode_size_aux. destruct a.
  destruct ofs. omega. destruct base. 
  destr; omega. omega.
Qed.

Lemma addrmode_size_aux_upper_bound: forall a, addrmode_size_aux a <= 2.
Proof.
  intros. destruct a. simpl. 
  destruct ofs; try omega.
  destruct base; try omega.
  destr; omega.
Qed.

Definition amod_size_ub := 6.

Lemma addrmode_size_pos: forall a, addrmode_size a > 0.
Proof.
  intros. unfold addrmode_size. 
  generalize (addrmode_size_aux_pos a). omega.
Qed.

Lemma addrmode_size_upper_bound: forall a, addrmode_size a <= amod_size_ub.
Proof.
  intros. unfold addrmode_size. 
  generalize (addrmode_size_aux_upper_bound a). unfold amod_size_ub. omega.
Qed.

Global Opaque addrmode_size.

(* [instr_size] definition *)

Definition instr_size (i: instruction) : Z :=
  match i with
  | Pjmp_l _ => 5
  | Pjcc _ _ => 6
  | Pjmp_l_rel _ => 5
  | Pjcc_rel _ _ => 6
  | Pcall (inr _) _ => 5
  | Pjmp (inr _) _ => 5
  | Pleal _ a => 1 + addrmode_size a
  | Pxorl_r _ => 2
  | Paddl_ri _ _ => 6
  | Psubl_ri _ _ => 6
  | Psubl_rr _ _ => 2
  | Pmovl_ri _ _ => 5
  | Pmov_rr _ _ => 2
  | Pmovl_rm _ a => 1 + addrmode_size a
  | Pmovl_mr a _ => 1 + addrmode_size a
  | Pmov_rm_a _ a => 1 + addrmode_size a
  | Pmov_mr_a a _ => 1 + addrmode_size a
  | Ptestl_rr _ _ => 2
  | Pret => 1
  | Pimull_rr _ _ => 3
  | Pcmpl_rr _ _ => 2
  | Pcmpl_ri _ _ => 6
  | Pcltd => 1
  | Pidivl _ => 2
  | Psall_ri _ _ => 3
  | Plabel _ => 1
  | Pmov_rs _ _ => 6
  | Pnop => 1
  | _ => 1
  end.

Fixpoint code_size (c:code) : Z :=
  match c with
  | nil => 0
  | i::c' => instr_size i + (code_size c')
  end.

(* Properties of [instr_size] *)

Lemma Pjmp_rel_size_eq : forall ofs l,
    instr_size (Pjmp_l_rel ofs) = instr_size (Pjmp_l l).
Proof.
  simpl. auto.
Qed.

Lemma Pjcc_rel_size_eq: forall ofs l cond,
    instr_size (Pjcc cond l) = instr_size (Pjcc_rel cond ofs).
Proof.
  simpl. auto.
Qed.

Lemma Pjcc2_rel_size_eq: forall ofs l cond1 cond2,
    instr_size (Pjcc2 cond1 cond2 l) = instr_size (Pjcc2_rel cond1 cond2 ofs).
Proof.
  simpl. auto.
Qed.

Lemma Pjmptbl_rel_size_eq: forall r tbl tbl',
    instr_size (Pjmptbl r tbl) = instr_size (Pjmptbl_rel r tbl').
Proof.
  simpl. auto.
Qed.

Lemma instr_size_positive : forall i, 0 < instr_size i.
Proof.
  intros. unfold instr_size. 
  destruct i; try omega;
    try (generalize (addrmode_size_pos a); omega);
    try (destr; omega).
Qed.  

Lemma z_le_ptrofs_max: forall n, 
    n < two_power_nat (if Archi.ptr64 then 64 else 32) -> 
    n <= Ptrofs.max_unsigned.
Proof.
  intros. unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus.
  unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize.
  omega.
Qed.

Local Transparent Archi.ptr64.

Lemma z_le_ptrofs_max32: forall n, 
    n < two_power_nat 32 -> 
    n <= Ptrofs.max_unsigned.
Proof.
  intros. apply z_le_ptrofs_max. unfold Archi.ptr64. assumption.
Qed.

Ltac solve_n_le_ptrofs_max :=
  match goal with
  | [ |- ?a <= Ptrofs.max_unsigned ] =>
    apply z_le_ptrofs_max32; reflexivity
  end.

Ltac solve_amod_le_ptrofs_max :=
  match goal with
  | [ |- ?n + addrmode_size ?a <= Ptrofs.max_unsigned ] =>
    apply Z.le_trans with (1 + amod_size_ub);
    [ generalize (addrmode_size_upper_bound a); omega | solve_n_le_ptrofs_max ]
  end.

Lemma instr_size_repr: forall i, 0 <= instr_size i <= Ptrofs.max_unsigned.
Proof.
  intros. unfold instr_size. 
  destruct i; split; try omega; 
  try solve_n_le_ptrofs_max;
  try (generalize (addrmode_size_pos a); omega);
  try solve_amod_le_ptrofs_max.
  destr; omega.
  destr; try solve_n_le_ptrofs_max.
  destr; omega.
  destr; try solve_n_le_ptrofs_max.
Qed.
  
Global Opaque instr_size.

(* Properties of [code_size] *)

Lemma code_size_non_neg : forall c,
  code_size c >= 0.
Proof.
  intros. induction c.
  - simpl. omega.
  - simpl. generalize (instr_size_positive a). omega.
Qed.

End SACC_INSTR_SIZE.

(*SACC: checks for not jumps *)
Section SACC_NOT_JMP.

Definition instr_not_jmp_rel (i:instruction) :=
  match i with
  | Pjmp_l_rel _ 
  | Pjcc_rel _ _ 
  | Pjcc2_rel _ _ _
  | Pjmptbl_rel _ _ => False
  | _ => True
  end.

Definition func_no_jmp_rel (f:function) :=
  Forall instr_not_jmp_rel (fn_code f).

Definition fundef_no_jmp_rel (f:fundef) :=
  match f with
  | Internal f => func_no_jmp_rel f
  | External _ => True
  end.

Definition prog_no_jmp_rel (p: program) :=
  Forall (fun def => match def with
                  | (id, Gvar _) => True
                  | (id, Gfun f) => fundef_no_jmp_rel f
                  end) (prog_defs p).

Definition instr_not_jmp_rel_dec : forall i, {instr_not_jmp_rel i} + {~instr_not_jmp_rel i}.
Proof.
  destruct i; auto; try (left; cbn; auto).
Defined.

Definition func_no_jmp_rel_dec: forall f, {func_no_jmp_rel f} + {~func_no_jmp_rel f}.
Proof.
  destruct f. unfold func_no_jmp_rel. simpl.
  apply Forall_dec. 
  apply instr_not_jmp_rel_dec.
Defined.

Definition fundef_no_jmp_rel_dec: forall f, {fundef_no_jmp_rel f} + {~fundef_no_jmp_rel f}.
Proof.
  destruct f. 
  simpl. apply func_no_jmp_rel_dec.
  simpl. auto.
Defined.

Definition prog_no_jmp_rel_dec: forall p, {prog_no_jmp_rel p} + {~prog_no_jmp_rel p}.
Proof.
  destruct p. unfold prog_no_jmp_rel. simpl.
  apply Forall_dec.
  destruct x as [id def]. repeat destr.
  apply fundef_no_jmp_rel_dec.
Defined.

End SACC_NOT_JMP.

(** * Operational semantics *)

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. decide equality. Defined.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(*SACC:*)
Fixpoint no_rsp_pair (b: rpair preg) :=
  match b with
    One r => r <> RSP
  | Twolong hi lo => hi <> RSP /\ lo <> RSP
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

(*SACC:*)
Fixpoint no_rsp_builtin_preg (b: builtin_res preg) :=
  match b with
    BR r => r <> RSP
  | BR_none => True
  | BR_splitlong hi lo => no_rsp_builtin_preg lo /\ no_rsp_builtin_preg hi
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - (*SACC:*)instr_size i) il
  end.

(*SACC: Properties of [find_instr] *)
Section SACC_FIND_INSTR.

Lemma find_instr_pos_positive:
  forall l o i,
    find_instr o l = Some i -> 0 <= o.
Proof.
  induction l; simpl; intros; eauto. congruence.
  destr_in H. omega. apply IHl in H.
  generalize (instr_size_positive a). omega.
Qed.

Lemma find_instr_no_overlap:
  forall l o1 o2 i1 i2,
    find_instr o1 l = Some i1 ->
    find_instr o2 l = Some i2 ->
    o1 <> o2 ->
    o1 + instr_size i1 <= o2 \/ o2 + instr_size i2 <= o1.
Proof.
  induction l; simpl; intros; eauto. congruence.
  repeat destr_in H; repeat destr_in H0.
  - apply find_instr_pos_positive in H2. omega.
  - apply find_instr_pos_positive in H3. omega.
  - specialize (IHl _ _ _ _ H3 H2). trim IHl. omega. omega.
Qed.

Lemma find_instr_no_overlap':
  forall l o1 o2 i1 i2,
    find_instr o1 l = Some i1 ->
    find_instr o2 l = Some i2 ->
    i1 = i2 \/ o1 + instr_size i1 <= o2 \/ o2 + instr_size i2 <= o1.
Proof.
  intros l o1 o2 i1 i2 FI1 FI2.
  destruct (zeq o1 o2). subst. rewrite FI1 in FI2; inv FI2; auto.
  right.
  eapply find_instr_no_overlap; eauto.
Qed.

End SACC_FIND_INSTR.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
    let nextpos := pos + instr_size instr in
      if is_label lbl instr then Some nextpos else label_pos lbl nextpos c'
  end.

(*SACC: Properties of [label_pos] *)
Section SACC_LABEL_POS.

Lemma label_pos_rng:
  forall lbl c pos z,
    label_pos lbl pos c = Some z ->
    0 <= pos ->
    0 <= z - pos <= code_size c.
Proof.
  induction c; simpl; intros; eauto. congruence. repeat destr_in H.
  generalize (code_size_non_neg c) (instr_size_positive a); omega.
  apply IHc in H2.
  generalize (instr_size_positive a); omega.
  generalize (instr_size_positive a); omega.
Qed.

Lemma label_pos_repr:
  forall lbl c pos z,
    code_size c + pos <= Ptrofs.max_unsigned ->
    0 <= pos ->
    label_pos lbl pos c = Some z ->
    Ptrofs.unsigned (Ptrofs.repr (z - pos)) = z - pos.
Proof.
  intros.
  apply Ptrofs.unsigned_repr.
  generalize (label_pos_rng _ _ _ _ H1 H0). omega.
Qed.

Lemma find_instr_ofs_pos:
  forall c o i,
    find_instr o c = Some i ->
    0 <= o.
Proof.
  induction c; simpl; intros; repeat destr_in H.
  omega. apply IHc in H1. generalize (instr_size_positive a); omega.
Qed. 

Lemma label_pos_spec:
  forall lbl c pos z,
    code_size c + pos <= Ptrofs.max_unsigned ->
    0 <= pos ->
    label_pos lbl pos c = Some z ->
    find_instr ((z - pos) - instr_size (Plabel lbl)) c = Some (Plabel lbl).
Proof.
  induction c; simpl; intros; repeat destr_in H1. 
  destruct a; simpl in Heqb; try congruence. repeat destr_in Heqb.
  apply pred_dec_true. omega.
  eapply IHc in H3. 2: omega. 2: generalize (instr_size_positive a); omega.
  generalize (find_instr_ofs_pos _ _ _ H3). intro.
  rewrite pred_dec_false. 2: generalize (instr_size_positive a); omega.
  rewrite <- H3. f_equal. omega.
Qed.

End SACC_LABEL_POS.


(*SACC:*)
Section SACC_WITH_INIT_STK.

Variable init_stk: stack.

Definition init_sp : val := current_sp init_stk.

Variable ge: genv.

(** Evaluating an addressing mode *)

Definition eval_addrmode32 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.add  (match base with
             | None => Vint Int.zero
             | Some r => rs r
            end)
  (Val.add (match ofs with
             | None => Vint Int.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mul (rs r) (Vint (Int.repr sc))
             end)
           (match const with
            | inl ofs => Vint (Int.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode64 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.addl (match base with
             | None => Vlong Int64.zero
             | Some r => rs r
            end)
  (Val.addl (match ofs with
             | None => Vlong Int64.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mull (rs r) (Vlong (Int64.repr sc))
             end)
           (match const with
            | inl ofs => Vlong (Int64.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode (a: addrmode) (rs: regset) : val :=
  if Archi.ptr64 then eval_addrmode64 a rs else eval_addrmode32 a rs.

(** Performing a comparison *)

(** Integer comparison between x and y:
-       ZF = 1 if x = y, 0 if x != y
-       CF = 1 if x <u y, 0 if x >=u y
-       SF = 1 if x - y is negative, 0 if x - y is positive
-       OF = 1 if x - y overflows (signed), 0 if not
-       PF is undefined
*)

Definition compare_ints (x y: val) (rs: regset) (m: mem): regset :=
  rs #ZF  <- (Val.cmpu (Mem.valid_pointer m) Ceq x y)
     #CF  <- (Val.cmpu (Mem.valid_pointer m) Clt x y)
     #SF  <- (Val.negative (Val.sub x y))
     #OF  <- (Val.sub_overflow x y)
     #PF  <- Vundef.

Definition compare_longs (x y: val) (rs: regset) (m: mem): regset :=
  rs #ZF  <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq x y))
     #CF  <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt x y))
     #SF  <- (Val.negativel (Val.subl x y))
     #OF  <- (Val.subl_overflow x y)
     #PF  <- Vundef.

(** Floating-point comparison between x and y:
-       ZF = 1 if x=y or unordered, 0 if x<>y
-       CF = 1 if x<y or unordered, 0 if x>=y
-       PF = 1 if unordered, 0 if ordered.
-       SF and 0F are undefined
*)

Definition compare_floats (vx vy: val) (rs: regset) : regset :=
  match vx, vy with
  | Vfloat x, Vfloat y =>
      rs #ZF  <- (Val.of_bool (negb (Float.cmp Cne x y)))
         #CF  <- (Val.of_bool (negb (Float.cmp Cge x y)))
         #PF  <- (Val.of_bool (negb (Float.cmp Ceq x y || Float.cmp Clt x y || Float.cmp Cgt x y)))
         #SF  <- Vundef
         #OF  <- Vundef
  | _, _ =>
      undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs
  end.

Definition compare_floats32 (vx vy: val) (rs: regset) : regset :=
  match vx, vy with
  | Vsingle x, Vsingle y =>
      rs #ZF  <- (Val.of_bool (negb (Float32.cmp Cne x y)))
         #CF  <- (Val.of_bool (negb (Float32.cmp Cge x y)))
         #PF  <- (Val.of_bool (negb (Float32.cmp Ceq x y || Float32.cmp Clt x y || Float32.cmp Cgt x y)))
         #SF  <- Vundef
         #OF  <- Vundef
  | _, _ =>
      undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs
  end.

(** Testing a condition *)

Definition eval_testcond (c: testcond) (rs: regset) : option bool :=
  match c with
  | Cond_e =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_ne =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_b =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_be =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.one || Int.eq z Int.one)
      | _, _ => None
      end
  | Cond_ae =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_a =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.zero && Int.eq z Int.zero)
      | _, _ => None
      end
  | Cond_l =>
      match rs OF, rs SF with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.one)
      | _, _ => None
      end
  | Cond_le =>
      match rs OF, rs SF, rs ZF with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.one || Int.eq z Int.one)
      | _, _, _ => None
      end
  | Cond_ge =>
      match rs OF, rs SF with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.zero)
      | _, _ => None
      end
  | Cond_g =>
      match rs OF, rs SF, rs ZF with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.zero && Int.eq z Int.zero)
      | _, _, _ => None
      end
  | Cond_p =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_np =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]).
  [nextinstr_nf] is a variant of [nextinstr] that sets condition flags
  to [Vundef] in addition to incrementing the [PC]. *)

(**SACC: The manipulation of PC is parameterized by a mapping from 
    instructions to their actual sizes when compiled to machine-level bytes.
    It is used to calculated the changes of PC as in the machine code.
    It will be instantiated by the later phases of the transformation. *)

Definition nextinstr (rs: regset) ((*SACC:*)sz : ptrofs) :=
  rs#PC <- (Val.offset_ptr rs#PC (*SACC:*)sz).

Definition nextinstr_nf (rs: regset) ((*SACC:*) sz : ptrofs) : regset :=
  nextinstr (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs) (*SACC:*)sz.

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => (*SACC:*)
        match Genv.find_funct_ptr ge b with
        | Some _ => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
        | None => Stuck
        end
      | _ => Stuck
    end
  end.

(*SACC:*)
Definition goto_ofs (sz:ptrofs) (ofs:Z) (rs: regset) (m: mem) :=
  match rs#PC with
  | Vptr b o =>
    match Genv.find_funct_ptr ge b with
    | Some _ => Next (rs#PC <- (Vptr b (Ptrofs.add o (Ptrofs.add sz (Ptrofs.repr ofs))))) m
    | None => Stuck
    end
  | _ => Stuck
  end.

(** Auxiliaries for memory accesses. *)

Definition exec_load (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) ((*SACC:*)sz:ptrofs) :=
  match Mem.loadv chunk m (eval_addrmode a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v) (*SACC:*)sz) m
  | None => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) ((*SACC:*)sz : ptrofs):=
  match Mem.storev chunk m (eval_addrmode a rs) (rs r1) with
  | Some m' => Next (nextinstr_nf (undef_regs destroyed rs) (*SACC:*)sz) m'
  | None => Stuck
  end.

(*SACC: Monad notations*)

(** Error monad with options or lists  (stolen from cfronted/Cexec.v *)
Notation "'do' X <- A ; B" := (match A with Some X => B | None => Stuck end)
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => Stuck end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200).

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => Stuck end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200).

Notation " 'check' A ; B" := (if A then B else Stuck)
  (at level 200, A at level 100, B at level 200).

Section SACC_EXEC_HELPERS.

Lemma check_top_tc m : { top_tframe_tc (Mem.stack m) } + { ~ top_tframe_tc (Mem.stack m) }.
Proof.
  unfold top_tframe_tc.
  destruct (Mem.stack m) eqn:STK. right; intro A; inv A.
  destruct t.
  destruct o.
  right. intro A. inv A. inv H0.
  left; constructor. auto.
Defined.

Definition check_alloc_frame (f: frame_info) :=
  zlt 0 (frame_size f).

Definition match_frame (bfi: block * frame_info) (stk: option block) (sz: Z) : Prop :=
  match stk with Some stk => stk = fst bfi | _ => True end
  /\ sz = (frame_size (snd bfi)).

Lemma match_frame_dec : forall bfi stk sz,
    { match_frame bfi stk sz } + { ~ match_frame bfi stk sz }.
Proof.
  unfold match_frame. intros.
  destruct (zeq sz (frame_size (snd bfi))). 2: right; intros (A & B); omega.
  destruct stk; auto.
  destruct (peq b (fst bfi)); auto. right; intros (A & B). congruence.
Qed.

Definition check_top_frame (m: mem) (stk: option block) (sz: Z) :=
  match Mem.stack m with
    (Some fr,_)::r =>
    Forall_dec _ (fun bfi => match_frame_dec bfi stk sz) (frame_adt_blocks fr) && zeq sz (frame_adt_size fr)
  | _ => false
  end.

Local Open Scope list_scope.

Definition check_init_sp_in_stack (m: mem) :=
  match init_sp with
    Vptr b o => in_stack (Mem.stack m) b 
  | _ => True
  end.

Definition check_init_sp_in_stack_dec m : { check_init_sp_in_stack m } + { ~ check_init_sp_in_stack m }.
Proof.
  unfold check_init_sp_in_stack.
  destr.
  apply in_stack_dec.
Qed.

Inductive is_call: instruction -> Prop :=
| is_call_into:
    forall ros sg,
      is_call (Pcall ros sg).

Lemma is_call_dec:
  forall i,
    {is_call i} + {~ is_call i}.
Proof.
  destruct i; try now (right; intro A; inv A).
  left; econstructor; eauto.
Qed.

Fixpoint offsets_after_call (c: code) (p: Z) : list Z :=
  match c with
    nil => nil
  | i::c => let r := offsets_after_call c (p + instr_size i) in
           if is_call_dec i then (p+instr_size i)::r
           else r
  end.

Definition is_after_call (f: fundef) (o: Z) : Prop :=
  match f with
    Internal f => In o (offsets_after_call (fn_code f) 0)
  | External ef => False
  end.

Definition check_is_after_call f o : {is_after_call f o} + {~ is_after_call f o}.
Proof.
  unfold is_after_call.
  destruct f; auto.
  apply In_dec. apply zeq.
Qed.

Definition ra_after_call (ge: Genv.t fundef unit) v:=
  v <> Vundef /\ forall b o,
    v = Vptr b o ->
    forall f,
      Genv.find_funct_ptr ge b = Some f ->
      is_after_call f (Ptrofs.unsigned o).

Definition check_ra_after_call (ge': Genv.t fundef unit) v:
  {ra_after_call ge' v} + { ~ ra_after_call ge' v}.
Proof.
  unfold ra_after_call.
  destruct v; try now (left; split; intros; congruence).
  right; intuition congruence.
  destruct (Genv.find_funct_ptr ge' b) eqn:FFP.
  2: left; split; [congruence|]; intros b0 o A; inv A; rewrite FFP; congruence.
  destruct (check_is_after_call f (Ptrofs.unsigned i)).
  left. split. congruence. intros b0 o A; inv A; rewrite FFP; congruence.
  right; intros (B & A); specialize (A _ _ eq_refl _ FFP). congruence.
Defined.

Definition eval_ros (ge': genv) (ros: ireg + ident) (rs: regset) : val :=
  match ros with
  | inl r => rs r
  | inr symb => Genv.symbol_address ge' symb Ptrofs.zero
  end.

End SACC_EXEC_HELPERS.


(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual IA32 instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the IA32 reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the IA32 code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.

    Concerning condition flags, the comparison instructions set them
    accurately; other instructions (moves, [lea]) preserve them;
    and all other instruction set those flags to [Vundef], to reflect
    the fact that the processor updates some or all of those flags,
    but we do not need to model this precisely.
*)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  (*SACC:*)let sz := Ptrofs.repr (instr_size i) in
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) (*SACC:*)sz) m
  | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n)) (*SACC:*)sz) m
  | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n)) (*SACC:*)sz) m
  | Pmov_rs rd id =>
      Next (nextinstr_nf (rs#rd <- (Genv.symbol_address ge id Ptrofs.zero)) (*SACC:*)sz) m
  | Pmovl_rm rd a =>
      exec_load Mint32 m a rs rd (*SACC:*)sz
  | Pmovq_rm rd a =>
      exec_load Mint64 m a rs rd (*SACC:*)sz
  | Pmovl_mr a r1 =>
      exec_store Mint32 m a rs r1 nil (*SACC:*)sz
  | Pmovq_mr a r1 =>
      exec_store Mint64 m a rs r1 nil (*SACC:*)sz
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) (*SACC:*)sz) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n)) (*SACC:*)sz) m
  | Pmovsd_fm rd a =>
      exec_load Mfloat64 m a rs rd (*SACC:*)sz
  | Pmovsd_mf a r1 =>
      exec_store Mfloat64 m a rs r1 nil (*SACC:*)sz
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n)) (*SACC:*)sz) m
  | Pmovss_fm rd a =>
      exec_load Mfloat32 m a rs rd (*SACC:*)sz
  | Pmovss_mf a r1 =>
      exec_store Mfloat32 m a rs r1 nil (*SACC:*)sz
  | Pfldl_m a =>
      exec_load Mfloat64 m a rs ST0 (*SACC:*)sz
  | Pfstpl_m a =>
      exec_store Mfloat64 m a rs ST0 (ST0 :: nil) (*SACC:*)sz
  | Pflds_m a =>
      exec_load Mfloat32 m a rs ST0 (*SACC:*)sz
  | Pfstps_m a =>
      exec_store Mfloat32 m a rs ST0 (ST0 :: nil) (*SACC:*)sz
  (*SACC:*)
  | Pxchg_rr r1 r2 =>
      Next (nextinstr (rs#r1 <- (rs r2) #r2 <- (rs r1)) sz) m
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store Mint8unsigned m a rs r1 nil (*SACC:*)sz
  | Pmovw_mr a r1 =>
      exec_store Mint16unsigned m a rs r1 nil (*SACC:*)sz
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1)) (*SACC:*)sz) m
  | Pmovzb_rm rd a =>
      exec_load Mint8unsigned m a rs rd (*SACC:*)sz
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1)) (*SACC:*)sz) m
  | Pmovsb_rm rd a =>
      exec_load Mint8signed m a rs rd (*SACC:*)sz
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1)) (*SACC:*)sz) m
  | Pmovzw_rm rd a =>
      exec_load Mint16unsigned m a rs rd (*SACC:*)sz
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1)) (*SACC:*)sz) m
  | Pmovsw_rm rd a =>
      exec_load Mint16signed m a rs rd (*SACC:*)sz
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1)) (*SACC:*)sz) m
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1)) (*SACC:*)sz) m
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd)) (*SACC:*)sz) m
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1)) (*SACC:*)sz) m
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1)) (*SACC:*)sz) m
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1))) (*SACC:*)sz) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1))) (*SACC:*)sz) m
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1))) (*SACC:*)sz) m
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1))) (*SACC:*)sz) m
  | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1))) (*SACC:*)sz) m
  | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1))) (*SACC:*)sz) m
  | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1))) (*SACC:*)sz) m
  | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1))) (*SACC:*)sz) m
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 a rs)) (*SACC:*)sz) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 a rs)) (*SACC:*)sz) m
  | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd)) (*SACC:*)sz) m
  | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd)) (*SACC:*)sz) m
  | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n))) (*SACC:*)sz) m
  | Paddq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n))) (*SACC:*)sz) m
  (*SACC:*)
  | Psubl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd (Vint n))) sz) m
  (*SACC:*)
  | Psubq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd (Vlong n))) sz) m
  | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1)) (*SACC:*)sz) m
  | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1)) (*SACC:*)sz) m
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1)) (*SACC:*)sz) m
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1)) (*SACC:*)sz) m
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n))) (*SACC:*)sz) m
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n))) (*SACC:*)sz) m
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1)) (*SACC:*)sz) m
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1)) (*SACC:*)sz) m
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1)) (*SACC:*)sz) m
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1)) (*SACC:*)sz) m
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31)))) (*SACC:*)sz) m
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63)))) (*SACC:*)sz) m
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) (*SACC:*)sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) (*SACC:*)sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) (*SACC:*)sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) (*SACC:*)sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1)) (*SACC:*)sz) m
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1)) (*SACC:*)sz) m
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n))) (*SACC:*)sz) m
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n))) (*SACC:*)sz) m
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1)) (*SACC:*)sz) m
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1)) (*SACC:*)sz) m
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n))) (*SACC:*)sz) m
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n))) (*SACC:*)sz) m
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero) (*SACC:*)sz) m
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero)) (*SACC:*)sz) m
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1)) (*SACC:*)sz) m
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1)) (*SACC:*)sz) m 
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n))) (*SACC:*)sz) m
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n))) (*SACC:*)sz) m
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd)) (*SACC:*)sz) m
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd)) (*SACC:*)sz) m
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#RCX)) (*SACC:*)sz) m
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd rs#RCX)) (*SACC:*)sz) m
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n))) (*SACC:*)sz) m
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd (Vint n))) (*SACC:*)sz) m
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX)) (*SACC:*)sz) m
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX)) (*SACC:*)sz) m
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n))) (*SACC:*)sz) m
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n))) (*SACC:*)sz) m
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX)) (*SACC:*)sz) m
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX)) (*SACC:*)sz) m
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n))) (*SACC:*)sz) m
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n))) (*SACC:*)sz) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n))))) (*SACC:*)sz) m
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n))) (*SACC:*)sz) m
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n))) (*SACC:*)sz) m
  | Pcmpl_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m) (*SACC:*)sz) m
  | Pcmpq_rr r1 r2 =>
      Next (nextinstr (compare_longs (rs r1) (rs r2) rs m) (*SACC:*)sz) m
  | Pcmpl_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m) (*SACC:*)sz) m
  | Pcmpq_ri r1 n =>
      Next (nextinstr (compare_longs (rs r1) (Vlong n) rs m) (*SACC:*)sz) m
  | Ptestl_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m) (*SACC:*)sz) m
  | Ptestq_rr r1 r2 =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs m) (*SACC:*)sz) m
  | Ptestl_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m) (*SACC:*)sz) m
  | Ptestq_ri r1 n =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs m) (*SACC:*)sz) m
  | Pcmov c rd r1 =>
      match eval_testcond c rs with
      | Some true => Next (nextinstr (rs#rd <- (rs#r1)) (*SACC:*)sz) m
      | Some false => Next (nextinstr rs (*SACC:*)sz) m
      | None => Next (nextinstr (rs#rd <- Vundef) (*SACC:*)sz) m
      end
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs))) (*SACC:*)sz) m
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1)) (*SACC:*)sz) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1)) (*SACC:*)sz) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1)) (*SACC:*)sz) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1)) (*SACC:*)sz) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd)) (*SACC:*)sz) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd)) (*SACC:*)sz) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs) (*SACC:*)sz) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero)) (*SACC:*)sz) m
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1)) (*SACC:*)sz) m
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1)) (*SACC:*)sz) m
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1)) (*SACC:*)sz) m
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1)) (*SACC:*)sz) m
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd)) (*SACC:*)sz) m
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd)) (*SACC:*)sz) m
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs) (*SACC:*)sz) m
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vsingle Float32.zero)) (*SACC:*)sz) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label f lbl rs m
  (*SACC: comments this*)(*
  | Pjmp_s id sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmp_r r sg =>
      Next (rs#PC <- (rs r)) m*)
  (*SACC:*)
  | Pjmp ros sg =>
    let addr := eval_ros ge ros rs in
    match Genv.find_funct ge addr with
    | Some _ => Next (rs#PC <- addr) m
    | _ => Stuck
    end
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs (*SACC:*)sz) m
      | None => Stuck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label f lbl rs m
      | Some _, Some _ => Next (nextinstr rs (*SACC:*)sz) m
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  (*SACC: comments this*)(*
  | Pcall_s id sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pcall_r r sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (rs r)) m*)
  (*SACC:*)
  | Pcall ros sg =>
    let addr := eval_ros ge ros rs in
    match Genv.find_funct ge addr with
    | Some _ => Next (rs#RA <- (Val.offset_ptr rs#PC sz) #PC <- addr) (Mem.push_new_stage m)
    | _ => Stuck
    end
  | Pret =>
      (*Next (rs#PC <- (rs#RA)) m*)
  (*SACC:*)
    check (check_ra_after_call ge (rs#RA));
    check (check_top_tc m);
    do m' <- Mem.unrecord_stack_block m;
      Next (rs#PC <- (rs#RA) #RA <- Vundef) m'
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load (if Archi.ptr64 then Many64 else Many32) m a rs rd (*SACC:*)sz
  | Pmov_mr_a a r1 =>
      exec_store (if Archi.ptr64 then Many64 else Many32) m a rs r1 nil (*SACC:*)sz
  | Pmovsd_fm_a rd a =>
      exec_load Many64 m a rs rd (*SACC:*)sz
  | Pmovsd_mf_a a r1 =>
      exec_store Many64 m a rs r1 nil (*SACC:*)sz
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs (*SACC:*)sz) m
  | Pallocframe size ofs_ra (*SACC:*ofs_link*) =>
      check (check_top_tc m) ;
      let (m1, b) := Mem.alloc m 0 size in
      do m2 <- Mem.store Mptr m1 b (Ptrofs.unsigned ofs_ra) rs#RA;
      do m3 <- Mem.record_stack_blocks m2 (make_singleton_frame_adt b size size);
      Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- (Vptr b Ptrofs.zero)) sz) m3
  | Pfreeframe size ofs_ra (*SACC:ofs_link*) =>
      do ra <- Mem.loadbytesv Mptr m (Val.offset_ptr rs#RSP ofs_ra);
         match rs#RSP with
         | Vptr stk ofs =>
            check (check_top_frame m (Some stk) size);
            check (is_stack_top_dec (Mem.stack m) stk);
            do m' <- Mem.free m stk 0 size;
            do m' <- Mem.tailcall_stage m';
            check (check_init_sp_in_stack_dec m');
            do sp <- Mem.is_ptr (parent_sp (Mem.stack m));
            Next (nextinstr (rs#RSP <- sp #RA <- ra) sz) m'
          | _ => Stuck
          end
  (*SACC:*)
  | Pload_parent_pointer rd size =>
      check (check_top_frame m None size);
      check (Sumbool.sumbool_not _ _ (preg_eq rd RSP));
      do sp <- Mem.is_ptr (parent_sp (Mem.stack m));
      Next (nextinstr (rs#rd <- sp) sz) m
  (*SACC:*)
  | Pcfi_adjust n => Next rs m
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  (**SACC: Local jumps to relative offsets *)
  | Pjmp_l_rel ofs => goto_ofs sz ofs rs m
  | Pjcc_rel cond ofs =>
      match eval_testcond cond rs with
      | Some true => goto_ofs sz ofs rs m
      | Some false => Next (nextinstr rs sz) m
      | None => Stuck
      end
  | Pjcc2_rel cond1 cond2 ofs =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_ofs sz ofs rs m
      | Some _, Some _ => Next (nextinstr rs sz) m
      | _, _ => Stuck
      end
  | Pjmptbl_rel r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some ofs => goto_ofs sz ofs (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  (**SACC: Nop *)
  | Pnop => Next (nextinstr rs sz) m
  (** The following instructions and directives are not generated
      directly by [Asmgen], so we do not model them. *)
  | Padcl_ri _ _
  | Padcl_rr _ _
  | Paddl_mi _ _
  | Paddl_rr _ _
  | Pbsfl _ _
  | Pbsfq _ _
  | Pbsrl _ _
  | Pbsrq _ _
  | Pbswap64 _
  | Pbswap32 _
  | Pbswap16 _
  | Pfmadd132 _ _ _
  | Pfmadd213 _ _ _
  | Pfmadd231 _ _ _
  | Pfmsub132 _ _ _
  | Pfmsub213 _ _ _
  | Pfmsub231 _ _ _
  | Pfnmadd132 _ _ _
  | Pfnmadd213 _ _ _
  | Pfnmadd231 _ _ _
  | Pfnmsub132 _ _ _
  | Pfnmsub213 _ _ _
  | Pfnmsub231 _ _ _
  | Pmaxsd _ _
  | Pminsd _ _
  | Pmovb_rm _ _
  | Pmovsq_rm _ _
  | Pmovsq_mr _ _
  | Pmovsb
  | Pmovsw
  | Pmovw_rm _ _
  | Prep_movsl
  | Psbbl_rr _ _
  | Psqrtsd _ _
                       => Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the Asm view.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | AX => IR RAX
  | BX => IR RBX
  | CX => IR RCX
  | DX => IR RDX
  | SI => IR RSI
  | DI => IR RDI
  | BP => IR RBP
  | Machregs.R8 => IR R8
  | Machregs.R9 => IR R9
  | Machregs.R10 => IR R10
  | Machregs.R11 => IR R11
  | Machregs.R12 => IR R12
  | Machregs.R13 => IR R13
  | Machregs.R14 => IR R14
  | Machregs.R15 => IR R15
  | X0 => FR XMM0
  | X1 => FR XMM1
  | X2 => FR XMM2
  | X3 => FR XMM3
  | X4 => FR XMM4
  | X5 => FR XMM5
  | X6 => FR XMM6
  | X7 => FR XMM7
  | X8 => FR XMM8
  | X9 => FR XMM9
  | X10 => FR XMM10
  | X11 => FR XMM11
  | X12 => FR XMM12
  | X13 => FR XMM13
  | X14 => FR XMM14
  | X15 => FR XMM15
  | FP0 => ST0
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use machine registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr (rs (IR RSP)) (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' (*SACC:*)m'',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs RSP) m args vargs ->
      external_call ef ge vargs ((*SACC:*)Mem.push_new_stage m) t vres m' ->
  (*SACC:*)Mem.unrecord_stack_block m' = Some m'' ->
  (*SACC:*)(*no_rsp_builtin_preg res ->*)
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs))
               ((*SACC:*)Ptrofs.repr (instr_size (Pbuiltin ef args res))) ->
      step (State rs m) t (State rs' (*SACC:*)m'')
  | exec_step_external:
      forall b ef args res rs m t rs' m' (*SACC:*)m'',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      (*SACC:*)(*
       forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
        (RA_TYPE: Val.has_type (rs RA) Tptr)
        (SP_NOT_VUNDEF: rs RSP <> Vundef)
        (RA_NOT_VUNDEF: rs RA <> Vundef)
        (TIN: top_tframe_tc (Mem.stack m))*)
      (*SACC:*)(*
        no_rsp_pair (loc_external_result (ef_sig ef)) ->
        ra_after_call ge (rs#RA) ->*)
      external_call ef ge args m t res m' ->
  (*SACC:*)Mem.unrecord_stack_block m' = Some m'' ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res rs) #PC <- (rs RA) ->
  (*SACC:*)(*rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->*)
      step (State rs m) t (State rs' (*SACC:*)m'').

End SACC_WITH_INIT_STK.

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0 (*SACC:*)m2 (*SACC:*)bmain,
      Genv.init_mem p = Some m0 ->
  (*SACC:*)Mem.record_init_sp m0 = Some m2 ->
      let ge := Genv.globalenv p in
  (*SACC:*)Genv.find_symbol ge p.(prog_main) = Some bmain ->
      let rs0 := (*SACC:*)
        (Pregmap.init Vundef)
        # PC <- (Vptr bmain Ptrofs.zero)
        # RA <- Vnullptr
        # RSP <- (Vptr (Mem.nextblock m0) Ptrofs.zero) in
      initial_state p (State rs0 (Mem.push_new_stage m2)).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#RAX = Vint r ->
      final_state (State rs m) r.

Definition semantics ((*SACC:*)init_stk: stack) (p: program) :=
  Semantics (step (*SACC:*)init_stk) (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0. 
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall (*SACC:*)istk p, determinate (semantics p istk).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
+ split. constructor. auto.
+ discriminate.
+ discriminate.
+ assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H12. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto. congruence.
+ assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H4. eexact H10. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto. congruence.
- (* trace length *)
  red; intros; inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0.
  unfold rs0 , rs1, ge, ge0 in *.
  congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | PC => false
  | IR _ => true
  | FR _ => true
  | ST0 => true
  | CR _ => false
  | RA => false
  end.

