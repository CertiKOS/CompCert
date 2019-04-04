Require Import Coqlib Integers AST Maps.
Require Import Asm MC Segment.
Require Import Errors.
Require Import FlatAsmBuiltin.
Require Import Memtype.
Require Import FlatAsmProgram FlatMCProgram FlatMC FlatBinary.
Require Import Hex Bits Memdata.
Import ListNotations.
Import Hex Bits.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(** * Encoding of instructions *)
Definition encode_int32 (i: Z) : list byte :=
  encode_int 4 i.


Definition encode_ireg (r: ireg) : res bits :=
  match r with
  | RAX => OK (b["000"])
  | RCX => OK (b["001"])
  | RDX => OK (b["010"])
  | RBX => OK (b["011"])
  | RSP => OK (b["100"])
  | RBP => OK (b["101"])
  | RSI => OK (b["110"])
  | RDI => OK (b["111"])
  | _ => Error (msg "Encoding of register not supported")
  end.

Definition encode_scale (s: scale) : bits :=
  match s with
  | Scale1 => b["00"]
  | Scale2 => b["01"]
  | Scale4 => b["10"]
  | Scale8 => b["11"]
  end.

(** ** Encoding of the address modes *)

(** Encode the address mode except the displacement *)
Definition encode_addrmode_aux (a: addrmode) (rd:ireg) : res bits :=
  let '(Addrmode bs ss disp) := a in
  do rdbits <- encode_ireg rd;
  match ss, bs with
  | None, None =>
    (** No scale index and base register *)
    OK (b["00"] ++ rdbits ++ b["101"])

  | None, Some rb =>
    (** No scale index and with a base register *)
    do rbbits <- encode_ireg rb;
    if ireg_eq rb RSP then
    (** When the base register is RSP, an SIB byte for RSP following
    the ModR/M byte is needed *)
      OK (b["10"] ++ rdbits ++ b["100"] ++
          b["00"] ++ b["100"] ++ rbbits)
    else
    (** Otherwise, no SIB byte is needed *)
      OK (b["10"] ++ rdbits ++ rbbits)

  | Some (rs, scale), None =>
    (** With a scale and without a base register *)
    let scbits := encode_scale scale in
    do rsbits <- encode_ireg rs;
    OK (b["00"] ++ rdbits ++ b["100"] ++
        scbits ++ rsbits ++ b["101"])

  | Some (rs, scale), Some rb =>
    (** With a scale and a base register *)
    let scbits := encode_scale scale in
    do rsbits <- encode_ireg rs;
    do rbbits <- encode_ireg rb;
    OK (b["10"] ++ rdbits ++ b["100"] ++
        scbits ++ rsbits ++ rbbits)
  end.
    
(** Encode the full address mode *)
Definition encode_addrmode (a: addrmode) (rd: ireg) : res (list byte) :=
  let '(Addrmode bs ss disp) := a in
  do bits <- encode_addrmode_aux a rd;
  let abytes := encode_int32 (bits_to_Z bits) in
  OK (abytes ++ (encode_int32 (Ptrofs.unsigned disp))).

(** Encode the conditions *)
Definition encode_testcond (c:testcond) : list byte :=
  match c with
  | Cond_e   => HB["0F"] :: HB["84"] :: nil
  | Cond_ne  => HB["0F"] :: HB["85"] :: nil
  | Cond_b   => HB["0F"] :: HB["82"] :: nil
  | Cond_be  => HB["0F"] :: HB["86"] :: nil
  | Cond_ae  => HB["0F"] :: HB["83"] :: nil
  | Cond_a   => HB["0F"] :: HB["87"] :: nil
  | Cond_l   => HB["0F"] :: HB["8C"] :: nil
  | Cond_le  => HB["0F"] :: HB["8E"] :: nil
  | Cond_ge  => HB["0F"] :: HB["8D"] :: nil
  | Cond_g   => HB["0F"] :: HB["8F"] :: nil
  | Cond_p   => HB["0F"] :: HB["8A"] :: nil
  | Cond_np  => HB["0F"] :: HB["8B"] :: nil
  end.

(** Encode a single instruction *)
Definition fmc_instr_encode (i: FlatMC.instruction) : res FlatBinary.instruction :=
  match i with
  | FMCjmp_l ofs =>
    OK (HB["E9"] :: encode_int32 (Ptrofs.unsigned ofs))
  | FMCjcc c ofs =>
    let cbytes := encode_testcond c in
    OK (cbytes ++ encode_int32 (Ptrofs.unsigned ofs))
  | FMCshortcall ofs _ =>
    OK (HB["E8"] :: encode_int32 (Ptrofs.unsigned ofs))
  | FMCleal rd a =>
    do abytes <- encode_addrmode a rd;
    OK (HB["8D"] :: abytes)
  | FMCxorl_r rd =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ rdbits ++ rdbits ] in
    OK (HB["31"] :: modrm :: nil)
  | FMCaddl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["000"] ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | FMCsubl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["101"] ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | FMCsubl_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits ] in
    OK (HB["2B"] :: modrm :: nil)
  | FMCmovl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let opcode := bB[b["10111"] ++ rdbits] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (opcode :: nbytes)
  | FMCmov_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits] in
    OK (HB["8B"] :: modrm :: nil)
  | FMCmovl_rm rd a =>
    do abytes <- encode_addrmode a rd;
    OK (HB["8B"] :: abytes)
  | FMCmovl_mr a rs =>
    do abytes <- encode_addrmode a rs;
    OK (HB["89"] :: abytes)
  | FMCmov_rm_a rd a =>
    do abytes <- encode_addrmode a rd;
    OK (HB["8B"] :: abytes)    
  | FMCmov_mr_a a rs =>
    do abytes <- encode_addrmode a rs;
    OK (HB["89"] :: abytes)
  | FMCtestl_rr r1 r2 =>
    do r1bits <- encode_ireg r1;
    do r2bits <- encode_ireg r2;
    let modrm := bB[ b["11"] ++ r2bits ++ r1bits ] in
    OK (HB["85"] :: modrm :: nil)
  | FMCret =>
    OK (HB["C3"] :: nil)
  | FMCimull_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits ] in
    OK (HB["0F"] :: HB["AF"] :: modrm :: nil)
  | FMCimull_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ rdbits ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["69"] :: modrm :: nbytes)
  | FMCcmpl_rr r1 r2 =>
    do r1bits <- encode_ireg r1;
    do r2bits <- encode_ireg r2;
    let modrm := bB[ b["11"] ++ r2bits ++ r1bits ] in
    OK (HB["39"] :: modrm :: nil)
  | FMCcmpl_ri r1 n =>
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ b["111"] ++ r1bits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | FMCcltd =>
    OK (HB["99"] :: nil)
  | FMCidivl r1 =>
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ b["110"] ++ r1bits ] in
    OK (HB["F7"] :: modrm :: nil)
  | FMCsall_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["100"] ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["C1"] :: modrm :: nbytes)
  | FMCnop =>
    OK (HB["90"] :: nil)
  end.

Definition transl_instr' (ii: FlatMC.instr_with_info) : res instruction :=
  let '(i, sz) := ii in
  fmc_instr_encode i.


(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (instrs: list FlatMC.instr_with_info) : res (list instruction) :=
  match instrs with
  | nil => OK nil
  | i::instrs' =>
    do instr <- transl_instr' i;
    do tinstrs' <- transl_instrs instrs';
    OK (instr :: tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (f:@FlatMCProgram.function FlatMC.instr_with_info) : res function :=
  do code' <- transl_instrs (FlatMCProgram.fn_code f);
  OK (mkfunction (FlatMCProgram.fn_sig f) code').

Definition transl_globdef (def: (ident * option (@FlatMCProgram.gdef FlatMC.instr_with_info)) )
  : res (ident * option (@FlatMCProgram.gdef instruction)) :=
  let '(id,def) := def in
  match def with
  | Some (AST.Gfun (Internal f)) =>
    do f' <- transl_fun f;
      OK (id, Some (AST.Gfun (Internal f')))
  | Some (AST.Gfun (External f)) => 
    OK (id, Some (AST.Gfun (External f)))
  | Some (AST.Gvar v) =>
    OK (id, Some (AST.Gvar v))
  | None => OK (id, None)
  end.

Fixpoint transl_globdefs defs :=
  match defs with
  | nil => OK nil
  | def::defs' =>
    do tdef <- transl_globdef def;
    do tdefs' <- transl_globdefs defs';
    OK (tdef :: tdefs')
  end.


(** Translation of a program *)
Definition transf_program (p:FlatMC.program) : res program := 
  do defs <- transl_globdefs (FlatMCProgram.prog_defs p);
  OK (Build_program
        defs
        (prog_public p)
        (prog_main p)
        (prog_main_ofs p)
        (prog_data_addr p)
        (prog_data_size p)
        (prog_code_addr p)
        (prog_code_size p))
      .