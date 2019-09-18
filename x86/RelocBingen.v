(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 18, 2019 *)
(* *******************  *)

Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import Asm RelocProgram RelocAsm RelocBin.
Require Import Hex Bits Memdata.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


(** * Encoding of instructions and initialization data *)

Definition encode_int_big (n:nat) (i: Z) : list byte :=
  rev (bytes_of_int n i).

Definition encode_int_little (n:nat) (i: Z) : list byte :=
  bytes_of_int n i.

Definition encode_int32 (i:Z) : list byte :=
  encode_int 4 i.

Definition n_zeros_bytes (n:nat) : list byte :=
  List.map (fun _ => Byte.zero) (seq 1 n).


(** * Encoding of instructions and functions *)

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


Definition encode_scale (s: Z) : res bits :=
  match s with
  | 1 => OK b["00"]
  | 2 => OK b["01"]
  | 4 => OK b["10"]
  | 8 => OK b["11"]
  | _ => Error (msg "Translation of scale failed")
  end.

(** ** Encoding of the address modes *)

(** Encode the address mode except the displacement *)
Definition encode_addrmode_aux (a: addrmode) (rd:ireg) : res (list byte) :=
  let '(Addrmode bs ss disp) := a in
  do rdbits <- encode_ireg rd;
  match ss, bs with
  | None, None =>
    (** No scale index and base register *)
    OK ([bB[b["00"] ++ rdbits ++ b["101"]]])

  | None, Some rb =>
    (** No scale index and with a base register *)
    do rbbits <- encode_ireg rb;
    if ireg_eq rb RSP then
    (** When the base register is RSP, an SIB byte for RSP following
    the ModR/M byte is needed *)
      let bits := b["10"] ++ rdbits ++ b["100"] ++
                  b["00"] ++ b["100"] ++ rbbits in
      OK (encode_int_big 2 (bits_to_Z bits))
    else
    (** Otherwise, no SIB byte is needed *)
      OK ([bB[b["10"] ++ rdbits ++ rbbits]])

  | Some (rs, scale), None =>
    if (ireg_eq rs RSP) then
      Error (msg "RSP cannot be the index of SIB")
    else
      (** With a scale and without a base register *)
      do scbits <- encode_scale scale;
      do rsbits <- encode_ireg rs;
      let bits := 
          b["00"] ++ rdbits ++ b["100"] ++
          scbits ++ rsbits ++ b["101"] in
      OK (encode_int_big 2 (bits_to_Z bits))

  | Some (rs, scale), Some rb =>
    if (ireg_eq rs RSP) then
      Error (msg "RSP cannot be the index of SIB")
    else    
      (** With a scale and a base register *)
      do scbits <- encode_scale scale;
      do rsbits <- encode_ireg rs;
      do rbbits <- encode_ireg rb;
      let bits := 
          b["10"] ++ rdbits ++ b["100"] ++
          scbits ++ rsbits ++ rbbits in
      OK (encode_int_big 2 (bits_to_Z bits))
  end.
    
(** Encode the full address mode *)
Definition encode_addrmode (a: addrmode) (rd: ireg) : res (list byte) :=
  let '(Addrmode bs ss disp) := a in
  do abytes <- encode_addrmode_aux a rd;
  let ofs := match disp with
             | inl ofs => ofs
             | inr _ => 0
             end in
  OK (abytes ++ (encode_int_little 4 ofs)).

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
Definition encode_instr (i: instruction) : res code :=
  match i with
  | Pjmp_l_rel ofs =>
    OK (HB["E9"] :: encode_int32 ofs)
  | Pjcc_rel c ofs =>
    let cbytes := encode_testcond c in
    OK (cbytes ++ encode_int32 ofs)
  | Pcall (inr id) _ =>
    OK (HB["E8"] :: n_zeros_bytes 4)
  | Pleal rd a =>
    do abytes <- encode_addrmode a rd;
    OK (HB["8D"] :: abytes)
  | Pxorl_r rd =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ rdbits ++ rdbits ] in
    OK (HB["31"] :: modrm :: nil)
  | Paddl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["000"] ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | Psubl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["101"] ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | Psubl_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits ] in
    OK (HB["2B"] :: modrm :: nil)
  | Pmovl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let opcode := bB[b["10111"] ++ rdbits] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (opcode :: nbytes)
  | Pmov_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits] in
    OK (HB["8B"] :: modrm :: nil)
  | Pmovl_rm rd a =>
    do abytes <- encode_addrmode a rd;
    OK (HB["8B"] :: abytes)
  | Pmovl_mr a rs =>
    do abytes <- encode_addrmode a rs;
    OK (HB["89"] :: abytes)
  | Pmov_rm_a rd a =>
    do abytes <- encode_addrmode a rd;
    OK (HB["8B"] :: abytes)    
  | Pmov_mr_a a rs =>
    do abytes <- encode_addrmode a rs;
    OK (HB["89"] :: abytes)
  | Ptestl_rr r1 r2 =>
    do r1bits <- encode_ireg r1;
    do r2bits <- encode_ireg r2;
    let modrm := bB[ b["11"] ++ r2bits ++ r1bits ] in
    OK (HB["85"] :: modrm :: nil)
  | Pret =>
    OK (HB["C3"] :: nil)
  | Pimull_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits ] in
    OK (HB["0F"] :: HB["AF"] :: modrm :: nil)
  | Pimull_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ rdbits ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["69"] :: modrm :: nbytes)
  | Pcmpl_rr r1 r2 =>
    do r1bits <- encode_ireg r1;
    do r2bits <- encode_ireg r2;
    let modrm := bB[ b["11"] ++ r2bits ++ r1bits ] in
    OK (HB["39"] :: modrm :: nil)
  | Pcmpl_ri r1 n =>
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ b["111"] ++ r1bits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | Pcltd =>
    OK (HB["99"] :: nil)
  | Pidivl r1 =>
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ b["110"] ++ r1bits ] in
    OK (HB["F7"] :: modrm :: nil)
  | Psall_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["100"] ++ rdbits ] in
    let nbytes := [Byte.repr (Int.unsigned n)] in
    OK (HB["C1"] :: modrm :: nbytes)
  | Fnop =>
    OK (HB["90"] :: nil)
  end.

Definition transl_instr' (ii: instr_with_info) : res code :=
  let '(i, sz) := ii in
  encode_instr i.


(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (instrs: list instr_with_info) : res code :=
  match instrs with
  | nil => OK nil
  | i::instrs' =>
    do instr <- transl_instr' i;
    do tinstrs' <- transl_instrs instrs';
    OK (instr ++ tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (f:RelocAsm.Prog.function) : res function :=
  do code' <- transl_instrs (RelocAsm.Prog.fn_code f);
  OK (mkfunction (RelocAsm.Prog.fn_sig f) code' 
                 (RelocAsm.Prog.fn_stacksize f) 
                 (RelocAsm.Prog.fn_pubrange f)).

Definition transf_fundef (f:RelocAsm.Prog.fundef) : res fundef :=
  match f with
  | External ef => OK (External ef)
  | Internal f =>  
    do f' <- transl_fun f;
    OK (Internal f')
  end.
    

(** ** Encoding of data *)

Definition transl_init_data (d:init_data) : res (list byte) :=
  match d with
  | Init_int8 i => OK [Byte.repr (Int.unsigned i)]
  | Init_int16 i => OK (encode_int 2 (Int.unsigned i))
  | Init_int32 i => OK (encode_int 4 (Int.unsigned i))
  | Init_int64 i => OK (encode_int 8 (Int64.unsigned i))
  | Init_float32 f => OK (encode_int 4 (Int64.unsigned (Float.to_bits (Float.of_single f))))
  | Init_float64 f => OK (encode_int 4 (Int64.unsigned (Float.to_bits f)))
  | Init_space n => OK (n_zeros_bytes (nat_of_Z n))
  | Init_addrof id ofs => OK (n_zeros_bytes 4)
  end.

Definition transl_init_data_list (l: list init_data) : res (list byte) :=
  fold_right (fun d r =>
                do rbytes <- r;
                do dbytes <- transl_init_data d;
                OK (dbytes ++ rbytes))
             (OK []) l.

(** Translation of global variables *)
Definition transf_globvar (gv:RelocAsm.globvar) : res globvar :=
  do bytes <- transl_init_data_list (gvar_init gv);
  let info :=  match gvar_info gv with
               | None => None
               | Some slbl => Some (slbl, bytes)
               end in
  OK (mkglobvar info (gvar_init gv) (gvar_readonly gv) (gvar_volatile gv)).
  
Definition transf_globdef (def: (ident * option RelocAsm.Prog.gdef))
  : res (ident * option gdef) :=
  let '(id,def) := def in
  match def with
  | Some (AST.Gfun f) =>
    do f' <- transf_fundef f;
    OK (id, Some (AST.Gfun f'))
  | Some (AST.Gvar v) =>
    do v' <- transf_globvar v;
    OK (id, Some (AST.Gvar v'))
  | None => OK (id, None)
  end.

Fixpoint transf_globdefs defs :=
  fold_right (fun def r =>
                do defs <- r;
                do def' <- transf_globdef def;
                OK (def' :: defs))
             (OK []) defs.

(** Translation of a program *)
Definition transf_program (p:RelocAsm.Prog.program) : res program := 
  do defs <- transf_globdefs (RelocAsm.Prog.prog_defs p);
  OK {| prog_defs := defs;
        prog_public := RelocAsm.Prog.prog_public p;
        prog_main := RelocAsm.Prog.prog_main p;
        prog_sectable := RelocAsm.Prog.prog_sectable p;
        prog_symbtable := RelocAsm.Prog.prog_symbtable p;
        prog_reloctables := RelocAsm.Prog.prog_reloctables p;
        prog_senv := RelocAsm.Prog.prog_senv p;
     |}.

