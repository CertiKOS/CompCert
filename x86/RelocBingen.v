(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 18, 2019 *)
(* *******************  *)

(* *******************  *)
(* Modify: Xiangzhe Xu  *)
(* Date:   Oct 09, 2019 *)
(* *******************  *)


Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import Asm RelocProgram.
Require Import Hex Bits Memdata Encode SeqTable.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


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

Definition encode_freg (r: freg) : res bits :=
  match r with
  | XMM0 => OK (b["000"])
  | XMM1 => OK (b["001"])
  | XMM2 => OK (b["010"])
  | XMM3 => OK (b["011"])
  | XMM4 => OK (b["100"])
  | XMM5 => OK (b["101"])
  | XMM6 => OK (b["110"])
  | XMM7 => OK (b["111"])
  | _ => Error (msg "Unsupported freg")
  end.

Definition encode_scale (s: Z) : res bits :=
  match s with
  | 1 => OK b["00"]
  | 2 => OK b["01"]
  | 4 => OK b["10"]
  | 8 => OK b["11"]
  | _ => Error (msg "Translation of scale failed")
  end.

Section WITH_RELOC_TABLE.

Variable rtbl: reloctable.

Definition get_reloc_addend (rid:ident) : res Z :=
  match SeqTable.get (RelocIndex.interp rid) rtbl with
  | None => Error [MSG "Cannot find the relocation entry "; POS rid]
  | Some e => OK (reloc_addend e)
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
  do ofs <- match disp with
           | inl ofs => OK ofs
           | inr (id,_) => get_reloc_addend id
           end;
  OK (abytes ++ (encode_int32 ofs)).

Definition encode_addrmode_aux_f (a: addrmode) (frd:freg) : res (list byte) :=
  let '(Addrmode bs ss disp) := a in
  do rdbits <- encode_freg frd;
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
    

Definition encode_addrmode_f (a: addrmode) (frd: freg) : res (list byte) :=
  let '(Addrmode bs ss disp) := a in
  do abytes <- encode_addrmode_aux_f a frd;
  do ofs <- match disp with
           | inl ofs => OK ofs
           | inr (id,_) => get_reloc_addend id
           end;
  OK (abytes ++ (encode_int32 ofs)).


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

Definition encode_testcond_cmov (c:testcond) : list byte :=
  match c with
  | Cond_e   => HB["0F"] :: HB["44"] :: nil
  | Cond_ne  => HB["0F"] :: HB["45"] :: nil
  | Cond_b   => HB["0F"] :: HB["42"] :: nil
  | Cond_be  => HB["0F"] :: HB["46"] :: nil
  | Cond_ae  => HB["0F"] :: HB["43"] :: nil
  | Cond_a   => HB["0F"] :: HB["47"] :: nil
  | Cond_l   => HB["0F"] :: HB["4C"] :: nil
  | Cond_le  => HB["0F"] :: HB["4E"] :: nil
  | Cond_ge  => HB["0F"] :: HB["4D"] :: nil
  | Cond_g   => HB["0F"] :: HB["4F"] :: nil
  | Cond_p   => HB["0F"] :: HB["4A"] :: nil
  | Cond_np  => HB["0F"] :: HB["4B"] :: nil
  end.

Definition encode_testcond_setcc (c:testcond) : list byte :=
  match c with
  | Cond_e   => HB["0F"] :: HB["94"] :: nil
  | Cond_ne  => HB["0F"] :: HB["95"] :: nil
  | Cond_b   => HB["0F"] :: HB["92"] :: nil
  | Cond_be  => HB["0F"] :: HB["96"] :: nil
  | Cond_ae  => HB["0F"] :: HB["93"] :: nil
  | Cond_a   => HB["0F"] :: HB["97"] :: nil
  | Cond_l   => HB["0F"] :: HB["9C"] :: nil
  | Cond_le  => HB["0F"] :: HB["9E"] :: nil
  | Cond_ge  => HB["0F"] :: HB["9D"] :: nil
  | Cond_g   => HB["0F"] :: HB["9F"] :: nil
  | Cond_p   => HB["0F"] :: HB["9A"] :: nil
  | Cond_np  => HB["0F"] :: HB["9B"] :: nil
  end.
(** Encode a single instruction *)
Definition encode_instr (i: instruction) : res (list byte) :=
  match i with
  | Pjmp_l_rel ofs =>
    OK (HB["E9"] :: encode_int32 ofs)
  | Pjcc_rel c ofs =>
    let cbytes := encode_testcond c in
    OK (cbytes ++ encode_int32 ofs)
  | Pcall (inr id) _ =>
    do addend <- get_reloc_addend id;
      OK (HB["E8"] :: encode_int32 addend)
  | Pcall (inl reg) _ =>
    do rm <- encode_ireg reg;
      (* reg filed must be 2 *)
      let modrm := bB[b["11"] ++ b["010"] ++ rm] in
      OK (HB["FF"] :: modrm :: nil)
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
  (* movs *)
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
  | Pmov_rs rd id =>
    do abytes <- encode_addrmode (Addrmode None None (inr (id,Ptrofs.zero))) rd;
    OK (HB["8B"] :: abytes)  
  | Pmovsd_ff frd fr1 =>
    do bfrd <- encode_freg frd;
      do bfr1 <- encode_freg fr1;
      OK (HB["F2"] :: HB["0F"] :: HB["10"] :: bB[b["11"] ++ bfrd ++ bfr1]::nil)
  | Pmovsd_fm_a frd a
  | Pmovsd_fm frd a =>
    do abytes <- encode_addrmode_f a frd;
      OK(HB["F2"] :: HB["0F"] :: HB["10"] :: abytes)
  | Pmovsd_mf_a a fr1
  | Pmovsd_mf a fr1 =>
    do abytes <- encode_addrmode_f a fr1;
      OK(HB["F2"] :: HB["0F"] :: HB["11"] :: abytes)
  | Pmovss_fm frd a =>
    do abytes <- encode_addrmode_f a frd;
      OK(HB["F3"] :: HB["0F"] :: HB["10"] :: abytes)
  | Pmovss_mf a fr1 =>
    do abytes <- encode_addrmode_f a fr1;
      OK(HB["F3"] :: HB["0F"] :: HB["11"] :: abytes)
  | Pfldl_m a =>
    (* the rd bits must be 000 *)
    do abytes <- encode_addrmode_f a XMM0;
      OK(HB["DD"] :: abytes)
  | Pfstpl_m a =>
    (* the rd bits must be 002 *)
    do abytes <- encode_addrmode_f a XMM2;
      OK(HB["DD"] :: abytes)
  | Pflds_m a =>
    (* the rd bits must be 000 *)
    do abytes <- encode_addrmode_f a XMM0;
      OK(HB["D9"] :: abytes)
  | Pfstps_m a =>
    (* the rd bits must be 002 *)
    do abytes <- encode_addrmode_f a XMM2;
      OK(HB["D9"] :: abytes)
  | Pxchg_rr r1 r2 =>
    do rm <- encode_ireg r1;
    do reg <- encode_ireg r2;
    OK(HB["87"] :: bB[b["11"] ++ reg ++ rm] :: nil)
  | Pmovb_mr a rs =>
    do abytes <- encode_addrmode a rs;
      OK(HB["88"] :: abytes)
  | Pmovw_mr a rs =>
    do abytes <- encode_addrmode a rs;
      OK(HB["66"] :: HB["89"] :: abytes)
  | Pmovzb_rr rd rs =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg rs;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK (HB["0F"] :: HB["B6"] :: modrm ::nil)
  | Pmovzb_rm rd a =>
    do abytes <- encode_addrmode a rd;
      OK (HB["0F"] :: HB["B6"] :: abytes)
  | Pmovzw_rr rd rs =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg rs;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK (HB["0F"] :: HB["B7"] :: modrm ::nil)
  | Pmovzw_rm rd a =>
    do abytes <- encode_addrmode a rd;
      OK (HB["0F"] :: HB["B7"] :: abytes)
  | Pmovsb_rr rd rs =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg rs;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK (HB["0F"] :: HB["BE"] :: modrm ::nil)
  | Pmovsb_rm rd a =>
    do abytes <- encode_addrmode a rd;
      OK (HB["0F"] :: HB["BE"] :: abytes)
  | Pmovsw_rr rd rs =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg rs;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK (HB["0F"] :: HB["BF"] :: modrm ::nil)
  | Pmovsw_rm rd a =>
    do abytes <- encode_addrmode a rd;
      OK (HB["0F"] :: HB["BF"] :: abytes)
  | Pcvtsd2ss_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F2"] :: HB["0F"] :: HB["5A"] :: modrm ::nil)      
  | Pcvtss2sd_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F3"] :: HB["0F"] :: HB["5A"] :: modrm ::nil)
  | Pcvttsd2si_rf rd fr1 =>
    do reg <- encode_ireg rd;
      do rm <- encode_freg fr1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F2"] :: HB["0F"] :: HB["2D"] :: modrm ::nil)
  | Pcvtsi2sd_fr frd r1 =>
    do reg <- encode_freg frd;
      do rm <- encode_ireg r1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F2"] :: HB["0F"] :: HB["2A"] :: modrm ::nil)
  | Pcvttss2si_rf rd fr1 =>
    do reg <- encode_ireg rd;
      do rm <- encode_freg fr1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F3"] :: HB["0F"] :: HB["2D"] :: modrm ::nil)
  | Pcvtsi2ss_fr frd r1 =>
    do reg <- encode_freg frd;
      do rm <- encode_ireg r1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F3"] :: HB["0F"] :: HB["2A"] :: modrm ::nil)
  | Pnegl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 3 *)
      let modrm := bB[b["11"] ++ b["011"] ++ rm] in
      OK(HB["F6"] :: modrm :: nil)
  | Pimull_r r1 =>
    do rm <- encode_ireg r1;
      (* reg field must be 5 *)
      let modrm := bB[b["11"] ++ b["101"] ++ rm] in
      OK(HB["F7"] :: modrm :: nil)
  | Pmull_r r1 =>
    do rm <- encode_ireg r1;
      (* reg field must be 4 *)
      let modrm := bB[b["11"] ++ b["100"] ++ rm] in
      OK(HB["F7"] :: modrm :: nil)
  | Pdivl r1 =>
    do rm <- encode_ireg r1;
      (* reg field must be 6 *)
      let modrm := bB[b["11"] ++ b["110"] ++ rm] in
      OK(HB["F7"] :: modrm :: nil)
  | Pandl_rr rd r1  =>
    do reg <- encode_ireg r1;
      do rm <- encode_ireg rd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["21"] :: modrm :: nil)
  | Pandl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 4 *)
      let modrm := bB[b["11"] ++ b["100"] ++ rm] in
      OK(HB["81"] :: modrm :: encode_int32 (Int.unsigned n))
  | Porl_rr rd r1 =>
    do reg <- encode_ireg r1;
      do rm <- encode_ireg rd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["09"] :: modrm :: nil)
  | Porl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 1 *)
      let modrm := bB[b["11"] ++ b["001"] ++ rm] in
      OK(HB["81"] :: modrm :: encode_int32 (Int.unsigned n))
  | Pxorl_rr rd r1 =>
    do reg <- encode_ireg r1;
      do rm <- encode_ireg rd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["31"] :: modrm :: nil)
  | Pxorl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 6 *)
      let modrm := bB[b["11"] ++ b["110"] ++ rm] in
      OK(HB["81"] :: modrm :: encode_int32 (Int.unsigned n))
  | Pnotl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 2 *)
      let modrm := bB[b["11"] ++ b["010"] ++ rm] in
      OK(HB["F7"] :: modrm :: nil)
  | Psall_rcl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 4 *)
      let modrm := bB[b["11"] ++ b["100"] ++ rm] in
      OK(HB["D3"] :: modrm :: nil)
  | Pshrl_rcl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 5 *)
      let modrm := bB[b["11"] ++ b["101"] ++ rm] in
      OK(HB["D3"] :: modrm :: nil)
  | Pshrl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 5 *)
      let modrm := bB[b["11"] ++ b["101"] ++ rm] in
      OK(HB["C1"] :: modrm :: (encode_int 1 (Int.unsigned n)))
  | Psarl_rcl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 7 *)
      let modrm := bB[b["11"] ++ b["111"] ++ rm] in
      OK(HB["D3"] :: modrm :: nil)
  | Psarl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 7 *)
      let modrm := bB[b["11"] ++ b["111"] ++ rm] in
      OK(HB["C1"] :: modrm :: (encode_int 1 (Int.unsigned n)))
  | Pshld_ri rd r1 n =>
    do reg <- encode_ireg r1;
      do rm <- encode_ireg rd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["0F"] :: HB["A4"] :: modrm :: (encode_int 1 (Int.unsigned n)))
  | Prorl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 1 *)
      let modrm := bB[b["11"] ++ b["001"] ++ rm] in
      OK(HB["C1"] :: modrm :: (encode_int 1 (Int.unsigned n)))
  | Ptestl_ri r1 n =>
    do rm <- encode_ireg r1;
      (* reg field must be 0 *)
      let modrm := bB[b["11"] ++ b["000"] ++ rm] in
      OK(HB["F7"] :: modrm :: encode_int32 (Int.unsigned n))
  | Pcmov c rd r1 =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg r1;
      let cc := encode_testcond_cmov c in
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(cc ++ modrm :: nil)
  | Psetcc c rd =>
    do rm <- encode_ireg rd;
      let cc := encode_testcond_cmov c in
      (* reg field is not used *)
      let modrm := bB[b["11"] ++ b["000"] ++ rm] in
      OK(cc ++ modrm :: nil)
  | Paddd_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F2"] :: HB["0F"] :: HB["58"] :: modrm :: nil)
  | Padds_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F3"] :: HB["0F"] :: HB["58"] :: modrm :: nil)
  | Psubd_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F2"] :: HB["0F"] :: HB["5C"] :: modrm :: nil)
  | Psubs_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F3"] :: HB["0F"] :: HB["5C"] :: modrm :: nil)
  | Pmuld_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F2"] :: HB["0F"] :: HB["59"] :: modrm :: nil)
  | Pmuls_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F3"] :: HB["0F"] :: HB["59"] :: modrm :: nil)
  | Pdivd_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F2"] :: HB["0F"] :: HB["5E"] :: modrm :: nil)
  | Pdivs_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F3"] :: HB["0F"] :: HB["5E"] :: modrm :: nil)
  | Pnegd frd
  | Pnegs frd 
  | Pabsd frd
  | Pabss frd =>
    Error (msg "pseduo instruction Pnegd")
  | Pcomisd_ff fr1 fr2 =>
    do reg <- encode_freg fr1;
      do rm <- encode_freg fr2;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["66"] :: HB["0F"] :: HB["2F"] :: modrm :: nil)
  | Pcomiss_ff fr1 fr2 =>
    do reg <- encode_freg fr1;
      do rm <- encode_freg fr2;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["0F"] :: HB["2F"] :: modrm :: nil)
  | Pxorpd_f frd =>
    do reg <- encode_freg frd;
      do rm <- encode_freg frd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["66"] :: HB["0F"] :: HB["57"] :: modrm :: nil)
  | Pxorps_f frd =>
    do reg <- encode_freg frd;
      do rm <- encode_freg frd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["0F"] :: HB["57"] :: modrm :: nil)
  | Pjmp (inr id) sg =>
    do addend <- get_reloc_addend id;
      OK (HB["E9"] :: encode_int32 addend)
  | Pjmp (inl reg) sg =>
    do rm <- encode_ireg reg;
      (* reg field must be 4 *)
      let modrm := bB[b["11"] ++ b["100"] ++ rm] in
      OK(HB["FF"] :: modrm :: nil)      
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
      (* reg must be 7 *)
      let modrm := bB[ b["11"] ++ b["111"] ++ r1bits ] in
      OK (HB["F7"] :: modrm :: nil)
  | Psall_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["100"] ++ rdbits ] in
    let nbytes := [Byte.repr (Int.unsigned n)] in
    OK (HB["C1"] :: modrm :: nbytes)
  | Plabel _
  | Pnop =>
    OK (HB["90"] :: nil)
  | _ =>
    Error [MSG "Encoding of the instruction is not supported yet: ";
           MSG (instr_to_string i)]
  end.

Definition acc_instrs i r := 
  do code <- r;
  do c <- encode_instr i;
  OK (c ++ code).

(** Translation of a sequence of instructions in a function *)
Definition transl_code (c:code) : res (list byte) :=
  fold_right acc_instrs (OK []) c.


(** ** Encoding of data *)

Definition transl_init_data (d:init_data) : res (list byte) :=
  match d with
  | Init_int8 i => OK [Byte.repr (Int.unsigned i)]
  | Init_int16 i => OK (encode_int 2 (Int.unsigned i))
  | Init_int32 i => OK (encode_int 4 (Int.unsigned i))
  | Init_int64 i => OK (encode_int 8 (Int64.unsigned i))
  | Init_float32 f => OK (encode_int 4 (Int.unsigned (Float32.to_bits f)))
  | Init_float64 f => OK (encode_int 8 (Int64.unsigned (Float.to_bits f)))
  | Init_space n => OK (zero_bytes (nat_of_Z n))
  | Init_addrof id ofs => 
    do addend <- get_reloc_addend id;
    OK (encode_int32 addend)
  end.

Definition acc_init_data d r := 
  do rbytes <- r;
  do dbytes <- transl_init_data d;
  OK (dbytes ++ rbytes).

Definition transl_init_data_list (l: list init_data) : res (list byte) :=
  fold_right acc_init_data (OK []) l.

End WITH_RELOC_TABLE.

(** ** Translation of a program *)

Definition transl_section (sec:section) (rtbl:option reloctable) : res section :=
  match sec with
  | sec_text code =>
    match rtbl with
    | None => Error [MSG "Encoding failed: No relocation table found for .text section"]
    | Some rtbl => 
      do bytes <- transl_code rtbl code;
      OK (sec_bytes bytes)
    end
  | sec_data l =>
    match rtbl with
    | None => Error [MSG "Encoding failed: No relocation table found for .data section"]
    | Some rtbl => 
      do bytes <- transl_init_data_list rtbl l;
      OK (sec_bytes bytes)
    end
  | _ => OK sec
  end.

Definition acc_sections rtbls r sec := 
  do r' <- r;
  let '(stbl,si) := r' in
  match SecIndex.deinterp si with
  | None => OK (sec :: stbl, N.succ si)
  | Some sec_index =>
    do sec' <- transl_section sec (PTree.get sec_index rtbls);
    OK (sec' :: stbl, N.succ si)
  end.

Definition transl_sectable (stbl: sectable) (rtbls: PTree.t reloctable) : res sectable :=
  do r <- 
     fold_left (acc_sections rtbls)
     stbl
     (OK ([],0%N));
  let '(stbl', _) := r in
  OK (rev stbl').

Definition transf_program (p:program) : res program := 
  do stbl <- transl_sectable (prog_sectable p) (prog_reloctables p);
  OK {| prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := stbl;
        prog_strtable := prog_strtable p;
        prog_symbtable := prog_symbtable p;
        prog_reloctables := prog_reloctables p;
        prog_senv := prog_senv p;
     |}.

