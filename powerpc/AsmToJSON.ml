(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(* Simple functions to serialize powerpc Asm to JSON *)

open Asm
open AST
open BinNums
open C2C
open Camlcoq
open Json
open Format
open Sections

let pp_reg pp t n =
  let s = sprintf "%s%s" t n in
  pp_jsingle_object pp "Register" pp_jstring s

let pp_ireg pp reg =
  pp_reg pp "r" (TargetPrinter.int_reg_name reg)

let pp_freg pp reg =
  pp_reg pp "f" (TargetPrinter.float_reg_name reg)

let preg_annot = function
  | IR r -> sprintf "r%s" (TargetPrinter.int_reg_name r)
  | FR r -> sprintf "f%s" (TargetPrinter.float_reg_name r)
  | _    -> assert false

let pp_atom pp a = pp_jstring pp (extern_atom a)

let pp_atom_constant pp a = pp_jsingle_object pp "Atom" pp_atom a

let pp_int pp i = fprintf pp "%ld" (camlint_of_coqint i)
let pp_int64 pp i = fprintf pp "%Ld" (camlint64_of_coqint i)
let pp_float32 pp f = fprintf pp "%ld" (camlint_of_coqint (Floats.Float32.to_bits f))
let pp_float64 pp f = fprintf pp "%Ld" (camlint64_of_coqint (Floats.Float.to_bits f))
let pp_z pp z = fprintf pp "%s" (Z.to_string z)

let pp_int_constant pp i = pp_jsingle_object pp "Integer" pp_int i
let pp_float64_constant pp f = pp_jsingle_object pp "Float" pp_float64 f
let pp_float32_constant pp f = pp_jsingle_object pp "Float" pp_float32 f

let pp_constant pp c =
  let pp_symbol pp (i,c) =
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Name" pp_atom i;
    pp_jmember  pp "Offset" pp_int c;
    pp_jobject_end pp in
  match c with
  | Cint i ->  pp_int_constant pp i
  | Csymbol_low (i,c) ->
      pp_jsingle_object pp "Symbol_low" pp_symbol (i,c)
  | Csymbol_high (i,c) ->
      pp_jsingle_object pp "Symbol_high" pp_symbol (i,c)
  | Csymbol_sda (i,c) ->
      pp_jsingle_object pp "Symbol_sda" pp_symbol (i,c)
  | Csymbol_rel_low (i,c) ->
      pp_jsingle_object pp "Symbol_rel_low" pp_symbol (i,c)
  | Csymbol_rel_high (i,c) ->
      pp_jsingle_object pp "Symbol_rel_high" pp_symbol (i,c)

let pp_crbit pp c =
  pp_jsingle_object pp "CRbit" pp_jint (TargetPrinter.num_crbit c)

let pp_label pp l =
  pp_jsingle_object pp "Label" pp_jint32 (P.to_int32 l)

type instruction_arg =
  | Ireg of ireg
  | Freg of freg
  | Constant of constant
  | Long of Integers.Int.int
  | Id
  | Crbit of crbit
  | ALabel of positive
  | Float32 of Floats.float32
  | Float64 of Floats.float
  | Atom of positive
  | String of string

let id = ref 0

let next_id () =
  let tmp = !id in
  incr id;
  tmp

let reset_id () =
  id := 0

let pp_arg pp = function
  | Ireg ir -> pp_ireg pp ir
  | Freg fr -> pp_freg pp fr
  | Constant c -> pp_constant pp c
  | Long i ->  pp_jsingle_object pp "Integer" pp_int64 i
  | Id -> let i = next_id () in
    pp_jsingle_object pp "Integer" (fun pp i -> fprintf pp "%d" i) i
  | Crbit cr -> pp_crbit pp cr
  | ALabel lbl -> pp_label pp lbl
  | Float32 f -> pp_float32_constant pp f
  | Float64 f  -> pp_float64_constant pp f
  | Atom a -> pp_atom_constant pp a
  | String s -> pp_jsingle_object pp "String" pp_jstring s

let pp_instructions pp ic =
  let ic = List.filter (fun s -> match s with
      | Pbuiltin (ef,_,_) ->
        begin match ef with
          | EF_inline_asm _
          | EF_annot _ -> true
          | _ -> false
        end
      | Pcfi_adjust _  (* Only debug relevant *)
      | Pcfi_rel_offset _ -> false
      | _ -> true) ic in
  let instruction pp n args =
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Instruction Name" pp_jstring n;
    pp_jmember pp "Args" (pp_jarray pp_arg) args;
    pp_jobject_end pp in
  let instruction pp = function
  | Padd (ir1,ir2,ir3)
  | Padd64 (ir1,ir2,ir3) -> instruction pp "Padd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Paddc (ir1,ir2,ir3) -> instruction pp "Paddc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Padde (ir1,ir2,ir3) -> instruction pp "Padde" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Paddi (ir1,ir2,c) -> instruction pp "Paddi" [Ireg ir1; Ireg ir2; Constant c]
  | Paddi64 (ir1,ir2,n) -> instruction pp "Paddi" [Ireg ir1; Ireg ir2; Constant (Cint n)] (* FIXME, ugly, immediates are int64 but always fit into 16bits *)
  | Paddic  (ir1,ir2,c) -> instruction pp "Paddic" [Ireg ir1; Ireg ir2; Constant c]
  | Paddis  (ir1,ir2,c) -> instruction pp "Paddis" [Ireg ir1; Ireg ir2; Constant c]
  | Paddis64 (ir1,ir2,n) -> instruction pp "Paddis" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Paddze (ir1,ir2)
  | Paddze64 (ir1,ir2) -> instruction pp "Paddze" [Ireg ir1; Ireg ir2]
  | Pallocframe _ -> assert false (* Should not ppcur *)
  | Pand_ (ir1,ir2,ir3)
  | Pand_64 (ir1,ir2,ir3) -> instruction pp "Pand_" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pandc (ir1,ir2,ir3) -> instruction pp "Pandc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pandi_ (ir1,ir2,c) -> instruction pp "Pandi_" [Ireg ir1; Ireg ir2; Constant c]
  | Pandi_64 (ir1,ir2,n) -> instruction pp "Pandi_" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Pandis_ (ir1,ir2,c) -> instruction pp "Pandis_" [Ireg ir1; Ireg ir2; Constant c]
  | Pandis_64 (ir1,ir2,n) -> instruction pp "Pandis_" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Pb l -> instruction pp "Pb" [ALabel l]
  | Pbctr s -> instruction pp "Pbctr" []
  | Pbctrl s -> instruction pp "Pbctrl" []
  | Pbdnz l -> instruction pp "Pbdnz" [ALabel l]
  | Pbf (cr,l) -> instruction pp "Pbf" [Crbit cr; ALabel l]
  | Pbl (i,s) -> instruction pp "Pbl" [Atom i]
  | Pbs (i,s) -> instruction pp "Pbs" [Atom i]
  | Pblr -> instruction pp "Pblr" []
  | Pbt (cr,l) ->  instruction pp "Pbt" [Crbit cr; ALabel l]
  | Pbtbl (i,lb) -> instruction pp "Pbtbl" ((Ireg i)::(List.map (fun a -> ALabel a) lb))
  | Pcmpb (ir1,ir2,ir3) -> instruction pp "Pcmpb" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pcmpld (ir1,ir2) -> instruction pp "Pcmpld" [Ireg ir1; Ireg ir2]
  | Pcmpldi (ir,n) -> instruction pp "Pcmpldi" [Ireg ir; Constant (Cint n)]
  | Pcmplw (ir1,ir2) -> instruction pp "Pcmplw" [Ireg ir1; Ireg ir2]
  | Pcmplwi (ir,c) -> instruction pp "Pcmplwi" [Ireg ir; Constant c]
  | Pcmpd (ir1,ir2) -> instruction pp "Pcmpd" [Ireg ir1; Ireg ir2]
  | Pcmpdi (ir,n) -> instruction pp "Pcmpdi" [Ireg ir; Constant (Cint n)]
  | Pcmpw (ir1,ir2) -> instruction pp "Pcmpw" [Ireg ir1; Ireg ir2]
  | Pcmpwi (ir,c) -> instruction pp "Pcmpwi" [Ireg ir; Constant c]
  | Pcntlzd (ir1,ir2) -> instruction pp "Pcntlzd" [Ireg ir1; Ireg ir2]
  | Pcntlzw (ir1,ir2) -> instruction pp "Pcntlzw" [Ireg ir1; Ireg ir2]
  | Pcreqv (cr1,cr2,cr3) -> instruction pp "Pcreqv" [Crbit cr1; Crbit cr2; Crbit cr3]
  | Pcror (cr1,cr2,cr3) -> instruction pp "Pcror" [Crbit cr1; Crbit cr2; Crbit cr3]
  | Pcrxor (cr1,cr2,cr3) -> instruction pp "Pcrxor" [Crbit cr1; Crbit cr2; Crbit cr3]
  | Pdcbf (ir1,ir2) -> instruction pp "Pdcbf" [Ireg ir1; Ireg ir2]
  | Pdcbi (ir1,ir2) -> instruction pp "Pdcbi" [Ireg ir1; Ireg ir2]
  | Pdcbt (n,ir1,ir2) -> instruction pp "Pdcbt" [Constant (Cint n); Ireg ir1; Ireg ir2]
  | Pdcbtst (n,ir1,ir2) -> instruction pp "Pdcbtst" [Constant (Cint n); Ireg ir1; Ireg ir2]
  | Pdcbtls (n,ir1,ir2) ->  instruction pp "Pdcbtls" [Constant (Cint n); Ireg ir1; Ireg ir2]
  | Pdcbz (ir1,ir2) -> instruction pp "Pdcbz" [Ireg ir1; Ireg ir2]
  | Pdivw (ir1,ir2,ir3) -> instruction pp "Pdivw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pdivd (ir1,ir2,ir3) -> instruction pp "Pdivd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pdivwu (ir1,ir2,ir3) -> instruction pp "Pdivwu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pdivdu (ir1,ir2,ir3) -> instruction pp "Pdivdu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Peieio -> instruction pp "Peieio" []
  | Peqv (ir1,ir2,ir3) -> instruction pp "Peqv" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pextsb (ir1,ir2) -> instruction pp "Pextsb" [Ireg ir1; Ireg ir2]
  | Pextsh (ir1,ir2) -> instruction pp "Pextsh" [Ireg ir1; Ireg ir2]
  | Pextsw (ir1,ir2) -> instruction pp "Pextsw" [Ireg ir1; Ireg ir2]
  | Pextzw (ir1,ir2) -> assert false (* Should not ppcur *)
  | Pfreeframe (c,i) -> assert false (* Should not ppcur *)
  | Pfabs (fr1,fr2)
  | Pfabss (fr1,fr2) -> instruction pp "Pfabs" [Freg fr1; Freg fr2]
  | Pfadd (fr1,fr2,fr3) -> instruction pp "Pfadd" [Freg fr1; Freg fr2; Freg fr3]
  | Pfadds (fr1,fr2,fr3) -> instruction pp "Pfadds" [Freg fr1; Freg fr2; Freg fr3]
  | Pfcmpu (fr1,fr2) -> instruction pp "Pfcmpu" [Freg fr1; Freg fr2]
  | Pfcfi (ir,fr)
  | Pfcfl (ir,fr) -> assert false (* Should not ppcur *)
  | Pfcfid (fr1,fr2) -> instruction pp "Pfcfid" [Freg fr1; Freg fr2]
  | Pfcfiu _ (* Should not ppcur *)
  | Pfcti _ (* Should not ppcur *)
  | Pfctiu _ (* Should not ppcur *)
  | Pfctid _ -> assert false (* Should not ppcur *)
  | Pfctidz (fr1,fr2) -> instruction pp "Pfctidz" [Freg fr1; Freg fr2]
  | Pfctiw (fr1,fr2) -> instruction pp "Pfctiw" [Freg fr1; Freg fr2]
  | Pfctiwz (fr1,fr2) -> instruction pp "Pfctiwz" [Freg fr1; Freg fr2]
  | Pfdiv (fr1,fr2,fr3) -> instruction pp "Pfdiv" [Freg fr1; Freg fr2; Freg fr3]
  | Pfdivs (fr1,fr2,fr3) -> instruction pp "Pfdivs" [Freg fr1; Freg fr2; Freg fr3]
  | Pfmake (fr,ir1,ir2) -> assert false (* Should not ppcur *)
  | Pfmr (fr1,fr2) -> instruction pp "Pfmr" [Freg fr1; Freg fr2]
  | Pfmul (fr1,fr2,fr3) -> instruction pp "Pfmul" [Freg fr1; Freg fr2; Freg fr3]
  | Pfmuls(fr1,fr2,fr3) -> instruction pp "Pfmuls" [Freg fr1; Freg fr2; Freg fr3]
  | Pfneg (fr1,fr2)
  | Pfnegs (fr1,fr2) -> instruction pp "Pfneg" [Freg fr1; Freg fr2]
  | Pfrsp (fr1,fr2) -> instruction pp "Pfrsp" [Freg fr1; Freg fr2]
  | Pfxdp (fr1,fr2) -> assert false (* Should not ppcur *)
  | Pfsub (fr1,fr2,fr3) -> instruction pp "Pfsub" [Freg fr1; Freg fr2; Freg fr3]
  | Pfsubs (fr1,fr2,fr3) ->  instruction pp "Pfsubs" [Freg fr1; Freg fr2; Freg fr3]
  | Pfmadd (fr1,fr2,fr3,fr4) -> instruction pp "Pfmadd" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pfmsub (fr1,fr2,fr3,fr4) ->  instruction pp "Pfmsub" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pfnmadd (fr1,fr2,fr3,fr4) -> instruction pp "Pfnmadd" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pfnmsub (fr1,fr2,fr3,fr4) -> instruction pp "Pfnmsub" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pfsqrt (fr1,fr2) -> instruction pp "Pfsqrt" [Freg fr1; Freg fr2]
  | Pfrsqrte (fr1,fr2) -> instruction pp "Pfrsqrte" [Freg fr1; Freg fr2]
  | Pfres (fr1,fr2) -> instruction pp "Pfres" [Freg fr1; Freg fr2]
  | Pfsel (fr1,fr2,fr3,fr4) -> instruction pp "Pfsel" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pisel (ir1,ir2,ir3,cr) ->  instruction pp "Pisel" [Ireg ir1; Ireg ir2; Ireg ir3; Crbit cr]
  | Picbi (ir1,ir2) -> instruction pp "Picbi" [Ireg ir1; Ireg ir2]
  | Picbtls (n,ir1,ir2) -> instruction pp "Picbtls" [Constant (Cint n);Ireg ir1; Ireg ir2]
  | Pisync -> instruction pp "Pisync" []
  | Plwsync -> instruction pp "Plwsync" []
  | Plbz (ir1,c,ir2) -> instruction pp "Plbz" [Ireg ir1; Constant c; Ireg ir2]
  | Plbzx (ir1,ir2,ir3) -> instruction pp "Plbzx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pld (ir1,c,ir2)
  | Pld_a (ir1,c,ir2) -> instruction pp "Pld" [Ireg ir1; Constant c; Ireg ir2]
  | Pldx (ir1,ir2,ir3)
  | Pldx_a (ir1,ir2,ir3) -> instruction pp "Pldx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plfd (fr,c,ir)
  | Plfd_a (fr,c,ir) -> instruction pp "Plfd" [Freg fr; Constant c; Ireg ir]
  | Plfdx (fr,ir1,ir2)
  | Plfdx_a (fr,ir1,ir2) -> instruction pp "Plfdx" [Freg fr; Ireg ir1; Ireg ir2]
  | Plfs (fr,c,ir) -> instruction pp "Plfs" [Freg fr; Constant c; Ireg ir]
  | Plfsx  (fr,ir1,ir2) -> instruction pp "Plfsx" [Freg fr; Ireg ir1; Ireg ir2]
  | Plha (ir1,c,ir2) -> instruction pp "Plha" [Ireg ir1; Constant c; Ireg ir2]
  | Plhax (ir1,ir2,ir3) -> instruction pp "Plhax" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plhbrx (ir1,ir2,ir3) -> instruction pp "Plhbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plhz (ir1,c,ir2) -> instruction pp "Plhz" [Ireg ir1; Constant c; Ireg ir2]
  | Plhzx (ir1,ir2,ir3) -> instruction pp "Plhzx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pldi (ir,c) -> instruction pp "Pldi" [Ireg ir; Long c] (* FIXME Cint is too small, we need Clong *)
  | Plmake _ (* Should not ppcur *)
  | Pllo _ (* Should not ppcur *)
  | Plhi _ -> assert false (* Should not ppcur *)
  | Plfi (fr,fc) -> instruction pp "Plfi" [Freg fr; Float64 fc]
  | Plfis (fr,fc) -> instruction pp "Plfis" [Freg fr; Float32 fc]
  | Plwz (ir1,c,ir2)
  | Plwz_a (ir1,c,ir2) -> instruction pp "Plwz" [Ireg ir1;Constant c; Ireg ir2]
  | Plwzu (ir1,c,ir2) -> instruction pp "Plwzu" [Ireg ir1; Constant c; Ireg ir2]
  | Plwzx (ir1,ir2,ir3)
  | Plwzx_a (ir1,ir2,ir3) -> instruction pp "Plwzx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plwarx (ir1,ir2,ir3) -> instruction pp "Plwarx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plwbrx (ir1,ir2,ir3) -> instruction pp "Plwbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmbar c -> instruction pp "Pmbar" [Constant (Cint c)]
  | Pmfcr ir -> instruction pp "Pmfcr" [Ireg ir]
  | Pmfcrbit (ir,crb) -> assert false (* Should not ppcur *)
  | Pmflr ir -> instruction pp "Pmflr" [Ireg ir]
  | Pmr (ir1,ir2) -> instruction pp "Pmr" [Ireg ir1; Ireg ir2]
  | Pmtctr ir -> instruction pp "Pmtctr" [Ireg ir]
  | Pmtlr ir -> instruction pp "Pmtlr" [Ireg ir]
  | Pmfspr(ir, n) -> instruction pp "Pmfspr" [Ireg ir; Constant (Cint n)]
  | Pmtspr(n, ir) -> instruction pp "Pmtspr" [Constant (Cint n); Ireg ir]
  | Pmulhd (ir1,ir2,ir3) -> instruction pp "Pmulhd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulhdu (ir1,ir2,ir3) -> instruction pp "Pmulhdu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulld (ir1,ir2,ir3) -> instruction pp "Pmulld" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulli (ir1,ir2,c) -> instruction pp "Pmulli" [Ireg ir1; Ireg ir2; Constant c]
  | Pmullw (ir1,ir2,ir3) -> instruction pp "Pmullw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulhw (ir1,ir2,ir3) -> instruction pp "Pmulhw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulhwu (ir1,ir2,ir3) -> instruction pp "Pmulhwu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pnand (ir1,ir2,ir3) -> instruction pp "Pnand" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pnor (ir1,ir2,ir3)
  | Pnor64 (ir1,ir2,ir3) -> instruction pp "Pnor" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Por (ir1,ir2,ir3)
  | Por64 (ir1,ir2,ir3) -> instruction pp "Por" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Porc (ir1,ir2,ir3) -> instruction pp "Porc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pori (ir1,ir2,c) -> instruction pp "Pori" [Ireg ir1; Ireg ir2; Constant c]
  | Pori64 (ir1,ir2,n) -> instruction pp "Pori" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Poris (ir1,ir2,c) -> instruction pp "Poris" [Ireg ir1; Ireg ir2; Constant c]
  | Poris64 (ir1,ir2,n) -> instruction pp "Poris" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Prldicl (ir1,ir2,ic1,ic2) -> instruction pp "Prldicl" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Prldinm (ir1,ir2,ic1,ic2) -> instruction pp "Prldinm" [Ireg ir1; Ireg ir2; Long ic1; Long ic2]
  | Prldimi  (ir1,ir2,ic1,ic2) ->instruction pp "Prldimi" [Ireg ir1; Ireg ir2; Long ic1; Long ic2]
  | Prlwinm (ir1,ir2,ic1,ic2) -> instruction pp "Prlwinm" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Prlwimi  (ir1,ir2,ic1,ic2) ->instruction pp "Prlwimi" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Psld (ir1,ir2,ir3) -> instruction pp "Psld" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pslw (ir1,ir2,ir3) -> instruction pp "Pslw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psrad (ir1,ir2,ir3) -> instruction pp "Psrad" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psradi  (ir1,ir2,ic) -> instruction pp "Psradi" [Ireg ir1; Ireg ir2; Constant (Cint ic)]
  | Psraw (ir1,ir2,ir3) -> instruction pp "Psraw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psrawi  (ir1,ir2,ic) -> instruction pp "Psrawi" [Ireg ir1; Ireg ir2; Constant (Cint ic)]
  | Psrd (ir1,ir2,ir3) -> instruction pp "Psrd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psrw (ir1,ir2,ir3) -> instruction pp "Psrw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstb (ir1,c,ir2) -> instruction pp "Pstb" [Ireg ir1; Constant c; Ireg ir2]
  | Pstbx (ir1,ir2,ir3) -> instruction pp "Pstbx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstd (ir1,c,ir2)
  | Pstd_a (ir1,c,ir2) -> instruction pp "Pstd" [Ireg ir1; Constant c; Ireg ir2]
  | Pstdx (ir1,ir2,ir3)
  | Pstdx_a (ir1,ir2,ir3) -> instruction pp "Pstdx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstdu (ir1,c,ir2) -> instruction pp "Pstdu" [Ireg ir1; Constant c; Ireg ir2]
  | Pstfd (fr,c,ir)
  | Pstfd_a (fr,c,ir) -> instruction pp "Pstfd" [Freg fr; Constant c; Ireg ir]
  | Pstfdu (fr,c,ir) -> instruction pp "Pstfdu" [Freg fr; Constant c; Ireg ir]
  | Pstfdx (fr,ir1,ir2)
  | Pstfdx_a (fr,ir1,ir2) -> instruction pp "Pstfdx" [Freg fr; Ireg ir1; Ireg ir2]
  | Pstfs (fr,c,ir) -> instruction pp "Pstfs" [Freg fr; Constant c; Ireg ir]
  | Pstfsx (fr,ir1,ir2) -> instruction pp "Pstfsx" [Freg fr; Ireg ir1; Ireg ir2]
  | Psth (ir1,c,ir2) -> instruction pp "Psth"  [Ireg ir1; Constant c; Ireg ir2]
  | Psthx (ir1,ir2,ir3) -> instruction pp "Psthx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psthbrx (ir1,ir2,ir3) -> instruction pp "Psthbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstw (ir1,c,ir2)
  | Pstw_a (ir1,c,ir2) -> instruction pp "Pstw" [Ireg ir1; Constant c; Ireg ir2]
  | Pstwu (ir1,c,ir2) -> instruction pp "Pstwu" [Ireg ir1; Constant c; Ireg ir2]
  | Pstwx (ir1,ir2,ir3)
  | Pstwx_a (ir1,ir2,ir3) -> instruction pp "Pstwx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstwux (ir1,ir2,ir3) -> instruction pp "Pstwux" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstwbrx (ir1,ir2,ir3) -> instruction pp "Pstwbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstwcx_ (ir1,ir2,ir3) -> instruction pp "Pstwcx_" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfc (ir1,ir2,ir3)
  | Psubfc64 (ir1,ir2,ir3) -> instruction pp "Psubfc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfe (ir1,ir2,ir3) -> instruction pp "Psubfe" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfze (ir1,ir2) -> instruction pp "Psubfze" [Ireg ir1; Ireg ir2]
  | Psubfic (ir1,ir2,c) -> instruction pp "Psubfic" [Ireg ir1; Ireg ir2; Constant c]
  | Psubfic64 (ir1,ir2,n) -> instruction pp "Psubfic" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Psync -> instruction pp "Psync" []
  | Ptrap -> instruction pp "Ptrap" []
  | Pxor (ir1,ir2,ir3)
  | Pxor64 (ir1,ir2,ir3) -> instruction pp "Pxor" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pxori (ir1,ir2,c) -> instruction pp "Pxori" [Ireg ir1; Ireg ir2; Constant c]
  | Pxori64 (ir1,ir2,n) -> instruction pp "Pxori" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Pxoris (ir1,ir2,c) -> instruction pp "Pxoris" [Ireg ir1; Ireg ir2; Constant c]
  | Pxoris64 (ir1,ir2,n) -> instruction pp "Pxoris" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Plabel l -> instruction pp "Plabel" [ALabel l]
  | Pbuiltin (ef,args,_) ->
    begin match ef with
      | EF_inline_asm _ ->
        instruction pp "Pinlineasm" [Id];
        Cerrors.warning ("",-10) Cerrors.Inline_asm_sdump "inline assembler is not supported in sdump"
      | EF_annot (txt,targs) ->
        let annot_string = PrintAsmaux.annot_text preg_annot "r1" (camlstring_of_coqstring txt) args in
        let len = String.length annot_string in
        let buf = Buffer.create len in
        String.iter (fun c -> begin match c with
            | '\\' | '"' -> Buffer.add_char buf '\\'
            | _ -> () end;
            Buffer.add_char buf c) annot_string;
        let annot_string = Buffer.contents buf in
        instruction pp "Pannot" [String annot_string]
      | _ -> assert false
    end
  | Pcfi_adjust _  (* Only debug relevant *)
  | Pcfi_rel_offset _ -> assert false in (* Only debug relevant *)
  pp_jarray instruction pp ic

let pp_storage pp static =
    pp_jstring pp (if static then "Static" else "Extern")

let pp_section pp sec =
  let pp_simple name =
    pp_jsingle_object pp "Section Name" pp_jstring name
  and pp_complex name init =
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Section Name" pp_jstring name;
    pp_jmember pp "Init" pp_jbool init;
    pp_jobject_end pp in
  match sec with
  | Section_text -> pp_simple "Text"
  | Section_data init -> pp_complex "Data" init
  | Section_small_data init -> pp_complex "Small Data" init
  | Section_const init -> pp_complex "Const" init
  | Section_small_const init -> pp_complex "Small Const" init
  | Section_string -> pp_simple "String"
  | Section_literal -> pp_simple "Literal"
  | Section_jumptable -> pp_simple "Jumptable"
  | Section_user (s,w,e) ->
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Section Name" pp_jstring s;
    pp_jmember pp "Writable" pp_jbool w;
    pp_jmember pp "Writable" pp_jbool e;
    pp_jobject_end pp
  | Section_debug_info _
  | Section_debug_abbrev
  | Section_debug_line _
  | Section_debug_loc
  | Section_debug_ranges
  | Section_debug_str -> () (* There should be no info in the debug sections *)

let pp_int_opt pp = function
  | None -> fprintf pp "0"
  | Some i -> fprintf pp "%d" i


let pp_fundef pp (name,f) =
  let alignment = atom_alignof name
  and inline = atom_is_inline name
  and static = atom_is_static name
  and c_section,l_section,j_section = match (atom_sections name) with [a;b;c] -> a,b,c | _ -> assert false in
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Fun Name" pp_atom name;
  pp_jmember pp "Fun Storage Class" pp_storage static;
  pp_jmember pp "Fun Alignment" pp_int_opt alignment;
  pp_jmember pp "Fun Section Code" pp_section c_section;
  pp_jmember pp "Fun Section Literals" pp_section l_section;
  pp_jmember pp "Fun Section Jumptable" pp_section j_section;
  pp_jmember pp "Fun Inline" pp_jbool inline;
  pp_jmember pp "Fun Code" pp_instructions f.fn_code;
  pp_jobject_end pp

let pp_init_data pp = function
  | Init_int8 ic -> pp_jsingle_object pp "Init_int8" pp_int ic
  | Init_int16 ic -> pp_jsingle_object pp "Init_int16" pp_int ic
  | Init_int32 ic -> pp_jsingle_object pp "Init_int32" pp_int ic
  | Init_int64 lc -> pp_jsingle_object pp "Init_int64" pp_int64 lc
  | Init_float32 f -> pp_jsingle_object pp "Init_float32" pp_float32 f
  | Init_float64 f -> pp_jsingle_object pp "Init_float64" pp_float64 f
  | Init_space z -> pp_jsingle_object pp "Init_space" pp_z z
  | Init_addrof (p,i) ->
      let pp_addr_of pp (p,i) =
        pp_jobject_start pp;
        pp_jmember ~first:true pp "Addr" pp_atom p;
        pp_jmember  pp "Offset" pp_int i;
        pp_jobject_end pp  in
      pp_jsingle_object pp "Init_addrof" pp_addr_of (p,i)

let pp_vardef pp (name,v) =
  let alignment = atom_alignof name
  and static = atom_is_static name
  and section = match  (atom_sections name) with [s] -> s | _ -> assert false in(* Should only have one section *)
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Var Name" pp_atom name;
  pp_jmember pp "Var Readonly" pp_jbool v.gvar_readonly;
  pp_jmember pp "Var Volatile" pp_jbool v.gvar_volatile;
  pp_jmember pp "Var Storage Class" pp_storage static;
  pp_jmember pp "Var Alignment" pp_int_opt alignment;
  pp_jmember pp "Var Section" pp_section section;
  pp_jmember pp "Var Init" (pp_jarray pp_init_data) v.gvar_init;
  pp_jobject_end pp

let pp_program pp prog =
  reset_id ();
  let prog_vars,prog_funs = List.fold_left (fun (vars,funs) (ident,def) ->
    match def with
    | Gfun (Internal f) ->
      if not (atom_is_iso_inline_definition ident) then
        vars,(ident,f)::funs
      else
        vars,funs
    | Gvar v -> (ident,v)::vars,funs
    | _ -> vars,funs) ([],[]) prog.prog_defs in
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Global Variables" (pp_jarray pp_vardef) prog_vars;
  pp_jmember pp "Functions" (pp_jarray pp_fundef) prog_funs;
  pp_jobject_end pp
