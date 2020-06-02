(* ********************* *)
(* Author: Yuting Wang   *)
(* Date:   Oct 2, 2019   *)
(* ********************* *)

(** * Linking of relocatable programs with linking reloctation tables **)

Require Import Coqlib Integers Values Maps AST.
Require Import Asm RelocProgram.
Require Import Linking Errors SeqTable.
Require RelocLinking.
Import ListNotations.

Local Open Scope list_scope.


Definition shift_relocentry_offset (ofs:Z) (e:relocentry) : relocentry :=
  {| reloc_offset := reloc_offset e + ofs;
     reloc_type   := reloc_type e;
     reloc_symb   := reloc_symb e;
     reloc_addend := reloc_addend e; |}.

Definition update_reloc_symb (stbl: symbtable) (sidxmap: symb_index_map_type)
           (e:relocentry) : option relocentry :=
  match SymbTable.get (reloc_symb e) stbl with
  | None => None
  | Some se => 
    match sidxmap ! (symbentry_id se) with
    | None => None
    | Some i => 
      Some {| reloc_offset := reloc_offset e;
              reloc_type   := reloc_type e;
              reloc_symb   := i;
              reloc_addend := reloc_addend e |}
    end
  end.

Definition acc_update_reloc_symb (stbl: symbtable) (sidxmap: symb_index_map_type)
           (e:relocentry) (t: option reloctable) : option reloctable :=
  match t, update_reloc_symb stbl sidxmap e with
  | Some t, Some e => Some (e::t)
  | _, _ => None
  end.

Definition update_reloctable_symb (stbl: symbtable) (sidxmap: symb_index_map_type)
           (t:reloctable) : option reloctable :=
  fold_right (acc_update_reloc_symb stbl sidxmap) (Some nil) t.

Definition link_reloctable 
           (ofs: Z)  (**r offset to be shifted in t2 *)
           (stbl1 stbl2: symbtable)  (**r old symbol tables *)
           (sidxmap: PTree.t N) (**r mappings from symbol ids to their indexes in the new symbol table *)
           (t1 t2: reloctable) (**r tables to be relocated *)
  : option reloctable :=
  match update_reloctable_symb stbl1 sidxmap t1,
        update_reloctable_symb stbl2 sidxmap t2 with
  | Some t1', Some t2' =>
    let t2'' := map (shift_relocentry_offset ofs) t2' in
    Some (t1' ++ t2'')
  | _, _ => None
  end.

Definition link_data_reloctable (p1 p2 p: program) : option reloctable :=
  let sidxmap := gen_symb_index_map (prog_symbtable p) in
  let stbl1   := prog_symbtable p1 in
  let stbl2   := prog_symbtable p2 in
  match SecTable.get sec_data_id (prog_sectable p1)
  with
  | Some data_sec1=>
    let t1 := reloctable_data (prog_reloctables p1) in
    let t2 := reloctable_data (prog_reloctables p2) in
    let dsz := sec_size data_sec1 in
    link_reloctable dsz stbl1 stbl2 sidxmap t1 t2
  | _ => None
  end.

Definition link_code_reloctable (p1 p2 p: program) : option reloctable :=
  let sidxmap := gen_symb_index_map (prog_symbtable p) in
  let stbl1   := prog_symbtable p1 in
  let stbl2   := prog_symbtable p2 in
  match SecTable.get sec_code_id (prog_sectable p1)
  with
  | Some code_sec1 =>
    let t1 := reloctable_code (prog_reloctables p1) in
    let t2 := reloctable_code (prog_reloctables p2) in
    let csz := sec_size code_sec1 in
    match SecTable.get sec_code_id (prog_sectable p2) with
    | Some code_sec2 =>
      if zlt (sec_size code_sec1 + sec_size code_sec2) Ptrofs.max_unsigned
      then link_reloctable csz stbl1 stbl2 sidxmap t1 t2
      else None
    | _ => None
    end
  | _ => None
  end.

Definition link_reloc_prog (p1 p2: program) : option program :=
  match RelocLinking.link_reloc_prog p1 p2 with
  | None => None
  | Some p =>
    match link_data_reloctable p1 p2 p,
          link_code_reloctable p1 p2 p
    with
    | Some dtbl, Some ctbl =>
      Some {| prog_defs   := prog_defs p;
              prog_public := prog_public p;
              prog_main   := prog_main p;
              prog_sectable  := prog_sectable p;
              prog_symbtable := prog_symbtable p;
              prog_strtable  := prog_strtable p;
              prog_reloctables := Build_reloctable_map ctbl dtbl;
              prog_senv := prog_senv p;
           |}
    | _, _ => None
    end
  end.

Instance Linker_reloc_prog : Linker program :=
{
  link := link_reloc_prog;
  linkorder := fun _ _ => True;
}.
Proof.
  auto.
  auto.
  auto.
Defined.
