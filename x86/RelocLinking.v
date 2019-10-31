(* ********************* *)
(* Author: Yuting Wang   *)
(* Date:   Oct 2, 2019   *)
(* ********************* *)

(** * Linking of relocatable programs **)

Require Import Coqlib Integers Values Maps AST.
Require Import Asm RelocProgram.
Require Import Linking Errors SeqTable.
Import ListNotations.

Local Open Scope list_scope.

Definition is_not_dummy_symbentry (e:symbentry) :=
  match symbentry_id e with
  | None => false
  | Some _ => true
  end.

(* Definition symbentry_id_neq (id:ident) (e:symbentry) := *)
(*   match symbentry_id e with *)
(*   | None => true *)
(*   | Some id' => if ident_eq id id' then false else true *)
(*   end. *)

Definition symbentry_id_eq (id:ident) (e:symbentry) :=
  match symbentry_id e with
  | None => false
  | Some id' => if ident_eq id id' then true else false
  end.


Definition link_symbtype (t1 t2: symbtype) :=
  match t1, t2 with
  | _, symb_notype => Some t1
  | symb_notype, _ => Some t2
  | symb_func, symb_func => Some symb_func
  | symb_data, symb_data => Some symb_data
  | _, _ => None
  end.

(** Assume we are linking two symbol entries e1 and e2 where
    e1 comes from the first compilation unit and e2 comes 
    from the second, and i1 and i2 are their section indexes, respectively.
    We want to postpone the linking of e1 with e2 when e2 represents an
    internal definition since we want internal definitions of the second 
    compilation unit to come after these of the first compilation unit, 
    so that linking matches with the generation of symbol table and sections 
    during the compilation *)

(* Inductive option_postpone {A:Type} := *)
(* | ONone  *)
(* | OSome (x:A) *)
(* | OPostponed (x:A). *)
 
(* Definition link_secindex (i1 i2: secindex) (sz1 sz2: Z) : @option_postpone secindex := *)
(*   match i1, i2 with *)
(*   | _, secindex_undef => OSome i1 *)
(*   | _, secindex_comm => *)
(*     if zeq sz1 sz2 then OSome i1 else ONone *)
(*   | secindex_undef, secindex_normal _ => OPostponed i2 *)
(*   | secindex_comm, secindex_normal _ => *)
(*     if zeq sz1 sz2 then OPostponed i2 else ONone *)
(*   | secindex_normal _ , secindex_normal _ => ONone *)
(*   end. *)

Definition is_symbentry_internal (e2: symbentry) : bool :=
  let i2 := symbentry_secindex e2 in
  match i2 with
  | secindex_undef
  | secindex_comm => false
  | _ => true
  end.

Definition update_symbtype (e: symbentry) t :=
  {| symbentry_id    := symbentry_id e;
     symbentry_bind  := symbentry_bind e;
     symbentry_type  := t;
     symbentry_value := symbentry_value e;
     symbentry_secindex := symbentry_secindex e;
     symbentry_size  := symbentry_size e; |}.

Definition link_symb (e1 e2: symbentry) : option symbentry :=
  match link_symbtype (symbentry_type e1) (symbentry_type e2) with
  | None => None
  | Some t =>
    let sz1 := symbentry_size e1 in
    let sz2 := symbentry_size e2 in
    let i1 := symbentry_secindex e1 in
    let i2 := symbentry_secindex e2 in
    match i1, i2 with
    | secindex_undef, secindex_undef =>
      Some (update_symbtype e1 t)
    | _, secindex_undef => Some e1
    | secindex_undef, _ => Some e2
    | _, secindex_comm =>
      if zeq sz1 sz2 then Some e1 else None
    | secindex_comm, _ =>
      if zeq sz1 sz2 then Some e2 else None
    | secindex_normal _ , secindex_normal _ => None
    end
  end.

Section WITH_RELOC_OFFSET.

(** Relocation offsets for internal symbols 
    in the second compilation unit in linking *)
Variable get_reloc_offset : N -> option Z.

Definition reloc_symb (e:symbentry) : option symbentry :=
  match symbentry_secindex e with
  | secindex_normal i => 
    match get_reloc_offset i with
    | None => None
    | Some ofs => 
      let val' := symbentry_value e + ofs in
      Some {| symbentry_id := symbentry_id e;
              symbentry_bind := symbentry_bind e;
              symbentry_type := symbentry_type e;
              symbentry_value := val';
              symbentry_secindex := symbentry_secindex e;
              symbentry_size := symbentry_size e;
           |}
    end
  | _ => Some e
  end.

Definition reloc_iter e t :=
  match t with
  | None => None
  | Some t' => 
    match reloc_symb e with
    | None => None
    | Some e' => Some (e' :: t')
    end
  end.

Definition reloc_symbtable (t:symbtable) : option symbtable :=
  fold_right reloc_iter (Some []) t.

End WITH_RELOC_OFFSET.

(** Linking of symbol tables *)
Definition link_symbtable_check (t2: PTree.t symbentry) (x: ident) (symb1: symbentry) :=
  match t2!x with
  | None => true
  | Some symb2 =>
    match link_symb symb1 symb2 with Some _ => true | None => false end
  end.

Definition link_symb_merge (o1 o2: option symbentry) :=
  match o1, o2 with
  | None, _ => o2
  | _, None => o1
  | Some gd1, Some gd2 => link_symb gd1 gd2
  end.

Definition link_symbtable (t1 t2: symbtable) : option symbtable :=
  let tree1 := symbtable_to_tree t1 in
  let tree2 := symbtable_to_tree t2 in
  if list_norepet_dec ident_eq (get_symbentry_ids t1)
  && list_norepet_dec ident_eq (get_symbentry_ids t2)
  && PTree_Properties.for_all tree1 (link_symbtable_check tree2) then
    let t := PTree.elements (PTree.combine link_symb_merge tree1 tree2) in
    Some (dummy_symbentry :: map snd t)
  else
    None.  

Definition link_section (s1 s2: section) : option section :=
  match s1, s2 with
  | sec_null, sec_null => 
    Some sec_null
  | sec_data d1, sec_data d2 => 
    Some (sec_data (d1 ++ d2))
  | sec_text c1, sec_text c2 =>
    Some (sec_text (c1 ++ c2))
  | sec_bytes b1, sec_bytes b2 =>
    Some (sec_bytes (b1 ++ b2))
  | _, _ => None
  end.

Definition link_sectable (s1 s2: sectable) : option sectable :=
  let sec_data1 := SeqTable.get (SecIndex.interp sec_data_id) s1 in
  let sec_text1 := SeqTable.get (SecIndex.interp sec_code_id) s1 in
  let sec_data2 := SeqTable.get (SecIndex.interp sec_data_id) s2 in
  let sec_text2 := SeqTable.get (SecIndex.interp sec_code_id) s2 in
  match sec_data1, sec_text1, sec_data2, sec_text2 with
  | Some sec_data1', Some sec_text1', Some sec_data2', Some sec_text2' =>
    let res_sec_text := link_section sec_text1' sec_text2' in
    let res_sec_data := link_section sec_data1' sec_data2' in
    match res_sec_text, res_sec_data with
    | Some sec_text3, Some sec_data3 =>
      Some [sec_null; sec_data3; sec_text3]
    | _, _ => 
      None
    end
  | _, _, _, _ =>
    None
  end.

Definition reloc_offset_fun (dsz csz: Z): N -> option Z :=
  (fun i => if N.eq_dec i (SecIndex.interp sec_data_id) then
           Some dsz
         else if N.eq_dec i (SecIndex.interp sec_code_id) then
           Some csz
         else
           None).

Definition link_reloc_prog (p1 p2: program) : option program :=
  let ap1 : Asm.program := 
      {| AST.prog_defs   := prog_defs p1;
         AST.prog_public := prog_public p1;
         AST.prog_main   := prog_main p1; |} in
  let ap2 : Asm.program := 
      {| AST.prog_defs   := prog_defs p2;
         AST.prog_public := prog_public p2;
         AST.prog_main   := prog_main p2; |} in
  match link ap1 ap2 with
  | None => None
  | Some ap =>
    let stbl1 := prog_sectable p1 in
    let stbl2 := prog_sectable p2 in
    let data_sec1 := SeqTable.get (SecIndex.interp sec_data_id) stbl1 in
    let code_sec1 := SeqTable.get (SecIndex.interp sec_code_id) stbl1 in
    match data_sec1, code_sec1 with
    | Some data_sec1', Some code_sec1' =>
      match link_sectable stbl1 stbl2 with
      | None => None
      | Some sectbl =>
        let t1 := (prog_symbtable p1) in
        let f_rofs := reloc_offset_fun (sec_size data_sec1') (sec_size code_sec1') in
        match reloc_symbtable f_rofs (prog_symbtable p2) with
        | None => None
        | Some t2 =>
          match link_symbtable t1 t2 with
          | None => None
          | Some symbtbl =>
            Some {| prog_defs   := AST.prog_defs ap;
                    prog_public := AST.prog_public ap;
                    prog_main   := AST.prog_main ap;
                    prog_sectable  := sectbl;
                    prog_symbtable := symbtbl;
                    prog_strtable  := prog_strtable p1;
                    prog_reloctables := prog_reloctables p1;
                    prog_senv := Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv ap); |}
          end
        end
      end
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