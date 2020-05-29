(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Instruction selection *)

(** The instruction selection pass recognizes opportunities for using
  combined arithmetic and logical operations and addressing modes
  offered by the target processor.  For instance, the expression [x + 1]
  can take advantage of the "immediate add" instruction of the processor,
  and on the PowerPC, the expression [(x >> 6) & 0xFF] can be turned
  into a "rotate and mask" instruction.

  Instruction selection proceeds by bottom-up rewriting over expressions.
  The source language is Cminor and the target language is CminorSel. *)

Require String.
Require Import Coqlib Maps.
Require Import AST_old Errors Integers Globalenvs_old Switch_old.
Require Cminor_old.
Require Import Op_old CminorSel_old.
Require Import SelectOp_old SplitLong_old SelectLong_old SelectDiv_old.
Require Machregs_old.

Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.

(** Conversion of conditions *)

Function condexpr_of_expr (e: expr) : condexpr :=
  match e with
  | Eop (Ocmp c) el => CEcond c el
  | Econdition a b c => CEcondition a (condexpr_of_expr b) (condexpr_of_expr c)
  | Elet a b => CElet a (condexpr_of_expr b)
  | _ => CEcond (Ccompuimm Cne Int.zero) (e ::: Enil)
  end.

(** Conversion of loads and stores *)

Definition load (chunk: memory_chunk) (e1: expr) :=
  match addressing chunk e1 with
  | (mode, args) => Eload chunk mode args
  end.

Definition store (chunk: memory_chunk) (e1 e2: expr) :=
  match addressing chunk e1 with
  | (mode, args) => Sstore chunk mode args e2
  end.

(** Instruction selection for operator applications.  Most of the work
    is done by the processor-specific smart constructors defined
    in modules [SelectOp] and [SelectLong]. *)

Section SELECTION.

Definition globdef := AST_old.globdef Cminor_old.fundef unit.
Variable defmap: PTree.t globdef.
Context {hf: helper_functions}.

Definition sel_constant (cst: Cminor_old.constant) : expr :=
  match cst with
  | Cminor_old.Ointconst n => Eop (Ointconst n) Enil
  | Cminor_old.Ofloatconst f => Eop (Ofloatconst f) Enil
  | Cminor_old.Osingleconst f => Eop (Osingleconst f) Enil
  | Cminor_old.Olongconst n => longconst n
  | Cminor_old.Oaddrsymbol id ofs => addrsymbol id ofs
  | Cminor_old.Oaddrstack ofs => addrstack ofs
  end.

Definition sel_unop (op: Cminor_old.unary_operation) (arg: expr) : expr :=
  match op with
  | Cminor_old.Ocast8unsigned => cast8unsigned arg
  | Cminor_old.Ocast8signed => cast8signed arg
  | Cminor_old.Ocast16unsigned => cast16unsigned arg
  | Cminor_old.Ocast16signed => cast16signed arg
  | Cminor_old.Onegint => negint arg
  | Cminor_old.Onotint => notint arg
  | Cminor_old.Onegf => negf arg
  | Cminor_old.Oabsf => absf arg
  | Cminor_old.Onegfs => negfs arg
  | Cminor_old.Oabsfs => absfs arg
  | Cminor_old.Osingleoffloat => singleoffloat arg
  | Cminor_old.Ofloatofsingle => floatofsingle arg
  | Cminor_old.Ointoffloat => intoffloat arg
  | Cminor_old.Ointuoffloat => intuoffloat arg
  | Cminor_old.Ofloatofint => floatofint arg
  | Cminor_old.Ofloatofintu => floatofintu arg
  | Cminor_old.Ointofsingle => intofsingle arg
  | Cminor_old.Ointuofsingle => intuofsingle arg
  | Cminor_old.Osingleofint => singleofint arg
  | Cminor_old.Osingleofintu => singleofintu arg
  | Cminor_old.Onegl => negl arg
  | Cminor_old.Onotl => notl arg
  | Cminor_old.Ointoflong => intoflong arg
  | Cminor_old.Olongofint => longofint arg
  | Cminor_old.Olongofintu => longofintu arg
  | Cminor_old.Olongoffloat => longoffloat arg
  | Cminor_old.Olonguoffloat => longuoffloat arg
  | Cminor_old.Ofloatoflong => floatoflong arg
  | Cminor_old.Ofloatoflongu => floatoflongu arg
  | Cminor_old.Olongofsingle => longofsingle arg
  | Cminor_old.Olonguofsingle => longuofsingle arg
  | Cminor_old.Osingleoflong => singleoflong arg
  | Cminor_old.Osingleoflongu => singleoflongu arg
  end.

Definition sel_binop (op: Cminor_old.binary_operation) (arg1 arg2: expr) : expr :=
  match op with
  | Cminor_old.Oadd => add arg1 arg2
  | Cminor_old.Osub => sub arg1 arg2
  | Cminor_old.Omul => mul arg1 arg2
  | Cminor_old.Odiv => divs arg1 arg2
  | Cminor_old.Odivu => divu arg1 arg2
  | Cminor_old.Omod => mods arg1 arg2
  | Cminor_old.Omodu => modu arg1 arg2
  | Cminor_old.Oand => and arg1 arg2
  | Cminor_old.Oor => or arg1 arg2
  | Cminor_old.Oxor => xor arg1 arg2
  | Cminor_old.Oshl => shl arg1 arg2
  | Cminor_old.Oshr => shr arg1 arg2
  | Cminor_old.Oshru => shru arg1 arg2
  | Cminor_old.Oaddf => addf arg1 arg2
  | Cminor_old.Osubf => subf arg1 arg2
  | Cminor_old.Omulf => mulf arg1 arg2
  | Cminor_old.Odivf => divf arg1 arg2
  | Cminor_old.Oaddfs => addfs arg1 arg2
  | Cminor_old.Osubfs => subfs arg1 arg2
  | Cminor_old.Omulfs => mulfs arg1 arg2
  | Cminor_old.Odivfs => divfs arg1 arg2
  | Cminor_old.Oaddl => addl arg1 arg2
  | Cminor_old.Osubl => subl arg1 arg2
  | Cminor_old.Omull => mull arg1 arg2
  | Cminor_old.Odivl => divls arg1 arg2
  | Cminor_old.Odivlu => divlu arg1 arg2
  | Cminor_old.Omodl => modls arg1 arg2
  | Cminor_old.Omodlu => modlu arg1 arg2
  | Cminor_old.Oandl => andl arg1 arg2
  | Cminor_old.Oorl => orl arg1 arg2
  | Cminor_old.Oxorl => xorl arg1 arg2
  | Cminor_old.Oshll => shll arg1 arg2
  | Cminor_old.Oshrl => shrl arg1 arg2
  | Cminor_old.Oshrlu => shrlu arg1 arg2
  | Cminor_old.Ocmp c => comp c arg1 arg2
  | Cminor_old.Ocmpu c => compu c arg1 arg2
  | Cminor_old.Ocmpf c => compf c arg1 arg2
  | Cminor_old.Ocmpfs c => compfs c arg1 arg2
  | Cminor_old.Ocmpl c => cmpl c arg1 arg2
  | Cminor_old.Ocmplu c => cmplu c arg1 arg2
  end.

(** Conversion from Cminor expression to Cminorsel expressions *)

Fixpoint sel_expr (a: Cminor_old.expr) : expr :=
  match a with
  | Cminor_old.Evar id => Evar id
  | Cminor_old.Econst cst => sel_constant cst
  | Cminor_old.Eunop op arg => sel_unop op (sel_expr arg)
  | Cminor_old.Ebinop op arg1 arg2 => sel_binop op (sel_expr arg1) (sel_expr arg2)
  | Cminor_old.Eload chunk addr => load chunk (sel_expr addr)
  end.

Fixpoint sel_exprlist (al: list Cminor_old.expr) : exprlist :=
  match al with
  | nil => Enil
  | a :: bl => Econs (sel_expr a) (sel_exprlist bl)
  end.

(** Recognition of immediate calls and calls to built-in functions
    that should be inlined *)

Inductive call_kind : Type :=
  | Call_default
  | Call_imm (id: ident)
  | Call_builtin (ef: external_function).

Definition expr_is_addrof_ident (e: Cminor_old.expr) : option ident :=
  match e with
  | Cminor_old.Econst (Cminor_old.Oaddrsymbol id ofs) =>
      if Ptrofs.eq ofs Ptrofs.zero then Some id else None
  | _ => None
  end.

Definition classify_call (e: Cminor_old.expr) : call_kind :=
  match expr_is_addrof_ident e with
  | None => Call_default
  | Some id =>
      match defmap!id with
      | Some(Gfun(External ef)) => if ef_inline ef then Call_builtin ef else Call_imm id
      | _ => Call_imm id
      end
  end.

(** Builtin arguments and results *)

Definition sel_builtin_arg
       (e: Cminor_old.expr) (c: builtin_arg_constraint): AST_old.builtin_arg expr :=
  let e' := sel_expr e in
  let ba := builtin_arg e' in
  if builtin_arg_ok ba c then ba else BA e'.

Fixpoint sel_builtin_args
       (el: list Cminor_old.expr)
       (cl: list builtin_arg_constraint): list (AST_old.builtin_arg expr) :=
  match el with
  | nil => nil
  | e :: el =>
      sel_builtin_arg e (List.hd OK_default cl) :: sel_builtin_args el (List.tl cl)
  end.

Definition sel_builtin_res (optid: option ident) : builtin_res ident :=
  match optid with
  | None => BR_none
  | Some id => BR id
  end.

(** Conversion of Cminor [switch] statements to decision trees. *)

Parameter compile_switch: Z -> nat -> table -> comptree.

Section SEL_SWITCH.

Variable make_cmp_eq: expr -> Z -> expr.
Variable make_cmp_ltu: expr -> Z -> expr.
Variable make_sub: expr -> Z -> expr.
Variable make_to_int: expr -> expr.

Fixpoint sel_switch (arg: nat) (t: comptree): exitexpr :=
  match t with
  | CTaction act =>
      XEexit act
  | CTifeq key act t' =>
      XEcondition (condexpr_of_expr (make_cmp_eq (Eletvar arg) key))
                  (XEexit act)
                  (sel_switch arg t')
  | CTiflt key t1 t2 =>
      XEcondition (condexpr_of_expr (make_cmp_ltu (Eletvar arg) key))
                  (sel_switch arg t1)
                  (sel_switch arg t2)
  | CTjumptable ofs sz tbl t' =>
      XElet (make_sub (Eletvar arg) ofs)
        (XEcondition (condexpr_of_expr (make_cmp_ltu (Eletvar O) sz))
                     (XEjumptable (make_to_int (Eletvar O)) tbl)
                     (sel_switch (S arg) t'))
  end.

End SEL_SWITCH.

Definition sel_switch_int :=
  sel_switch
    (fun arg n => comp Ceq arg (Eop (Ointconst (Int.repr n)) Enil))
    (fun arg n => compu Clt arg (Eop (Ointconst (Int.repr n)) Enil))
    (fun arg ofs => sub arg (Eop (Ointconst (Int.repr ofs)) Enil))
    (fun arg => arg).

Definition sel_switch_long :=
  sel_switch
    (fun arg n => cmpl Ceq arg (longconst (Int64.repr n)))
    (fun arg n => cmplu Clt arg (longconst (Int64.repr n)))
    (fun arg ofs => subl arg (longconst (Int64.repr ofs)))
    lowlong.

(** Conversion from Cminor statements to Cminorsel statements. *)

Fixpoint sel_stmt (s: Cminor_old.stmt) : res stmt :=
  match s with
  | Cminor_old.Sskip => OK Sskip
  | Cminor_old.Sassign id e => OK (Sassign id (sel_expr e))
  | Cminor_old.Sstore chunk addr rhs => OK (store chunk (sel_expr addr) (sel_expr rhs))
  | Cminor_old.Scall optid sg fn args =>
      OK (match classify_call fn with
      | Call_default => Scall optid sg (inl _ (sel_expr fn)) (sel_exprlist args)
      | Call_imm id  => Scall optid sg (inr _ id) (sel_exprlist args)
      | Call_builtin ef => Sbuiltin (sel_builtin_res optid) ef
                                    (sel_builtin_args args
                                       (Machregs_old.builtin_constraints ef))
      end)
  | Cminor_old.Sbuiltin optid ef args =>
      OK (Sbuiltin (sel_builtin_res optid) ef
                   (sel_builtin_args args (Machregs_old.builtin_constraints ef)))
  | Cminor_old.Stailcall sg fn args =>
      OK (match classify_call fn with
      | Call_imm id  => Stailcall sg (inr _ id) (sel_exprlist args)
      | _            => Stailcall sg (inl _ (sel_expr fn)) (sel_exprlist args)
      end)
  | Cminor_old.Sseq s1 s2 =>
      do s1' <- sel_stmt s1; do s2' <- sel_stmt s2;
      OK (Sseq s1' s2')
  | Cminor_old.Sifthenelse e ifso ifnot =>
      do ifso' <- sel_stmt ifso; do ifnot' <- sel_stmt ifnot;
      OK (Sifthenelse (condexpr_of_expr (sel_expr e)) ifso' ifnot')
  | Cminor_old.Sloop body =>
      do body' <- sel_stmt body; OK (Sloop body')
  | Cminor_old.Sblock body =>
      do body' <- sel_stmt body; OK (Sblock body')
  | Cminor_old.Sexit n => OK (Sexit n)
  | Cminor_old.Sswitch false e cases dfl =>
      let t := compile_switch Int.modulus dfl cases in
      if validate_switch Int.modulus dfl cases t
      then OK (Sswitch (XElet (sel_expr e) (sel_switch_int O t)))
      else Error (msg "Selection: bad switch (int)")
  | Cminor_old.Sswitch true e cases dfl =>
      let t := compile_switch Int64.modulus dfl cases in
      if validate_switch Int64.modulus dfl cases t
      then OK (Sswitch (XElet (sel_expr e) (sel_switch_long O t)))
      else Error (msg "Selection: bad switch (long)")
  | Cminor_old.Sreturn None => OK (Sreturn None)
  | Cminor_old.Sreturn (Some e) => OK (Sreturn (Some (sel_expr e)))
  | Cminor_old.Slabel lbl body =>
      do body' <- sel_stmt body; OK (Slabel lbl body')
  | Cminor_old.Sgoto lbl => OK (Sgoto lbl)
  end.

End SELECTION.

(** Conversion of functions. *)

Definition sel_function (dm: PTree.t globdef) (hf: helper_functions) (f: Cminor_old.function) : res function :=
  do body' <- sel_stmt dm f.(Cminor_old.fn_body);
  OK (mkfunction
        f.(Cminor_old.fn_sig)
        f.(Cminor_old.fn_params)
        f.(Cminor_old.fn_vars)
        f.(Cminor_old.fn_stackspace)
        body').

Definition sel_fundef (dm: PTree.t globdef) (hf: helper_functions) (f: Cminor_old.fundef) : res fundef :=
  transf_partial_fundef (sel_function dm hf) f.

(** Setting up the helper functions. *)

(** We build a partial mapping from global identifiers to their definitions,
  restricting ourselves to the globals we are interested in, namely
  the external function declarations that are marked as runtime library
  helpers. 
  This ensures that the mapping remains small and that [lookup_helper]
  below is efficient. *)

Definition globdef_of_interest (gd: globdef) : bool :=
  match gd with
  | Gfun (External (EF_runtime name sg)) => true
  | _ => false
  end.

Definition record_globdefs (defmap: PTree.t globdef) : PTree.t globdef :=
  PTree.fold 
    (fun m id gd => if globdef_of_interest gd then PTree.set id gd m else m)
    defmap (PTree.empty globdef).

Definition lookup_helper_aux
     (name: String.string) (sg: signature) (res: option ident)
     (id: ident) (gd: globdef) :=
  match gd with
  | Gfun (External (EF_runtime name' sg')) =>
      if String.string_dec name name' && signature_eq sg sg'
      then Some id
      else res
  | _ => res
  end.

Definition lookup_helper (globs: PTree.t globdef)
                         (name: String.string) (sg: signature) : res ident :=
  match PTree.fold (lookup_helper_aux name sg) globs None with
  | Some id => OK id
  | None    => Error (MSG name :: MSG ": missing or incorrect declaration" :: nil)
  end.

Local Open Scope string_scope.

Definition get_helpers (defmap: PTree.t globdef) : res helper_functions :=
  let globs := record_globdefs defmap in
  do i64_dtos <- lookup_helper globs "__i64_dtos" sig_f_l ;
  do i64_dtou <- lookup_helper globs "__i64_dtou" sig_f_l ;
  do i64_stod <- lookup_helper globs "__i64_stod" sig_l_f ;
  do i64_utod <- lookup_helper globs "__i64_utod" sig_l_f ;
  do i64_stof <- lookup_helper globs "__i64_stof" sig_l_s ;
  do i64_utof <- lookup_helper globs "__i64_utof" sig_l_s ;
  do i64_sdiv <- lookup_helper globs "__i64_sdiv" sig_ll_l ;
  do i64_udiv <- lookup_helper globs "__i64_udiv" sig_ll_l ;
  do i64_smod <- lookup_helper globs "__i64_smod" sig_ll_l ;
  do i64_umod <- lookup_helper globs "__i64_umod" sig_ll_l ;
  do i64_shl <- lookup_helper globs "__i64_shl" sig_li_l ;
  do i64_shr <- lookup_helper globs "__i64_shr" sig_li_l ;
  do i64_sar <- lookup_helper globs "__i64_sar" sig_li_l ;
  do i64_umulh <- lookup_helper globs "__i64_umulh" sig_ll_l ;
  do i64_smulh <- lookup_helper globs "__i64_smulh" sig_ll_l ;
  OK (mk_helper_functions
     i64_dtos i64_dtou i64_stod i64_utod i64_stof i64_utof
     i64_sdiv i64_udiv i64_smod i64_umod
     i64_shl i64_shr i64_sar
     i64_umulh i64_smulh).

(** Conversion of programs. *)

Definition sel_program (p: Cminor_old.program) : res program :=
  let dm := prog_defmap p in
  do hf <- get_helpers dm;
  transform_partial_program (sel_fundef dm hf) p.

