(* *******************  *)
(* Author: PLDI-authors  *)
(* Date:   Oct 16, 2019 *)
(* *******************  *)




Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs .
Import ListNotations.

Local Open Scope error_monad_scope.

Definition option_ffpu := true.

Definition _Plea r addr :=
  if Archi.ptr64 then Pleaq r addr else Pleal r addr.

Definition linear_addr reg ofs := 
  Addrmode (Some reg) None (inl ofs).

Definition global_addr id ofs := 
  Addrmode None None (inr(id, ofs)).

Definition addressing_of_builtin_arg arg := 
  match arg with
  | BA (IR r) => OK (linear_addr r 0)
  | BA_addrstack ofs => OK (linear_addr RSP (Ptrofs.unsigned ofs))
  | BA_addrglobal id ofs => OK (global_addr id ofs)
  | _ => Error (msg "addressing_of_builtin_arg: builtin argument not supported")
  end.

Definition offset_addressing a delta :=
  let '(Addrmode base ofs cst) := a in
  let disp :=            
      match cst with
      | inl n => inl (n + delta)
      | inr (id, n) => inr (id, Ptrofs.add n (Ptrofs.repr delta))
      end in
  Addrmode base ofs disp.

(* Handling of memcpy *)

(* Unaligned memory accesses are quite fast on IA32, so use large
   memory accesses regardless of alignment. *)

Fixpoint copy (fuel:nat) (src dst:addrmode) (sz:Z) : res (list instruction) :=
  match fuel with
  | O => Error (msg "Error in copy: run out of fuel")
  | S fuel' =>
    if zle 8 sz && Archi.ptr64 then 
      do instrs <- copy fuel' (offset_addressing src 8) (offset_addressing dst 8) (sz - 8);
      OK ([Pmovq_rm RCX src; Pmovq_mr dst RCX] ++ instrs)
    else if zle 8 sz && option_ffpu then 
      do instrs <- copy fuel' (offset_addressing src 8) (offset_addressing dst 8) (sz - 8);
      OK ([Pmovsq_rm XMM7 src; Pmovsq_mr dst XMM7] ++ instrs)
    else if zle 4 sz then 
      do instrs <- copy fuel' (offset_addressing src 4) (offset_addressing dst 4) (sz - 4);
      OK ([Pmovl_rm RCX src; Pmovl_mr dst RCX] ++ instrs)
    else if zle 2 sz then
      do instrs <- copy fuel' (offset_addressing src 2) (offset_addressing dst 2) (sz - 2);
      OK ([Pmovw_rm RCX src; Pmovw_mr dst RCX] ++ instrs)
    else if zle 1 sz then
      do instrs <- copy fuel' (offset_addressing src 1) (offset_addressing dst 1) (sz - 1);
      OK ([Pmovb_rm RCX src; Pmovb_mr dst RCX] ++ instrs)
    else 
      OK []
  end.

Definition expand_builtin_memcpy_small (sz al:Z) (src dst: builtin_arg preg) : res (list instruction) :=
  do asrc <- (addressing_of_builtin_arg src);
  do adst <- (addressing_of_builtin_arg dst);
  copy (Z.to_nat sz) asrc adst sz.

Definition crbit_arg_dec (c1 c2: crbit) : {c1 = c2} + {c1 <> c2}.
  decide equality.
Qed.

Definition builtin_arg_dec (a1 a2: builtin_arg preg) : {a1 = a2} + {a1 <> a2}.
  decide equality; try decide equality; try apply Ptrofs.eq_dec.
  - apply ireg_eq.
  - apply freg_eq.
  - apply crbit_arg_dec.
  - apply Int.eq_dec.
  - apply Int64.eq_dec.
  - apply Floats.Float.eq_dec.
  - apply Floats.Float32.eq_dec.
Qed.

Definition expand_builtin_memcpy_big (sz al:Z) (src dst: builtin_arg preg) : res (list instruction) :=
  do sinstrs <-
      if builtin_arg_dec src (BA (IR RSI)) 
      then OK []
      else (do a <- addressing_of_builtin_arg src;
              OK [_Plea RSI a]);
  do dinstrs <-
      if builtin_arg_dec dst (BA (IR RDI))
      then OK []
      else (do a <- addressing_of_builtin_arg dst;
              OK [_Plea RDI a]);
  let i1 := Pmovl_ri RCX (Int.repr (sz / 4)) in
  let i2 := Prep_movsl in
  let is1 := if zle 2 (sz mod 4) then [Pmovsw] else [] in
  let is2 := if zle 1 (sz mod 2) then [Pmovsb] else [] in
  OK (sinstrs ++ dinstrs ++ [i1; i2] ++ is1 ++ is2).
  
Definition expand_builtin_memcpy (sz al:Z) (args: list (builtin_arg preg)) : res (list instruction) :=
  do r <-
     match args with 
     | [d; s] => OK (d, s) 
     | _ => Error (msg "Error in expanding builtin memcpy: Wrong number of arguments")
     end;
  let '(dst, src) := r in
  if zle sz 32 
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst.

Local Open Scope string_scope.

Definition expand_builtin_inline i name args res :=
  match name, args, res with
  | "__builtin_addl", [BA_splitlong (BA(IR ah)) (BA(IR al));
                       BA_splitlong (BA(IR bh)) (BA(IR bl))],
                       BR_splitlong (BR(IR rh)) (BR(IR rl)) =>
     if (ireg_eq ah RDX && ireg_eq al RAX && ireg_eq bh RCX && ireg_eq bl RBX && ireg_eq rh RDX && ireg_eq rl RAX) then
       OK [ Padcl_rr RDX RCX ; Paddl_rr RAX RBX]
     else
       Error (msg "Error in expanding of builtin: __builtin_addl arguments incorrect")
  | _, _, _ =>
    OK [i]
  end.

Local Close Scope string_scope.


Definition transl_instr (i: instruction) (ofs:Z) (code:code) : res (list instruction) :=
  match i with
  |Psetcc c rd =>
   OK [Pmovzb_rr rd rd; Psetcc c rd]
  |Pbuiltin ef args res =>
   match ef with
   | EF_memcpy sz al =>
     expand_builtin_memcpy sz al args
   | EF_builtin name sg =>
     expand_builtin_inline i name args res     
   | _ => OK [i]
   end
  |_ =>
   OK [i] 
  end.


Definition acc_transl_instr c r i :=
  do r' <- r;
    let '(ofs, code) := r' in
    do i' <- transl_instr i ofs c;
      OK (ofs + instr_size i, (i' ++ code)).
  
Definition transl_code (c:code) : res code :=
  do rs <- 
     fold_left (acc_transl_instr c)
               c
               (OK (0, []));
  let '(_, c') := rs in
  OK (rev c').


Definition trans_function (f: function) :res function :=
  if func_no_jmp_rel_dec f then 
    do instrs <- transl_code (fn_code f);
      OK (mkfunction (fn_sig f) instrs (fn_stacksize f) (fn_pubrange f))
  else
    Error (msg "Some source function contains relative jumps").

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef trans_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.


