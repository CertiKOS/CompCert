
Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Segment FlatAsmGlobenv FlatAsmBuiltin.
Require Import Asm RawAsm FlatAsm.
Require Import Num.
Require Import FlatAsmProgram.
Require Globalenvs.


Inductive instruction : Type :=
  | MCjmp_l (ofs: ptrofs)
  | MCjcc (c: testcond)(ofs: ptrofs)
  | MCjcc2 (c1 c2: testcond)(ofs: ptrofs)   (**r pseudo *)
  | MCjmptbl (r: ireg) (tbl: list ptrofs) (**r pseudo *)
  | MCAsminstr : Asm.instruction -> instruction.

Definition instr_with_info:Type := @FlatAsmProgram.instr_with_info instruction.

(* The MC program *)
Definition program := @FlatAsmProgram.program instruction.


Open Scope asm.

Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.


(** * Operational semantics *)

(* Definition regset := Asm.regset. *)
Definition genv := @FlatAsmProgram.genv instruction.


Definition goto_label (ofs: ptrofs) (sz: ptrofs) (rs: regset) (m:mem):=
  Next (rs#PC <- (Val.offset_ptr (rs PC) (Ptrofs.add ofs sz))) m.

Definition eval_ros (ge : genv) (ros : ireg + ident) (rs : regset) :=
  match ros with
  | inl r => rs r
  | inr symb => Genv.symbol_address ge symb Ptrofs.zero
  end.


Definition exec_flatasm_instr {exec_load exec_store} `{!MemAccessors exec_load exec_store} 
           (ge: genv) (sz: ptrofs) (i:Asm.instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) sz) m
  | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n)) sz) m
  | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n)) sz) m
  | Pmov_rs rd id =>
      Next (nextinstr_nf (rs#rd <- (Genv.symbol_address ge id Ptrofs.zero)) sz) m
  | Pmovl_rm rd a =>
      exec_load _ _ _ ge Mint32 m a rs rd sz
  | Pmovq_rm rd a =>
      exec_load _ _ _ ge Mint64 m a rs rd sz
  | Pmovl_mr a r1 =>
      exec_store _ _ _ ge Mint32 m a rs r1 nil sz
  | Pmovq_mr a r1 =>
      exec_store _ _ _ ge Mint64 m a rs r1 nil sz
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) sz) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n)) sz) m
  | Pmovsd_fm rd a =>
      exec_load _ _ _ ge Mfloat64 m a rs rd  sz
  | Pmovsd_mf a r1 =>
      exec_store _ _ _ ge Mfloat64 m a rs r1 nil sz
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n)) sz) m
  | Pmovss_fm rd a =>
      exec_load _ _ _ ge Mfloat32 m a rs rd sz
  | Pmovss_mf a r1 =>
      exec_store _ _ _ ge Mfloat32 m a rs r1 nil sz
  | Pfldl_m a =>
      exec_load _ _ _ ge Mfloat64 m a rs ST0 sz
  | Pfstpl_m a =>
      exec_store _ _ _ ge Mfloat64 m a rs ST0 (ST0 :: nil) sz
  | Pflds_m a =>
      exec_load _ _ _ ge Mfloat32 m a rs ST0 sz
  | Pfstps_m a =>
      exec_store _ _ _ ge Mfloat32 m a rs ST0 (ST0 :: nil) sz
  | Pxchg_rr r1 r2 =>
      Next (nextinstr (rs#r1 <- (rs r2) #r2 <- (rs r1)) sz) m
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store _ _ _ ge Mint8unsigned m a rs r1 nil sz
  | Pmovw_mr a r1 =>
      exec_store _ _ _ ge Mint16unsigned m a rs r1 nil sz
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1)) sz) m
  | Pmovzb_rm rd a =>
      exec_load _ _ _ ge Mint8unsigned m a rs rd sz
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1)) sz) m
  | Pmovsb_rm rd a =>
      exec_load _ _ _ ge Mint8signed m a rs rd sz
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1)) sz) m
  | Pmovzw_rm rd a =>
      exec_load _ _ _ ge Mint16unsigned m a rs rd sz
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1)) sz) m
  | Pmovsw_rm rd a =>
      exec_load _ _ _ ge Mint16signed m a rs rd sz
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1)) sz) m
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1)) sz) m
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd)) sz) m
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1)) sz) m
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1)) sz) m
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1))) sz) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1))) sz) m
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1))) sz) m
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1))) sz) m
  | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1))) sz) m
  | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1))) sz) m
  | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1))) sz) m
  | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1))) sz) m
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 ge a rs)) sz) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 ge a rs)) sz) m
  | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd)) sz) m
  | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd)) sz) m
  | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n))) sz) m
  | Psubl_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd (Vint n))) sz) m
  | Paddq_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n))) sz) m
  | Psubq_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd (Vlong n))) sz) m
  | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1)) sz) m
  | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1)) sz) m
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1)) sz) m
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1)) sz) m
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n))) sz) m
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n))) sz) m
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1)) sz) m
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1)) sz) m
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1)) sz) m
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1)) sz) m
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31)))) sz) m
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63)))) sz) m
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1)) sz) m
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1)) sz) m
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n))) sz) m
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n))) sz) m
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1)) sz) m
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1)) sz) m
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n))) sz) m
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n))) sz) m
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero) sz) m
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero)) sz) m
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1)) sz) m
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1)) sz) m 
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n))) sz) m
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n))) sz) m
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd)) sz) m
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd)) sz) m
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#RCX)) sz) m
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd rs#RCX)) sz) m
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n))) sz) m
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd (Vint n))) sz) m
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX)) sz) m
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX)) sz) m
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n))) sz) m
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n))) sz) m
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX)) sz) m
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX)) sz) m
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n))) sz) m
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n))) sz) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n))))) sz) m
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n))) sz) m
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n))) sz) m
  | Pcmpl_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m) sz) m
  | Pcmpq_rr r1 r2 =>
      Next (nextinstr (compare_longs (rs r1) (rs r2) rs m) sz) m
  | Pcmpl_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m) sz) m
  | Pcmpq_ri r1 n =>
      Next (nextinstr (compare_longs (rs r1) (Vlong n) rs m) sz) m
  | Ptestl_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m) sz) m
  | Ptestq_rr r1 r2 =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs m) sz) m
  | Ptestl_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m) sz) m
  | Ptestq_ri r1 n =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs m) sz) m
  | Pcmov c rd r1 =>
      match eval_testcond c rs with
      | Some true => Next (nextinstr (rs#rd <- (rs#r1)) sz) m
      | Some false => Next (nextinstr rs sz) m
      | None => Next (nextinstr (rs#rd <- Vundef) sz) m
      end
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs))) sz) m
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1)) sz) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1)) sz) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1)) sz) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1)) sz) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd)) sz) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd)) sz) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs) sz) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero)) sz) m
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1)) sz) m
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1)) sz) m
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1)) sz) m
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1)) sz) m
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd)) sz) m
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd)) sz) m
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs) sz) m
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vsingle Float32.zero)) sz) m
  (** Branches and calls *)
  | Pjmp_l lbl => Stuck
  | Pjmp (inr id) sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmp (inl r) sg =>
      Next (rs#PC <- (rs r)) m
  | Pjcc cond lbl => Stuck
  | Pjcc2 cond1 cond2 lbl => Stuck
  | Pjmptbl r tbl => Stuck
 | Pcall ros sg =>
      let addr := eval_ros ge ros rs in
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
      match Mem.storev Mptr m sp (Val.offset_ptr rs#PC sz) with
      | None => Stuck
      | Some m2 =>
        Next (rs#RA <- (Val.offset_ptr rs#PC sz)
                #PC <- addr
                #RSP <- sp) m2
      end
  (* | Pcall (inr gloc) sg => *)
  (*     Next (rs#RA <- (Val.offset_ptr rs#PC sz) #PC <- (Genv.symbol_address ge gloc Ptrofs.zero)) m *)
  (* | Pcall (inl r) sg => *)
  (*     Next (rs#RA <- (Val.offset_ptr rs#PC sz) #PC <- (rs r)) m *)
  | Pret =>
        match Mem.loadv Mptr m rs#RSP with
      | None => Stuck
      | Some ra =>
        let sp := Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)) in
        Next (rs #RSP <- sp
                 #PC <- ra
                 #RA <- Vundef) m
      end

  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load _ _ _ ge (if Archi.ptr64 then Many64 else Many32) m a rs rd sz
  | Pmov_mr_a a r1 =>
      exec_store _ _ _ ge (if Archi.ptr64 then Many64 else Many32) m a rs r1 nil sz
  | Pmovsd_fm_a rd a =>
      exec_load _ _ _  ge Many64 m a rs rd sz
  | Pmovsd_mf_a a r1 =>
      exec_store _ _ _ ge Many64 m a rs r1 nil sz
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs sz) m
  | Pcfi_adjust n => Next rs m
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
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
  | _ => Stuck
  end.

Definition exec_instr {exec_load exec_store} `{!FlatAsm.MemAccessors exec_load exec_store} 
           (ge: genv) (ii: instr_with_info) (rs: regset) (m: mem) : outcome :=
  let '(i,blk,fid) := ii in
  let sz := segblock_size blk in
  match i with
  (* Jump instruction in MC *)
  | MCjmp_l ofs => goto_label ofs sz rs m
  | MCjcc cond ofs =>
    match eval_testcond cond rs with
    | Some true => goto_label ofs sz rs m
    | Some false => Next (nextinstr rs sz) m
    | None => Stuck
    end
  | MCjcc2 cond1 cond2 ofs =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label ofs sz rs m
      | Some _, Some _ => Next (nextinstr rs sz) m
      | _, _ => Stuck
      end    
  | MCjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some ofs => goto_label ofs sz (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  (* The rest instructions are forwarded to FlatAsm *)
  | MCAsminstr ins =>
    exec_flatasm_instr ge (segblock_size blk) ins rs m
  end.


Inductive step {exec_load exec_store} `{!MemAccessors exec_load exec_store} 
  (ge: genv) : state -> trace -> state -> Prop :=
| exec_step_internal:
    forall b ofs i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.genv_internal_codeblock ge b = true ->
      Genv.find_instr ge (Vptr b ofs) = Some i ->
      exec_instr ge i rs m = Next rs' m' ->
      step ge (State rs m) E0 (State rs' m')
| exec_step_builtin:
    forall fid b ofs ef args res rs m vargs t vres rs' m' blk,
      rs PC = Vptr b ofs ->
      Genv.genv_internal_codeblock ge b = true ->
      Genv.find_instr ge (Vptr b ofs) = Some (MCAsminstr (Pbuiltin ef args res), blk, fid)  ->
      eval_builtin_args _ _ _ preg ge rs (rs RSP) m args vargs ->
        external_call ef (Genv.genv_senv ge) vargs m t vres m' ->
      forall BUILTIN_ENABLED: builtin_enabled ef,
        rs' = nextinstr_nf
                (set_res res vres
                         (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) (segblock_size blk) ->
        step ge (State rs m) t (State rs' m')
| exec_step_external:
    forall b ofs ef args res rs m t rs' m',
      rs PC = Vptr b ofs ->
      Genv.genv_internal_codeblock ge b = false ->
      Genv.find_funct ge (Vptr b ofs) = Some (External ef) ->
      forall ra (LOADRA: Mem.loadv Mptr m (rs RSP) = Some ra)
        (RA_NOT_VUNDEF: ra <> Vundef)
        (ARGS: extcall_arguments (rs # RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)))) m (ef_sig ef) args),
        external_call ef (Genv.genv_senv ge) args m t res m' ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res
                          (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil)
                                      (undef_regs (map preg_of destroyed_at_call) rs)))
                  #PC <- ra
                  #RA <- Vundef
                  #RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr))) ->
        step ge (State rs m) t (State rs' m').

End WITHEXTERNALCALLS.
