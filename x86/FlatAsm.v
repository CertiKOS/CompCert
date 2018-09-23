(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

(** Abstract syntax and semantics for IA32 assembly language with a flat memory space **)

Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Segment FlatAsmGlobenv FlatAsmBuiltin.
Require Import Asm RawAsm.
Require Import Num.
Require Globalenvs.


Definition undef_segid: segid_type := 1%positive.
Definition data_segid:  segid_type := 3%positive.
Definition code_segid:  segid_type := 4%positive.

Definition num_segments: nat := 3.


Definition instr_with_info:Type := instruction * segblock * ident.

Definition code := list instr_with_info.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code; (* fn_frame: frame_info; *) fn_range:segblock}.
Definition fundef := AST.fundef function.
Definition gdef := globdef fundef unit.

(* mapping from global identifiers to segment labels *)
Definition GID_MAP_TYPE := ident -> option seglabel.
(* mapping from local labels to segment labels *)
Definition LABEL_MAP_TYPE := ident -> ident -> option seglabel.

(* The FlatAsm program *)
Record program : Type := {
  prog_defs: list (ident * option gdef * segblock);
  prog_public: list ident;
  prog_main: ident;
  data_seg: segment;  (* The data segment *)
  code_seg: segment * code; (* The code segment *)
  glob_map: GID_MAP_TYPE;
  lbl_map: LABEL_MAP_TYPE;
  prog_senv : Globalenvs.Senv.t;
}.


(** * Operational semantics *)

(* Definition regset := Asm.regset. *)
Definition genv := Genv.t fundef unit instr_with_info.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Asm.Pregmap.set b c a) (at level 1, b at next level) : asm.


Open Scope asm.

Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Section RELSEM.


Section WITHGE.

Context {F V I: Type}.
Variable ge: Genv.t F V I.
  
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

End WITHGE.


(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]).
  [nextinstr_nf] is a variant of [nextinstr] that sets condition flags
  to [Vundef] in addition to incrementing the [PC]. *)

Definition goto_label {F V I} (ge: Genv.t F V I) (fid:ident) (lbl: label) (rs: regset) (m: mem) :=
  Next (rs#PC <- (Genv.label_address ge fid lbl)) m.

(* Definition goto_label {F V I} (ge: Genv.t F V I) (fid: ident) (lbl: label) (rs: regset) (m: mem) := *)
(*   match Genv.genv_lbl ge fid lbl with *)
(*   | None => Stuck *)
(*   | Some (b, ofs) => *)
(*       match rs#PC with *)
(*       | Vptr b ofs => Next (rs#PC <- (Vptr b ofs)) m *)
(*       | _ => Stuck *)
(*     end *)
(*   end. *)


(** [CompCertiKOS:test-compcert-param-mem-accessors] For CertiKOS, we
need to parameterize over [exec_load] and [exec_store], which will be
defined differently depending on whether we are in kernel or user
mode. *)

Class MemAccessors
      `{!Mem.MemoryModelOps mem}
      (exec_load: forall F V I: Type, Genv.t F V I -> memory_chunk -> mem -> addrmode -> regset -> preg -> ptrofs -> outcome)
      (exec_store: forall F V I: Type, Genv.t F V I -> memory_chunk -> mem -> addrmode -> regset -> preg -> list preg -> ptrofs -> outcome)
: Prop := {}.

Section MEM_ACCESSORS_DEFAULT.

(** [CompCertiKOS:test-compcert-param-mem-accessors] Compcert does not
care about kernel vs. user mode, and uses its memory model to define
its memory accessors. *)

Definition exec_load {F V I} (ge: Genv.t F V I) (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) (sz:ptrofs):=
  match Mem.loadv chunk m (eval_addrmode ge a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v) sz) m
  | None => Stuck
  end.

Definition exec_store {F V I} (ge: Genv.t F V I) (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) (sz:ptrofs) :=
  match Mem.storev chunk m (eval_addrmode ge a rs) (rs r1) with
  | Some m' =>
    Next (nextinstr_nf (undef_regs destroyed rs) sz) m'
  | None => Stuck
  end.

Local Instance mem_accessors_default: MemAccessors (@exec_load) (@exec_store).

End MEM_ACCESSORS_DEFAULT.


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

Definition exec_instr {exec_load exec_store} `{!MemAccessors exec_load exec_store} (ge: genv) (ii: instr_with_info) (rs: regset) (m: mem) : outcome :=
  let '(i,blk,fid) := ii in
  let sz := segblock_size blk in
  match i with
  (** Moves *)
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
  | Pjmp_l lbl =>
      goto_label ge fid lbl rs m
  | Pjmp (inr id) sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmp (inl r) sg =>
      Next (rs#PC <- (rs r)) m
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label ge fid lbl rs m
      | Some false => Next (nextinstr rs sz) m
      | None => Stuck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label ge fid lbl rs m
      | Some _, Some _ => Next (nextinstr rs sz) m
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label ge fid lbl (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall (inr gloc) sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC sz) #PC <- (Genv.symbol_address ge gloc Ptrofs.zero)) m
  | Pcall (inl r) sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC sz) #PC <- (rs r)) m
  | Pret =>
  (** [CompCertX:test-compcert-ra-vundef] We need to erase the value of RA,
      which is actually popped away from the stack in reality. *)
      Next (rs#PC <- (rs#RA) #RA <- Vundef) m
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

(* (** Symbol environments are not used to describe the semantics of FlatAsm. However, we need to provide a dummy one to match the semantics framework of CompCert *) *)
(* Definition dummy_senv (ge:genv) := Globalenvs.Genv.to_senv (Globalenvs.Genv.empty_genv unit unit (Genv.genv_public ge)). *)

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
      Genv.find_instr ge (Vptr b ofs) = Some (Pbuiltin ef args res, blk, fid)  ->
      eval_builtin_args _ _ _ preg ge rs (rs RSP) m args vargs ->
        external_call ef (Genv.genv_senv ge) vargs m t vres m' ->
      forall BUILTIN_ENABLED: builtin_enabled ef,
        rs' = nextinstr_nf
                (set_res res vres
                         (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) (segblock_size blk) ->
        step ge (State rs m) t (State rs' m')
| exec_step_external:
    forall b ofs ef args res rs m t m2 rs' m',
      rs PC = Vptr b ofs ->
      Genv.genv_internal_codeblock ge b = false ->
      Genv.find_funct ge (Vptr b ofs) = Some (External ef) ->
      forall (* CompCertX: BEGIN additional conditions for calling convention *)
        (* (STACK: *)
        (*    exists m_, *)
        (*      free_extcall_args (rs RSP) m (regs_of_rpairs (Conventions1.loc_arguments (ef_sig ef))) = Some m_ /\ *)
        (*      exists t_ res'_ m'_, *)
        (*        external_call ef ge args m_ t_ res'_ m'_ *)
        (* ) *)
        (SP_TYPE: Val.has_type (rs RSP) Tptr)
        (RA_TYPE: Val.has_type (rs RA) Tptr)
        (SP_NOT_VUNDEF: rs RSP <> Vundef)
        (RA_NOT_VUNDEF: rs RA <> Vundef)
        (SZRA: Mem.storev Mptr m (Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))
                          (rs RA) = Some m2)
        (ARGS: extcall_arguments rs m2 (ef_sig ef) args)
      ,      (* CompCertX: END additional conditions for calling convention *)
        external_call ef (Genv.genv_senv ge) args m2 t res m' ->
        rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->
        step ge (State rs m) t (State rs' m').

End RELSEM.

(** Initialization of the global environment *)
Definition add_global (ge:genv) (idg: ident * option gdef * segblock) : genv :=
  let '(gid,gdef,blk) := idg in
  let gsymbs := 
      match gdef with
      | None 
      | Some (Gfun (External _)) =>
        fun id => if ident_eq id gid then Some (Genv.genv_next ge, Ptrofs.zero) else (Genv.genv_symb ge) id
      | _ => Genv.genv_symb ge 
      end
  in
  let gdefs :=
      match gdef with
      | None
      | Some (Gfun (External _)) =>
        (fun (b:block) (ofs:ptrofs) => 
          if (eq_block b (Genv.genv_next ge)) && (Ptrofs.eq ofs Ptrofs.zero)
          then gdef else Genv.genv_defs ge b ofs)
      | _ => Genv.genv_defs ge
      end
  in
  Genv.mkgenv
    (Genv.genv_public ge)
    gsymbs
    gdefs
    (Genv.genv_instrs ge)
    (Genv.genv_internal_codeblock ge)
    (Genv.genv_lbl ge)
    (Pos.succ (Genv.genv_next ge))
    (Genv.genv_senv ge).
  
                     
Fixpoint add_globals (ge:genv) (gl: list (ident * option gdef * segblock)) : genv :=
  match gl with
  | nil => ge
  | (idg::gl') => 
    let ge' := add_global ge idg in
    add_globals ge' gl'
  end. 

Lemma add_global_pres_genv_instrs: forall def ge ge',
  ge' = add_global ge def ->
  forall b ofs, Genv.genv_instrs ge b ofs = Genv.genv_instrs ge' b ofs.
Proof.
  intros def ge ge' H b ofs.
  subst. unfold add_global. destruct def. destruct p.
  destruct (Genv.genv_symb ge i) eqn:EQ.
  destruct p. auto. auto.
Qed.

Lemma add_globals_pres_genv_instrs: forall defs ge ge',
  ge' = add_globals ge defs ->
  forall b ofs, Genv.genv_instrs ge b ofs = Genv.genv_instrs ge' b ofs.
Proof.
  induction defs; simpl; intros.
  - subst. auto.
  - assert (Genv.genv_instrs ge b ofs = Genv.genv_instrs (add_global ge a) b ofs)
           by (eapply add_global_pres_genv_instrs; eauto).
    rewrite H0. apply IHdefs. auto.
Qed.

(* Lemma add_global_pres_genv_segblocks: forall def ge ge', *)
(*   ge' = add_global ge def -> *)
(*   forall id, Genv.genv_segblocks ge id = Genv.genv_segblocks ge' id. *)
(* Proof. *)
(*   intros def ge ge' H id. *)
(*   subst. unfold add_global. destruct def. destruct p. destruct o. *)
(*   destruct g. simpl. auto. auto. auto. *)
(* Qed. *)

(* Lemma add_globals_pres_genv_segblocks: forall defs ge ge', *)
(*   ge' = add_globals ge defs -> *)
(*   forall id, Genv.genv_segblocks ge id = Genv.genv_segblocks ge' id. *)
(* Proof. *)
(*   induction defs; simpl; intros. *)
(*   - subst. auto. *)
(*   - assert (Genv.genv_segblocks ge id = Genv.genv_segblocks (add_global ge a) id) *)
(*            by (eapply add_global_pres_genv_segblocks; eauto). *)
(*     rewrite H0. apply IHdefs. auto. *)
(* Qed. *)

Definition get_instr_ptr (smap:segid_type ->block) (i:instr_with_info): val :=
  let '(_,bi,_) := i in Genv.label_to_ptr smap (segblock_to_label bi).

Definition acc_instr_map (smap:segid_type -> block) (i:instr_with_info) map :
  block -> ptrofs -> option instr_with_info :=
  let ptr := get_instr_ptr smap i in
  fun b ofs => if Val.eq (Vptr b ofs) ptr then Some i else (map b ofs).

Fixpoint acc_instrs_map (smap:segid_type -> block) (c:code) map
  : block -> ptrofs -> option instr_with_info :=
  match c with
  | nil => map
  | i'::c' =>
    let map' := acc_instrs_map smap c' map in
    acc_instr_map smap i' map'
  end.

(* Get the segment labels of instructions *)
Definition code_labels (c:code) : list seglabel :=
  List.map (fun '(_,blk,_) => segblock_to_label blk) c.

Lemma incode_labels : forall i (c:code),
  In i c -> In (segblock_to_label (snd (fst i))) (code_labels c).
Proof.
  induction c; simpl; intros.
  - auto.
  - destruct H. subst. destruct i. destruct p. auto.
    right. apply IHc. auto.
Qed.

Definition code_labels_are_distinct (c: code) : Prop :=
  let labels := (map (fun '(_,blk,_) => segblock_to_label blk) c) in
  list_norepet labels.

Fixpoint pos_advance_N (p:positive) (n:nat) : positive :=
  match n with
  | O => p
  | Datatypes.S n' => pos_advance_N (Psucc p) n'
  end.

Lemma psucc_advance_Nsucc_eq : forall n p,
  pos_advance_N (Pos.succ p) n = Pos.succ (pos_advance_N p n).
Proof.
  induction n; intros.
  - simpl. auto.
  - simpl. rewrite IHn. auto.
Qed.

Lemma pos_advance_N_ple : forall p n,
  Ple p (pos_advance_N p n).
Proof.
  induction n; intros.
  - simpl. apply Ple_refl.
  - simpl.
    rewrite psucc_advance_Nsucc_eq.
    apply Ple_trans with (pos_advance_N p n); auto. apply Ple_succ.
Qed.


(* The following are definitions and properties for segment blocks *)
(*    and the mapping from segment ids to segment blocks. They are necessary *)
(*    for proving invariants of the transformation from RawAsm to FlatAsm. *)
(*  *)
Section WITHSEGSLENGTH.

Variable init_block : block. (* The smallest segment block *)
Variable segs_length : nat.   (* The number of segments in a program *)


(* Definition of valid blocks for segments.  A segment block is valid if its id is  *)
(*    greater or equal to 'init_block' and less than 'init_block + segs_length' *)
Definition segblock_is_valid (b:block) : Prop :=
  Ple init_block b /\ Plt b (pos_advance_N init_block segs_length).

Lemma init_segblock_is_valid :
  (segs_length <> 0)%nat -> segblock_is_valid init_block.
Proof.
  clear. red. split. apply Ple_refl.
  destruct segs_length. congruence. simpl.
  rewrite psucc_advance_Nsucc_eq.
  apply Pos.le_lt_trans with (pos_advance_N init_block n).
  apply pos_advance_N_ple. apply Plt_succ.
Qed.

(* With its range restricted to valid blocks, a mapping from  *)
(*    segment ids to blocks is injective *)
Definition injective_on_valid_segs (sbmap: segid_type -> block) : Prop :=
  forall s1 s2, sbmap s1 = sbmap s2 -> segblock_is_valid (sbmap s1) -> s1 = s2.

(* A mapping from segment ids to blocks maps code labels to valid blocks *)
Definition code_labels_are_valid (sbmap: segid_type -> block) (c:code) : Prop :=
  forall i sblk fid, In (i,sblk,fid) c -> segblock_is_valid (sbmap (segblock_id sblk)).

Lemma code_labels_are_valid_cons_inv : forall sbmap a l,
    code_labels_are_valid sbmap (a :: l) ->
    segblock_is_valid (sbmap (segblock_id (snd (fst a))))
    /\ code_labels_are_valid sbmap l.
Proof.
  unfold code_labels_are_valid.
  intros sbmap a l VALID. split.
  - destruct a.  destruct p.  simpl. eapply VALID; eauto. apply in_eq.
  - intros i sblk fid IN. eapply VALID. apply in_cons. eauto.
Qed.

Lemma code_labels_are_valid_cons : forall sbmap a l,
    segblock_is_valid (sbmap (segblock_id (snd (fst a)))) ->
    code_labels_are_valid sbmap l ->
    code_labels_are_valid sbmap (a :: l).
Proof.
  unfold code_labels_are_valid.
  intros sbmap a l SVALID VALID i sblk fid IN. simpl in IN.
  destruct IN.
  - subst. simpl in *. auto.
  - eapply VALID; eauto.
Qed.
  
Lemma code_labels_are_valid_app : forall sbmap l1 l2,
    code_labels_are_valid sbmap l1 ->
    code_labels_are_valid sbmap l2 ->
    code_labels_are_valid sbmap (l1 ++ l2).
Proof.
  induction l1; intros; simpl in *.
  - auto.
  - apply code_labels_are_valid_cons_inv in H. destruct H.
    assert (code_labels_are_valid sbmap (l1 ++ l2))
      by (apply IHl1; auto).
    apply code_labels_are_valid_cons; auto.
Qed.

Lemma code_labels_are_valid_eq_map : forall sbmap sbmap' l,
    (forall id, sbmap id = sbmap' id) ->
    code_labels_are_valid sbmap l ->
    code_labels_are_valid sbmap' l.
Proof.
  induction l; simpl.
  - intros EQMAP VALID. red. intros. contradiction.
  - intros EQMAP VALID.
    apply code_labels_are_valid_cons_inv in VALID. destruct VALID.
    apply code_labels_are_valid_cons; auto.
    rewrite <- EQMAP. auto.
Qed.

End WITHSEGSLENGTH.

(* Given  *)
(*    - 'sbmap': a mapping that maps segment ids to blocks and that *)
(*               is injective for ids mapped on valid blocks *)
(*    - 'c':     a list of instructions residing in segments mapped into *)
(*               valid blocks by 'sbmap' *)
(*    - 'i':     an instruction in 'c' *)
   
(*    if the code labels for instructions in 'c' are all distinct, then *)
(*    the instruction mapping from pairs of segment blocks and offsets *)
(*    generated by 'acc_instrs_map' maps the pair of segment block  *)
(*    and offset for 'i' (determined by 'sbmap') to 'i' itself *)
(* *)
Lemma acc_instrs_map_self : forall init_block slen i c map map' sbmap,
  injective_on_valid_segs init_block slen sbmap ->
  In i c ->
  code_labels_are_distinct c ->
  code_labels_are_valid init_block slen sbmap c ->
  map' = acc_instrs_map sbmap c map ->
  map' (sbmap (segblock_id (snd (fst i)))) (segblock_start (snd (fst i))) = Some i.
Proof.
  induction c; simpl; intros.
  - contradiction.
  - destruct H0.
    + subst. unfold acc_instr_map.
      unfold get_instr_ptr. destruct i. simpl. unfold Genv.label_to_ptr.
      unfold segblock_to_label. simpl. destruct Val.eq. auto.
      destruct p. simpl in *. congruence.
    + subst. unfold acc_instr_map. destruct Val.eq.
      * unfold get_instr_ptr in e. destruct a. destruct p; simpl in *. 
        unfold Genv.label_to_ptr in e.
        unfold segblock_to_label in e. simpl in e.
        inv e. unfold injective_on_valid_segs in H.
        exploit H; eauto.
        unfold code_labels_are_valid in H2. 
        destruct i. destruct p. simpl in *. eapply H2.
        right. eauto. intros.
        destruct i. destruct p. simpl in *.
        assert (segblock_to_label s0 = segblock_to_label s).
        unfold segblock_to_label. f_equal; auto.
        simpl in H1. inv H1. rewrite <- H6 in *.
        apply incode_labels in H0. unfold code_labels in H0. 
        simpl in H0. congruence.
      * eapply IHc; eauto. inv H1. auto. destruct a. destruct p. inv H1.
        unfold code_labels_are_valid in *. intros i2 sblk fid H1.
        eapply H2. apply in_cons. eauto.
Qed.

(* Generate a mapping from offsets to instructions *)
Definition gen_instrs_map (smap:segid_type -> block) (p:program)
  : block -> ptrofs -> option instr_with_info :=
  acc_instrs_map smap (snd (code_seg p)) (fun b ofs => None).
  
(* Generate a function for checking if pc points to an internal instruction *)
Definition gen_internal_codeblock (smap:segid_type -> block) (p:program) : block -> bool:=
  let code_seg_id := segid (fst (p.(code_seg))) in
  fun b => eq_block b (smap code_seg_id).

Fixpoint acc_segblocks (nextblock: block) (ids: list segid_type) (map: segid_type -> block)
  : (segid_type -> block) :=
  match ids with
  | nil => map
  | id::ids' =>
    let map' := acc_segblocks (Psucc nextblock) ids' map in
    (fun x => if ident_eq x id then nextblock else map' x)
  end.

Definition list_of_segments (p:program) : list segment  :=
  (p.(data_seg) :: (fst p.(code_seg)) :: nil).

Definition undef_seg_block := 1%positive.
Definition code_block := 2%positive.
Definition data_block := 3%positive.
(* Definition init_glob_block := 4%positive. *)

(* Definition gen_segblocks (p:program) : (segid_type -> block) := *)
(*   let initmap := fun id => undef_seg_block in *)
(*   let ids := List.map segid (list_of_segments p) in *)
(*   acc_segblocks init_block ids initmap. *)

(* Lemma acc_segblocks_upper_bound : forall l i f, *)
(*   (forall id, Plt (f id) i) -> *)
(*   (forall id, Plt (acc_segblocks i l f id) (pos_advance_N i (length l))). *)
(* Proof. *)
(*   induction l; intros. *)
(*   - simpl in *. auto. *)
(*   - simpl in *. destruct ident_eq. *)
(*     + rewrite psucc_advance_Nsucc_eq. apply Pos.le_lt_trans with (pos_advance_N i (Datatypes.length l)). *)
(*       apply pos_advance_N_ple. apply Plt_succ. *)
(*     + apply IHl. intros. apply Plt_trans with i. apply H. *)
(*       apply Plt_succ. *)
(* Qed. *)

(* Lemma gen_segblocks_upper_bound : forall p id, *)
(*   Plt (gen_segblocks p id) (pos_advance_N init_block (length (list_of_segments p))). *)
(* Proof. *)
(*   intros. unfold gen_segblocks. *)
(*   eapply acc_segblocks_upper_bound; eauto. *)
(*   intros. unfold undef_seg_block, init_block. apply Plt_succ. *)
(* Qed. *)

(* (* The ids used to create a mapping from segment ids to blocks  *) *)
(* (*    are indeed mapped to valid blocks by the mapping*) *)
(* Lemma acc_segblocks_in_valid: forall ids id sbmap initb initmap, *)
(*   In id ids -> *)
(*   sbmap = acc_segblocks initb ids initmap -> *)
(*   segblock_is_valid initb (length ids) (sbmap id). *)
(* Proof. *)
(*   clear. *)
(*   induction ids. intros. *)
(*   - inv H. *)
(*   - intros id sbmap initb initmap H H0. simpl in H. destruct H. *)
(*     subst. simpl. destruct ident_eq. *)
(*     apply init_segblock_is_valid. omega. congruence. *)
(*     simpl in H0. subst. destruct ident_eq. *)
(*     apply init_segblock_is_valid. simpl. omega. *)
(*     exploit (IHids id (acc_segblocks (Pos.succ initb) ids initmap)); eauto. *)
(*     intros VALID. unfold segblock_is_valid in *.  destruct VALID. *)
(*     split. apply Ple_trans with (Pos.succ initb); auto. *)
(*     apply Ple_succ. simpl. *)
(*     auto. *)
(* Qed. *)
    
(* Lemma gen_segblocks_in_valid : forall p id sbmap, *)
(*   In id (map segid (list_of_segments p)) -> *)
(*   sbmap = gen_segblocks p -> *)
(*   segblock_is_valid init_block (length (list_of_segments p)) (sbmap id). *)
(* Proof. *)
(*   clear. *)
(*   intros p id sbmap H H0. *)
(*   assert (length (list_of_segments p) = length (map segid (list_of_segments p))). *)
(*   { rewrite list_length_map. auto. } *)
(*   rewrite H1. unfold gen_segblocks in H0. *)
(*   eapply acc_segblocks_in_valid; eauto. *)
(* Qed. *)

(* Lemma acc_segblocks_range: forall ids b initb initmap s, *)
(*   b = (acc_segblocks initb ids initmap s) -> *)
(*   b = (initmap s) \/ segblock_is_valid initb (length ids) b. *)
(* Proof. *)
(*   induction ids; simpl; intros. *)
(*   - auto. *)
(*   - destruct ident_eq; subst. *)
(*     + right. red. split. apply Ple_refl. *)
(*       simpl. rewrite psucc_advance_Nsucc_eq. *)
(*       apply Pos.le_lt_trans with (pos_advance_N initb (Datatypes.length ids)). *)
(*       apply pos_advance_N_ple. apply Plt_succ. *)
(*     + exploit (IHids (acc_segblocks (Pos.succ initb) ids initmap s)); eauto. *)
(*       intros [ACC | VALID]. *)
(*       auto. right. unfold segblock_is_valid in *. destruct VALID. *)
(*       split. apply Ple_trans with (Pos.succ initb); auto. apply Ple_succ. *)
(*       simpl. auto. *)
(* Qed. *)

(* Lemma acc_segblocks_absurd : forall ids b initb initmap s, *)
(*   (forall s, Plt (initmap s) b) -> Plt b initb -> *)
(*   b = (acc_segblocks initb ids initmap s) -> False. *)
(* Proof. *)
(*   intros. apply acc_segblocks_range in H1. destruct H1. *)
(*   - subst. specialize (H s). specialize (Plt_strict (initmap s)). *)
(*     congruence. *)
(*   - red in H1. destruct H1. generalize (Plt_le_absurd b initb); eauto. *)
(* Qed. *)

(* Lemma acc_segblocks_injective : forall ids init_block0 initmap sbmap, *)
(*     (forall s, Plt (initmap s) init_block0) -> *)
(*     sbmap = acc_segblocks init_block0 ids initmap -> *)
(*     injective_on_valid_segs init_block0 (length ids) sbmap. *)
(* Proof. *)
(*   induction ids; intros. *)
(*   - simpl in *. subst. red. *)
(*     intros s1 s2 EQ VALID. *)
(*     red in VALID. simpl in VALID. *)
(*     destruct VALID as [VALID1 VALID2]. exfalso. *)
(*     generalize (Plt_le_absurd (initmap s1) init_block0); eauto. *)
(*   - simpl in H0. subst. red. intros. repeat destruct ident_eq. *)
(*     + subst. auto. *)
(*     + red in H1. destruct H1. *)
(*       exfalso. eapply (acc_segblocks_absurd ids init_block0 (Psucc init_block0)); eauto. *)
(*       apply Pos.lt_succ_r. apply Ple_refl. *)
(*     + red in H1. destruct H1. *)
(*       exfalso. eapply (acc_segblocks_absurd ids init_block0 (Psucc init_block0)); eauto. *)
(*       apply Pos.lt_succ_r. apply Ple_refl. *)
(*     + set (sbmap := acc_segblocks (Pos.succ init_block0) ids initmap) in *. *)
(*       generalize (IHids (Pos.succ init_block0) initmap sbmap). intros. *)
(*       exploit H2; eauto. intros. apply Plt_trans_succ. auto. *)
(*       set (b1 := sbmap s1) in *. *)
(*       assert (b1 = sbmap s2) by auto. subst sbmap. *)
(*       apply acc_segblocks_range in H3. destruct H3; auto. *)
(*       red in H1. destruct H1. specialize (H s2). rewrite <- H3 in H. *)
(*       exfalso. generalize (Plt_le_absurd b1 init_block0); eauto. *)
(* Qed. *)

(* Lemma gen_segblocks_injective : forall p, *)
(*     injective_on_valid_segs init_block (length (list_of_segments p)) (gen_segblocks p). *)
(* Proof. *)
(*   intros p. set (sbmap := gen_segblocks p) in *. *)
(*   unfold gen_segblocks in *. *)
(*   assert (length (list_of_segments p) = length (map segid (list_of_segments p))). *)
(*   symmetry. apply list_length_map. rewrite H. *)
(*   eapply acc_segblocks_injective; eauto. *)
(*   instantiate (1:=(fun _ : segid_type => undef_seg_block)). intros. simpl. *)
(*   apply Plt_succ. auto. *)
(* Qed. *)


Definition empty_genv (p:program): genv :=
  Genv.mkgenv (prog_public p) (fun id => None) (fun b ofs => None) (fun b ofs => None) (fun b => false)
              (fun fid lbl => None) 1%positive (prog_senv p).

Definition gidmap_to_symbmap (smap: segid_type -> block) (gmap:GID_MAP_TYPE) :=
  fun id =>
    match gmap id with
    | None => None
    | Some (sid,ofs) => Some (smap sid, ofs)
    end.

Definition lblmap_to_symbmap (smap: segid_type -> block) (lmap:LABEL_MAP_TYPE) :=
  fun fid lbl =>
    match lmap fid lbl with
    | None => None
    | Some (sid,ofs) => Some (smap sid, ofs)
    end.

Definition segmap := 
  fun sid => if eq_block sid code_segid then 
            code_block 
          else 
            if eq_block sid data_segid then
              data_block
            else
              undef_seg_block.

Lemma segmap_injective: 
  injective_on_valid_segs code_block 2 segmap.
Proof.
  clear.
  unfold segmap. red. intros.
  repeat destruct eq_block; subst; auto.
  unfold data_block, code_block in H. admit.
  unfold code_block, undef_seg_block in H. admit.
  unfold data_block, code_block in H. admit.
  unfold data_block, undef_seg_block in H. admit.
  unfold undef_seg_block, code_block in H. admit.
  unfold data_block, undef_seg_block in H. admit.
  unfold segblock_is_valid in H0. inv H0. admit.
Admitted.

Definition globalenv (p: program) : genv :=
  let smap := segmap in
  let symbmap := gidmap_to_symbmap smap (glob_map p) in
  let lblmap := lblmap_to_symbmap smap (lbl_map p) in
  let imap := gen_instrs_map smap p in
  let nextblock := Pos.of_succ_nat num_segments in
  let cbmap := gen_internal_codeblock smap p in
  let genv := Genv.mkgenv (prog_public p) symbmap (fun b ofs => None) imap cbmap lblmap nextblock (prog_senv p) in
  add_globals genv p.(prog_defs).
  
(* (** Initialization of the memory *) *)
(* Definition mem_block_size : Z := *)
(*   if Archi.ptr64 then two_power_nat 64 else two_power_nat 32. *)

(* Lemma genv_gen_segblocks:  forall p sid, *)
(*   Genv.genv_segblocks (globalenv p) sid = gen_segblocks p sid. *)
(* Proof. *)
(*   unfold globalenv. intros p sid. *)
(*   erewrite <- add_globals_pres_genv_segblocks; eauto. simpl. auto. *)
(* Qed. *)

Section WITHGE.

Variable ge:genv.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof gloc ofs => Mem.store Mptr m b p (Genv.symbol_address ge gloc ofs)
  | Init_space n => Some m
  end.

Fixpoint store_init_data_list (m: mem) (b: block) (p: Z) (idl: list init_data)
                              {struct idl}: option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m b p id with
      | None => None
      | Some m' => store_init_data_list m' b (p + init_data_size id) idl'
      end
  end.

(* Allocate global definitions like in previous assembly language.
   Even though the internal function and data definitions will reside
   in data and code segments, we still allocate blocks for them to
   make the memory injection easy to define 
*)
Definition alloc_global (m: mem) (idg: ident * option gdef * segblock): option mem :=
  let '(id, gdef, sb) := idg in
  match gdef with
  | None => 
    let (m1, b) := Mem.alloc m 0 0 in
    Some m1
  | Some (Gfun f) =>
    (** The block allocated for the internal function is dummy.
        Internal function actually reside in the block for the code segment. *)
    let (m1, b) := Mem.alloc m 0 1 in
    Mem.drop_perm m1 b 0 1 Nonempty
  | Some (Gvar v) =>
    (** The block allocated for the data is dummy.
        Data actually reside in the block for the code segment. *)
    let (m1, b) := Mem.alloc m 0 0 in
    Some m1 
  end.

Fixpoint alloc_globals (m: mem) (gl: list (ident * option gdef * segblock))
                       {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_global m g with
      | None => None
      | Some m' => alloc_globals m' gl'
      end
  end.

Definition store_global (smap:segid_type -> block) (m: mem) (idg: ident * option gdef * segblock): option mem :=
  let '(id, gdef, sb) := idg in
  let ofs := Ptrofs.unsigned (segblock_start sb) in
  let sz := Ptrofs.unsigned (segblock_size sb) in
  let b := smap (segblock_id sb) in
  match gdef with
  | None => Some m
  | Some (Gfun f) =>
    match f with
    | External _ => Some m
    | Internal f =>
      Mem.drop_perm m b ofs (ofs + sz) Nonempty
    end
  | Some (Gvar v) =>
    let init := gvar_init v in
    let isz := init_data_list_size init in
    match Globalenvs.store_zeros m b ofs isz with
    | None => None
    | Some m1 =>
      match store_init_data_list m1 b ofs init with
      | None => None
      | Some m2 => Mem.drop_perm m2 b ofs (ofs+isz) (Globalenvs.Genv.perm_globvar v)
      end
    end
  end.

Fixpoint store_globals (smap:segid_type->block) (m: mem) (gl: list (ident * option gdef * segblock))
                       {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match store_global smap m g with
      | None => None
      | Some m' => store_globals smap m' gl'
      end
  end.

End WITHGE.

(* Fixpoint alloc_segments m (segs: list segment) := *)
(*   match segs with *)
(*   | nil => m *)
(*   | s :: segs' => *)
(*     match Mem.alloc m 0 (Ptrofs.unsigned (segsize s)) with *)
(*     | (m',_) => alloc_segments m' segs' *)
(*     end *)
(*   end. *)

Definition alloc_segment m seg := Mem.alloc m 0 (Ptrofs.unsigned (segsize seg)).

Definition init_mem (p: program) :=
  let ge := globalenv p in
  let (initm,_) := Mem.alloc Mem.empty 0 0 in (** *r A dummy block is allocated for undefined segments *)
  (* let m := alloc_segments initm (list_of_segments p) in *)
  let (m1,_) := alloc_segment initm (fst (code_seg p)) in
  let (m2,_) := alloc_segment m1 (data_seg p) in
  match alloc_globals m2 (prog_defs p) with
  | None => None
  | Some m3 =>
    store_globals ge segmap m3 (prog_defs p)
  end.



(** Execution of whole programs. *)
(* Definition get_seg_block (id:ident) (l: list (ident * option gdef * segblock)) : option segblock := *)
(*   match (List.find (fun '(id',_,_) => ident_eq id id') l) with *)
(*   | None => None *)
(*   | Some (_,_,sb) => Some sb *)
(*   end. *)

(* Definition get_main_fun_ptr (ge:genv) (p:program) : val := *)
(*   match get_seg_block (prog_main p) (prog_defs p) with *)
(*   | None => Vundef *)
(*   | Some sb => (Genv.symbol_address ge (segblock_to_label sb) Ptrofs.zero) *)
(*   end. *)

(* Definition init_rsp (ge:genv) (p:program) : val := *)
(*   Vptr (Genv.genv_segblocks ge (segid (p.(stack_seg)))) *)
(*        (segsize (p.(stack_seg))). *)

Inductive initial_state_gen (p: program) (rs: regset) m: state -> Prop :=
  | initial_state_gen_intro:
      forall m1 m2 m3 bstack
      (MALLOC: Mem.alloc (Mem.push_new_stage m) 0 (Mem.stack_limit + align (size_chunk Mptr) 8) = (m1,bstack))
      (MDROP: Mem.drop_perm m1 bstack 0 (Mem.stack_limit + align (size_chunk Mptr) 8) Writable = Some m2)
      (MRSB: Mem.record_stack_blocks m2 (make_singleton_frame_adt' bstack frame_info_mono 0) = Some m3),
      let ge := (globalenv p) in
      let rs0 :=
        rs # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
           # RA <- Vnullptr
           # RSP <- (Vptr bstack (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8))) in
      initial_state_gen p rs m (State rs0 m3).

Inductive initial_state (prog: program) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall m,
    init_mem prog = Some m ->
    initial_state_gen prog rs m s ->
    initial_state prog rs s.

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#RAX = Vint r ->
      final_state (State rs m) r.

Local Existing Instance mem_accessors_default.

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen step (initial_state p rs) final_state (globalenv p) (Genv.genv_senv (globalenv p)).

(* (** Determinacy of the [Asm] semantics. *) *)

(* Remark extcall_arguments_determ: *)
(*   forall rs m sg args1 args2, *)
(*   extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2. *)
(* Proof. *)
(*   intros until m. *)
(*   assert (A: forall l v1 v2, *)
(*              extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2). *)
(*   { intros. inv H; inv H0; congruence. } *)
(*   assert (B: forall p v1 v2, *)
(*              extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2). *)
(*   { intros. inv H; inv H0.  *)
(*     eapply A; eauto. *)
(*     f_equal; eapply A; eauto. } *)
(*   assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 -> *)
(*              forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2). *)
(*   { *)
(*     induction 1; intros vl2 EA; inv EA. *)
(*     auto. *)
(*     f_equal; eauto. } *)
(*   intros. eapply C; eauto. *)
(* Qed. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
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
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
+ assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H4. eexact H9. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. assert (m = m0) by congruence. subst. inv H2; inv H3.
  assert (m1 = m4 /\ bstack = bstack0) by intuition congruence. destruct H0; subst.
  assert (m2 = m5) by congruence. subst.
  f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

End WITHEXTERNALCALLS.

