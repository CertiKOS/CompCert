(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 6, 2019  *)
(* *******************  *)

(** * The semantics of relocatable program using both the symbol and the relocation tables *)

(** The key feature of this semantics: it uses mappings from the
    offsets of global symbols in their corresponding sections to
    memory locations in deciding their memory addresses. These
    mappings are calculated by using both the symobl and the
    relocation tables *)

Require Import Coqlib Maps AST Integers Values.
Require Import Events Floats Memory Smallstep.
Require Import Asm RelocProgram RawAsm Globalenvs.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Linking SeqTable Errors.
Require RelocProgSemantics Reloctablesgen.
Require Import LocalLib.
(** Global environments *)

Definition gdef := globdef Asm.fundef unit.

Module Genv.

Section GENV.

Record t: Type := mkgenv {
  genv_reloc_ofs_symb: reloctable_id -> ZTree.t ident;
  genv_genv : RelocProgSemantics.Genv.t;
}.

(** ** Lookup functions *)

Definition find_symbol (ge: t) (sec_index: reloctable_id) (idofs: Z) : option (block * ptrofs):=
  let ge' := ge.(genv_genv) in
  let ofs_map :=  ge.(genv_reloc_ofs_symb) sec_index in
  match ZTree.get idofs ofs_map with
  | None => None
  | Some id => RelocProgSemantics.Genv.find_symbol ge' id
  end.

Definition symbol_address (ge: t) (sec_index: reloctable_id) (idofs: Z) (ofs: ptrofs) : val :=
  match find_symbol ge sec_index idofs with
  | Some (b, o) => Vptr b (Ptrofs.add ofs o)
  | None => Vundef
  end.

Definition find_ext_funct (ge: t) (v:val) : option external_function :=
  RelocProgSemantics.Genv.find_ext_funct (genv_genv ge) v.

(* Lemma symbol_address_offset : forall ge ofs1 b s ofs, *)
(*     symbol_address ge s Ptrofs.zero = Vptr b ofs -> *)
(*     symbol_address ge s ofs1 = Vptr b (Ptrofs.add ofs ofs1). *)
(* Proof. *)
(*   unfold symbol_address. intros.  *)
(*   destruct (find_symbol ge s) eqn:FSM. *)
(*   -  *)
(*     destruct p. *)
(*     inv H. *)
(*     rewrite Ptrofs.add_zero_l. rewrite Ptrofs.add_commut. auto. *)
(*   -  *)
(*     inv H. *)
(* Qed. *)

(* Lemma find_sym_to_addr : forall (ge:t) id b ofs, *)
(*     find_symbol ge id = Some (b, ofs) -> *)
(*     symbol_address ge id Ptrofs.zero = Vptr b ofs. *)
(* Proof. *)
(*   intros. unfold symbol_address. rewrite H. *)
(*   rewrite Ptrofs.add_zero_l. auto. *)
(* Qed. *)

Definition find_instr (ge: t) (v:val) : option instruction :=
  RelocProgSemantics.Genv.find_instr (genv_genv ge) v.

(* Definition to_reloc_prog_genv (ge:t) := genv_genv ge. *)

End GENV.

End Genv.

(* Coercion Genv.to_reloc_prog_genv: Genv.t >-> RelocProgSemantics.Genv.t. *)

(** Evaluating an addressing mode *)

Section WITHGE.

Variable ge: Genv.t.

Definition eval_addrmode32 (idofs: option Z) (a: addrmode) (rs: regset) : val :=
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
            | inr(id, ofs) => 
              match idofs with
              | None => Vundef
              | Some idofs =>
                Genv.symbol_address ge RELOC_CODE idofs ofs
              end
            end)).

Definition eval_addrmode64 (idofs:option Z) (a: addrmode) (rs: regset) : val :=
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
            | inr(id, ofs) => 
              match idofs with
              | None => Vundef
              | Some idofs =>
                Genv.symbol_address ge RELOC_CODE idofs ofs
              end
            end)).

Definition eval_addrmode (idofs: option Z) (a: addrmode) (rs: regset) : val :=
  if Archi.ptr64 then eval_addrmode64 idofs a rs else eval_addrmode32 idofs a rs.

End WITHGE.

Definition exec_load (ge: Genv.t) (chunk: memory_chunk) (m: mem)
                     (idofs: option Z) (a: addrmode) (rs: regset) 
                     (rd: preg) (sz:ptrofs):=
  match Mem.loadv chunk m (eval_addrmode ge idofs a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v) sz) m
  | None => Stuck
  end.

Definition exec_store (ge: Genv.t) (chunk: memory_chunk) (m: mem)
                      (idofs: option Z) (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) (sz:ptrofs) :=
  match Mem.storev chunk m (eval_addrmode ge idofs a rs) (rs r1) with
  | Some m' =>
    Next (nextinstr_nf (undef_regs destroyed rs) sz) m'
  | None => Stuck
  end.

Open Scope asm.

Definition eval_ros (ge : Genv.t) (idofs: option Z) (ros : ireg + ident) (rs : regset) :=
  match ros with
  | inl r => rs r
  | inr _ => 
    match idofs with
    | None => Vundef
    | Some idofs => Genv.symbol_address ge RELOC_CODE idofs Ptrofs.zero
    end
  end.

(** Execution of instructions *)

Definition get_pc_offset (rs:regset) : option Z :=
  match rs#PC with
  | Vptr _ ofs => Some (Ptrofs.unsigned ofs)
  | _ => None
  end.

Definition id_reloc_offset sofs (i:instruction) : option Z :=
  match Reloctablesgen.instr_reloc_offset i with
  | Error _ => None
  | OK ofs => Some (sofs + ofs)
  end.

Definition exec_instr (ge: Genv.t) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match get_pc_offset rs with
  | None => Stuck
  | Some ofs => 
    let sz := Ptrofs.repr (instr_size i) in 
    let idofs := id_reloc_offset ofs i in
    match i with
    (** Moves *)
    | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) sz) m
    | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n)) sz) m
    | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n)) sz) m
    | Pmov_rs rd id =>
      match idofs with
      | None => Stuck
      | Some idofs => 
        let symbaddr := (Genv.symbol_address ge RELOC_CODE idofs Ptrofs.zero) in
        Next (nextinstr_nf (rs#rd <- symbaddr) sz) m
      end
    | Pmovl_rm rd a =>
      exec_load ge Mint32 m idofs a rs rd sz
    | Pmovq_rm rd a =>
      exec_load ge Mint64 m idofs a rs rd sz
    | Pmovl_mr a r1 =>
      exec_store ge Mint32 m idofs a rs r1 nil sz
    | Pmovq_mr a r1 =>
      exec_store ge Mint64 m idofs a rs r1 nil sz
    | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) sz) m
    | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n)) sz) m
    | Pmovsd_fm rd a =>
      exec_load ge Mfloat64 m idofs a rs rd  sz
    | Pmovsd_mf a r1 =>
      exec_store ge Mfloat64 m idofs a rs r1 nil sz
    | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n)) sz) m
    | Pmovss_fm rd a =>
      exec_load ge Mfloat32 m idofs a rs rd sz
    | Pmovss_mf a r1 =>
      exec_store ge Mfloat32 m idofs a rs r1 nil sz
    | Pfldl_m a =>
      exec_load ge Mfloat64 m idofs a rs ST0 sz
    | Pfstpl_m a =>
      exec_store ge Mfloat64 m idofs a rs ST0 (ST0 :: nil) sz
    | Pflds_m a =>
      exec_load ge Mfloat32 m idofs a rs ST0 sz
    | Pfstps_m a =>
      exec_store ge Mfloat32 m idofs a rs ST0 (ST0 :: nil) sz
    | Pxchg_rr r1 r2 =>
      Next (nextinstr (rs#r1 <- (rs r2) #r2 <- (rs r1)) sz) m
    (** Moves with conversion *)
    | Pmovb_mr a r1 =>
      exec_store ge Mint8unsigned m idofs a rs r1 nil sz
    | Pmovw_mr a r1 =>
      exec_store ge Mint16unsigned m idofs a rs r1 nil sz
    | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1)) sz) m
    | Pmovzb_rm rd a =>
      exec_load ge Mint8unsigned m idofs a rs rd sz
    | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1)) sz) m
    | Pmovsb_rm rd a =>
      exec_load ge Mint8signed m idofs a rs rd sz
    | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1)) sz) m
    | Pmovzw_rm rd a =>
      exec_load ge Mint16unsigned m idofs a rs rd sz
    | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1)) sz) m
    | Pmovsw_rm rd a =>
      exec_load ge Mint16signed m idofs a rs rd sz
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
      Next (nextinstr (rs#rd <- (eval_addrmode32 ge idofs a rs)) sz) m
    | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 ge idofs a rs)) sz) m
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
    | Pjmp_l_rel ofs =>
      RelocProgSemantics.goto_ofs sz ofs rs m
    | Pjmp (inr id) sg =>
      match idofs with
      | None => Stuck
      | Some idofs =>
        let symbaddr := (Genv.symbol_address ge RELOC_CODE idofs Ptrofs.zero) in
        Next (rs#PC <- symbaddr) m
      end
    | Pjmp (inl r) sg =>
      Next (rs#PC <- (rs r)) m
    | Pjcc_rel cond ofs =>
      match eval_testcond cond rs with
      | Some true => RelocProgSemantics.goto_ofs sz ofs rs m
      | Some false => Next (nextinstr rs sz) m
      | None => Stuck
      end
    | Pjcc2_rel cond1 cond2 ofs =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => RelocProgSemantics.goto_ofs sz ofs rs m
      | Some _, Some _ => Next (nextinstr rs sz) m
      | _, _ => Stuck
      end
    | Pjmptbl_rel r tbl =>
      match rs#r with
      | Vint n =>
        match list_nth_z tbl (Int.unsigned n) with
        | None => Stuck
        | Some ofs => RelocProgSemantics.goto_ofs sz ofs (rs #RAX <- Vundef #RDX <- Vundef) m
        end
      | _ => Stuck
      end
    | Pcall ros sg =>
      let addr := eval_ros ge idofs ros rs in
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
      exec_load ge (if Archi.ptr64 then Many64 else Many32) m idofs a rs rd sz
    | Pmov_mr_a a r1 =>
      exec_store ge (if Archi.ptr64 then Many64 else Many32) m idofs a rs r1 nil sz
    | Pmovsd_fm_a rd a =>
      exec_load ge Many64 m idofs a rs rd sz
    | Pmovsd_mf_a a r1 =>
      exec_store ge Many64 m idofs a rs r1 nil sz
    (** Pseudo-instructions *)
    | Plabel lbl =>
      Next (nextinstr rs sz) m
    | Pcfi_adjust n => Next rs m
    | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
    |Pnop => Next (nextinstr rs sz) m
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
    end
  end.

(** * Evaluation of builtin arguments *)

Section EVAL_BUILTIN_ARG.

Variable A: Type.

Variable ge: Genv.t.
Variable idofs: option Z.
Variable e: A -> val.
Variable sp: val.
Variable m:mem. 

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs v,
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk id idofs' ofs v,
      idofs = Some idofs' ->
      Mem.loadv chunk m  (Genv.symbol_address ge RELOC_CODE idofs' ofs) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs idofs',
      idofs = Some idofs' ->
      eval_builtin_arg (BA_addrglobal id ofs) (Genv.symbol_address ge RELOC_CODE idofs' ofs)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo).

Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

End EVAL_BUILTIN_ARG.


(** Small step semantics *)

Inductive step (ge: Genv.t) : state -> trace -> state -> Prop :=
| exec_step_internal:
    forall b ofs i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_ext_funct ge (Vptr b ofs) = None ->
      Genv.find_instr ge (Vptr b ofs) = Some i ->
      exec_instr ge i rs m = Next rs' m' ->
      step ge (State rs m) E0 (State rs' m')
| exec_step_builtin:
    forall b ofs ef args res rs m vargs t vres rs' m' idofs,
      rs PC = Vptr b ofs ->
      Genv.find_ext_funct ge (Vptr b ofs) = None ->
      Genv.find_instr ge (Vptr b ofs) = Some (Pbuiltin ef args res)  ->
      id_reloc_offset (Ptrofs.unsigned ofs) (Pbuiltin ef args res) = idofs ->
      eval_builtin_args preg ge idofs rs (rs RSP) m args vargs ->
      external_call ef (RelocProgSemantics.Genv.genv_senv (Genv.genv_genv ge)) vargs m t vres m' ->
        rs' = nextinstr_nf
                (set_res res vres
                         (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) 
                (Ptrofs.repr (instr_size (Pbuiltin ef args res))) ->
        step ge (State rs m) t (State rs' m')
| exec_step_external:
    forall b ofs ef args res rs m t rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_ext_funct ge (Vptr b ofs) = Some ef ->
      forall ra (LOADRA: Mem.loadv Mptr m (rs RSP) = Some ra)
        (RA_NOT_VUNDEF: ra <> Vundef)
        (ARGS: extcall_arguments (rs # RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)))) m (ef_sig ef) args),
        external_call ef (RelocProgSemantics.Genv.genv_senv (Genv.genv_genv ge)) args m t res m' ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res
                          (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil)
                                      (undef_regs (map preg_of destroyed_at_call) rs)))
                  #PC <- ra
                  #RA <- Vundef
                  #RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr))) ->
        step ge (State rs m) t (State rs' m').

(** Initialization of the global environment *)

(* Given relocentry [e] and symtable [stbl], updates the mapping [m] that
associates relocation offsets with their identifiers. *)
Definition acc_reloc_ofs_symb (stbl:symbtable) (e:relocentry) (m:ZTree.t ident) : ZTree.t ident :=
  match SymbTable.get (reloc_symb e) stbl with
  | None => m
  | Some s => ZTree.set (reloc_offset e) (symbentry_id s) m
  end.

Definition gen_reloc_ofs_symb (stbl: symbtable) (rtbl: reloctable) : ZTree.t ident :=
  fold_right (acc_reloc_ofs_symb stbl) (ZTree.empty ident) rtbl.

Definition add_reloc_ofs_symb (stbl: symbtable) (i:reloctable_id)  (rmap: reloctable_map)
           (ofsmap: reloctable_id -> ZTree.t ident) :=
  let rtbl := get_reloctable i rmap in
  let m := gen_reloc_ofs_symb stbl rtbl in
  fun i' => if reloctable_id_eq i i' then m else ofsmap i'.

Definition gen_reloc_ofs_symbs (p:program) :=
  let stbl := p.(prog_symbtable) in
  let rmap := p.(prog_reloctables) in
  let ofsmap := fun i => ZTree.empty ident in
  let ofsmap1 := add_reloc_ofs_symb stbl RELOC_RODATA rmap ofsmap in
  let ofsmap2 := add_reloc_ofs_symb stbl RELOC_DATA rmap ofsmap1 in
  let ofsmap3 := add_reloc_ofs_symb stbl RELOC_CODE rmap ofsmap2 in
  ofsmap3.

Definition globalenv (p: program) : Genv.t :=
  let ofsmap := gen_reloc_ofs_symbs p in
  let genv1 := RelocProgSemantics.globalenv p in
  Genv.mkgenv ofsmap genv1.


(** Initialization of memory *)
Section WITHGE1.

Variable ge:Genv.t.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof gloc ofs => Mem.store Mptr m b p (Genv.symbol_address ge RELOC_DATA p ofs)
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

Definition alloc_external_symbol (m: mem) (e:symbentry): option mem :=
  let id := symbentry_id e in
  match symbentry_type e with
  | symb_notype =>
    let (m1, b) := Mem.alloc m 0 0 in
    Some m1
  | symb_func =>
    match symbentry_secindex e with
    | secindex_undef =>
      let (m1, b) := Mem.alloc m 0 1 in
      Mem.drop_perm m1 b 0 1 Nonempty        
    | secindex_comm => 
      None (**r Impossible *)
    | secindex_normal _ => Some m
    end
  | symb_data =>
    match symbentry_secindex e with
    | secindex_undef
    | secindex_comm => 
      let sz := symbentry_size e in
      let (m1, b) := Mem.alloc m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
        Mem.drop_perm m2 b 0 sz Nonempty
      end        
    | secindex_normal _ => Some m
    end
  end.
      
Fixpoint alloc_external_symbols (m: mem) (t: symbtable)
                       {struct t} : option mem :=
  match t with
  | nil => Some m
  | h :: l =>
      match alloc_external_symbol m h with
      | None => None
      | Some m' => alloc_external_symbols m' l
      end
  end.

(* Definition store_internal_global (b:block) (ofs:Z) (m: mem) (idg: ident * option gdef): option (mem * Z) := *)
(*   let '(id, gdef) := idg in *)
(*   match gdef with *)
(*   | Some (Gvar v) => *)
(*     if is_var_internal v then *)
(*       let init := gvar_init v in *)
(*       let isz := init_data_list_size init in *)
(*       match Globalenvs.store_zeros m b ofs isz with *)
(*       | None => None *)
(*       | Some m1 => *)
(*         match store_init_data_list m1 b ofs init with *)
(*         | None => None *)
(*         | Some m2 =>  *)
(*           match Mem.drop_perm m2 b ofs (ofs+isz) (Globalenvs.Genv.perm_globvar v) with *)
(*           | None => None *)
(*           | Some m3 => Some (m3, ofs + isz) *)
(*           end *)
(*         end *)
(*       end *)
(*     else *)
(*       Some (m, ofs) *)
(*   | _ => Some (m, ofs) *)
(*   end. *)

(* Definition acc_store_internal_global b r (idg: ident * option gdef) := *)
(*   match r with *)
(*   | None => None *)
(*   | Some (m, ofs) => *)
(*     store_internal_global b ofs m idg *)
(*   end. *)

(* Definition store_internal_globals (b:block) (m: mem) (gl: list (ident * option gdef))  *)
(*   : option mem := *)
(*   match fold_left (acc_store_internal_global b) gl (Some (m, 0)) with *)
(*   | None => None *)
(*   | Some (m',_) => Some m' *)
(*   end. *)

Definition alloc_rodata_section (t:sectable) (m:mem) : option mem :=
  match SecTable.get sec_rodata_id t with
  | None => None
  | Some sec =>
    let sz := (sec_size sec) in
    match sec with
    | sec_rodata init =>
      let '(m1, b) := Mem.alloc m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
        match store_init_data_list m2 b 0 init with
        | None => None
        | Some m3 => Mem.drop_perm m3 b 0 sz Readable
        end
      end
    | _ => None
    end
  end.

Definition alloc_data_section (t:sectable) (m:mem) : option mem :=
  match SecTable.get sec_data_id t with
  | None => None
  | Some sec =>
    let sz := (sec_size sec) in
    match sec with
    | sec_data init =>
      let '(m1, b) := Mem.alloc m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
        match store_init_data_list m2 b 0 init with
        | None => None
        | Some m3 => Mem.drop_perm m3 b 0 sz Writable
        end
      end
    | _ => None
    end
  end.

Definition alloc_code_section (t:sectable) (m:mem) : option mem :=
  match SecTable.get sec_code_id t with
  | None => None
  | Some sec =>
    let sz := sec_size sec in
    let (m1, b) := Mem.alloc m 0 sz in
    Mem.drop_perm m1 b 0 sz Nonempty
  end.

End WITHGE1.


Definition init_mem (p: program) :=
  let ge := globalenv p in
  let stbl := prog_sectable p in
  match alloc_rodata_section ge stbl Mem.empty with
  | None => None
  | Some m1 =>
    match alloc_data_section ge stbl m1 with
    | None => None
    | Some m2 =>
      match alloc_code_section stbl m2 with
      | None => None
      | Some m3 =>
        alloc_external_symbols m3 (prog_symbtable p)
      end
    end      
  end.

(** Execution of whole programs. *)
Inductive initial_state_gen (p: program) (rs: regset) m: state -> Prop :=
  | initial_state_gen_intro:
      forall m1 m2 m3 bstack m4
      (MALLOC: Mem.alloc (Mem.push_new_stage m) 0 (Mem.stack_limit + align (size_chunk Mptr) 8) = (m1,bstack))
      (MDROP: Mem.drop_perm m1 bstack 0 (Mem.stack_limit + align (size_chunk Mptr) 8) Writable = Some m2)
      (MRSB: Mem.record_stack_blocks m2 (make_singleton_frame_adt' bstack frame_info_mono 0) = Some m3)
      (MST: Mem.storev Mptr m3 (Vptr bstack (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8 - size_chunk Mptr))) Vnullptr = Some m4),
      let ge := (globalenv p) in
      let rs0 :=
        rs # PC <- (RelocProgSemantics.Genv.symbol_address (Genv.genv_genv ge) 
                                                          p.(prog_main) Ptrofs.zero)
           # RA <- Vnullptr
           # RSP <- (Vptr bstack (Ptrofs.sub (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr)))) in
      initial_state_gen p rs m (State rs0 m4).

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

(* Local Existing Instance mem_accessors_default. *)

Definition genv_senv (ge:Genv.t) :=
  RelocProgSemantics.Genv.genv_senv (Genv.genv_genv ge).

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen step (initial_state p rs) final_state (globalenv p) 
                (genv_senv (globalenv p)).

(** Determinacy of the [Asm] semantics. *)

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
+ unfold exec_instr in H4. destr_in H4; discriminate.
+ unfold exec_instr in H12. destr_in H12; discriminate.
+ assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H6. eexact H12. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
+ assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H7. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. assert (m = m0) by congruence. subst. inv H2; inv H3.
  assert (m1 = m5 /\ bstack = bstack0) by intuition congruence. destruct H0; subst.
  assert (m2 = m6) by congruence. subst.
  f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

Theorem reloc_prog_single_events p rs:
  single_events (semantics p rs).
Proof.
  red. simpl. intros s t s' STEP.
  inv STEP; simpl. omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  split.
  - simpl. intros s t1 s1 t2 STEP MT.
    inv STEP.
    inv MT. eexists. eapply exec_step_internal; eauto.
    edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
    eexists. eapply exec_step_builtin; eauto.
    edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
    eexists. eapply exec_step_external; eauto.
  - eapply reloc_prog_single_events; eauto.
Qed.
