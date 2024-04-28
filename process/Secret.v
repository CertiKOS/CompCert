From compcert Require Import Integers.
Require Import List Coqlib.
Require Import AST CAsm.
Require Asm.
Import ListNotations.

Notation hello_bytes := [ Byte.repr 104; Byte.repr 101; Byte.repr 108; Byte.repr 108; Byte.repr 111 ].
Notation uryyb_bytes := [ Byte.repr 117; Byte.repr 114; Byte.repr 121; Byte.repr 121; Byte.repr 98].

Definition secret_main_id: positive := 1.
Definition secret_rot13_id: positive := 2.
Definition secret_write_id: positive := 3.
Definition secret_msg_id: positive := 4.

Definition msg_il : list init_data :=
  [ Init_int8 (Int.repr 117); (* u *)
    Init_int8 (Int.repr 114); (* r *)
    Init_int8 (Int.repr 121); (* y *)
    Init_int8 (Int.repr 121); (* y *)
    Init_int8 (Int.repr 98) ]. (* b *)

Definition msg_globvar : globvar unit :=
  {|
    gvar_info := tt;
    gvar_init := msg_il;
    gvar_readonly := false;
    gvar_volatile := false;
  |}.

Definition write_sig : signature :=
  {| sig_args := [Tint; Tptr; Tlong]; sig_res := Tint; sig_cc := cc_default; |}.
Definition rot13_sig : signature :=
  {| sig_args := [Tptr; Tlong]; sig_res := Tvoid; sig_cc := cc_default; |}.
Definition write: Asm.fundef := External (EF_external "write" write_sig).
Definition rot13: Asm.fundef := External (EF_external "rot13" rot13_sig).

Section CODE.
Import Asm.
Definition secret_main_code: code := [
    Pallocframe 16 (Ptrofs.repr 8) (Ptrofs.repr 0);
    Pleaq RDI (Addrmode None None (inr (secret_msg_id, Ptrofs.repr 0)));
    Pmovq_ri RSI (Int64.repr 5);
    Pcall_s secret_rot13_id rot13_sig;
    Pmovl_ri RDI (Int.repr 1);
    Pleaq RSI (Addrmode None None (inr (secret_msg_id, Ptrofs.repr 0)));
    Pmovq_ri RDX (Int64.repr 5);
    Pcall_s secret_write_id write_sig;
    Pmovl_ri RAX (Int.repr 0);
    Pfreeframe 16 (Ptrofs.repr 8) (Ptrofs.repr 0);
    Pret
  ].
End CODE.

Definition secret_main_fundef: Asm.function :=
  Asm.mkfunction signature_main secret_main_code.

Definition secret_asm_program: Asm.program :=
  {|
    prog_defs := [
      (secret_main_id, Gfun (Internal secret_main_fundef));
      (secret_rot13_id, Gfun rot13);
      (secret_write_id, Gfun write);
      (secret_msg_id, Gvar msg_globvar)];
    prog_public := nil;
    prog_main := Some secret_main_id;
  |}.

Require Import LanguageInterface Smallstep Memory Values Globalenvs Events.

Section SECRET_SPEC.

  Variant secret_state :=
    | secret1 | secret2 | secret3 | secret4 | secret5 | secret6.

  Section WITH_SE.
    Context (se: Genv.symtbl).
    Inductive secret_spec_initial_state: query li_c -> secret_state * mem -> Prop :=
    | secret_spec_initial_state_intro sg m b
        (HF: Genv.find_symbol se secret_main_id = Some b)
        (HSG: sg = signature_main):
      secret_spec_initial_state (cq (Vptr b Ptrofs.zero) sg nil m) (secret1, m).
    Inductive secret_spec_at_external: secret_state * mem -> query li_c -> Prop :=
    | secret_spec_at_external_intro1 m sg b1 b2
        (HB1: Genv.find_symbol se secret_rot13_id = Some b1)
        (HB2: Genv.find_symbol se secret_msg_id = Some b2)
        (HSG: sg = rot13_sig):
      secret_spec_at_external (secret2, m)
        (cq (Vptr b1 Ptrofs.zero) sg [ Vptr b2 Ptrofs.zero; Vlong (Int64.repr 5) ] m)
    | secret_spec_at_external_intro2 m sg b1 b2
        (HB1: Genv.find_symbol se secret_write_id = Some b1)
        (HB2: Genv.find_symbol se secret_msg_id = Some b2)
        (HSG: sg = write_sig):
      secret_spec_at_external (secret4, m)
        (cq (Vptr b1 Ptrofs.zero) sg [ Vint (Int.repr 1); Vptr b2 Ptrofs.zero; Vlong (Int64.repr 5) ] m).
    Inductive secret_spec_after_external: secret_state * mem -> reply li_c -> secret_state * mem -> Prop :=
    | secret_spec_after_external_intro1 m m' v b
        (HB: Genv.find_symbol se secret_msg_id = Some b)
        (* rot13 doesn't change the memory state other than the message buffer *)
        (HM: Mem.unchanged_on (fun bx _ => bx <> b) m m'):
        secret_spec_after_external (secret2, m) (cr v m') (secret3, m')
    | secret_spec_after_external_intro2 m v:
        (* write is not supposed to change the memory *)
        secret_spec_after_external (secret4, m) (cr v m) (secret5, m).
    Inductive secret_spec_final_state: secret_state * mem -> reply li_c -> Prop :=
    | secret_spec_final_state_intro m:
        secret_spec_final_state (secret6, m) (cr (Vint Int.zero) m).
    Inductive secret_step : secret_state * mem -> trace -> secret_state * mem -> Prop :=
    | secret_step1 m m' (HALLOC: Mem.alloc m 0 16 = Some m'):
      secret_step (secret1, m) E0 (secret2, m)
    | secret_step2 m: secret_step (secret3, m) E0 (secret4, m)
    | secret_step3 m: secret_step (secret5, m) E0 (secret6, m).

  End WITH_SE.

  Definition secret_spec: semantics li_c li_c :=
    {|
      activate se :=
        {|
          Smallstep.step _ := secret_step;
          Smallstep.initial_state := secret_spec_initial_state se;
          Smallstep.at_external := secret_spec_at_external se;
          Smallstep.after_external := secret_spec_after_external se;
          Smallstep.final_state := secret_spec_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := AST.erase_program secret_asm_program;
      footprint := AST.footprint_of_program secret_asm_program;
    |}.

End SECRET_SPEC.

Require Import InjectFootprint.

Section CODE_PROOF.

  Import Maps.

  Lemma find_funct_spec {F V} b id se (p: AST.program F V):
    Genv.find_symbol se id = Some b ->
    Genv.find_funct (Genv.globalenv se p) (Vptr b Ptrofs.zero) =
      match (prog_defmap p) ! id with
      | Some (Gfun f) => Some f
      | _ => None
      end.
  Proof.
    intros Hf. cbn.
    destruct Ptrofs.eq_dec; try easy.
    unfold Genv.find_funct_ptr. rewrite Genv.find_def_spec.
    erewrite Genv.find_invert_symbol; eauto.
  Qed.

  Import Asm.
  Require Import Lifting.       (* eprod_crush *)

  Search Mem.inject Mem.unchanged_on.

  Inductive secret_match_state: ccworld (cc_c injp @ cc_c_asm) -> secret_state * mem -> block * Asm.state -> Prop :=
  | secret_match_state1 rs nb b sg j m1 m2 Hm se
      (HPC: rs PC = Vptr b Ptrofs.zero)
      (HB: Genv.find_symbol se secret_main_id = Some b)
      (HSP: Mach.valid_blockv (Mem.nextblock m2) (rs RSP))
      (HNB: nb = Mem.nextblock m2):
    secret_match_state (se, injpw j m1 m2 Hm, caw sg rs m2)
      (secret1, m1) (nb, State rs m2 true)
  | secret_match_state2 rs nb se b1 b2 b3 sp ra sg wi m1 m2 j Hm mx1 mx2 Hmx sp_b rs0
      (HWI: wi = injpw j m1 m2 Hm)
      (HACC: injp_acc wi (injpw j mx1 mx2 Hmx))
      (HB1: Genv.find_symbol se secret_rot13_id = Some b1)
      (HB2: Genv.find_symbol se secret_main_id = Some b2)
      (HB3: Genv.find_symbol se secret_msg_id = Some b3)
      (HPC: rs PC = Vptr b1 Ptrofs.zero)
      (HRA: rs RA = Vptr b2 (Ptrofs.repr 3))
      (HRSI: rs (IR RSI) = Vlong (Int64.repr 5))
      (HRDI: rs (IR RDI) = Vptr b3 Ptrofs.zero)
      (HLSP: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some sp)
      (HLRA: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some ra)
      (HCALLEE: forall r, Conventions1.is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r))
      (HSP: Mach.valid_blockv nb sp)
      (HSPB1: Plt sp_b (Mem.nextblock mx2))
      (HSPB2: ~ Plt sp_b nb)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB3: forall b d, j b = Some (sp_b, d) -> False)
      (* (HOUT: forall ofs, loc_out_of_reach j m1 sp_b ofs) *)
      (HFREE: Mem.range_perm mx2 sp_b 0 16 Cur Freeable) :
    secret_match_state (se, wi, caw sg rs0 m2)
      (secret2, mx1) (nb, State rs mx2 true)
  | secret_match_state3  rs nb se sp ra sg wi m1 m2 j Hm mx1 mx2 mx3 jx Hmx sp_b rs0 b
      (HWI: wi = injpw j m1 m2 Hm)
      (HACC: injp_acc wi (injpw jx mx1 mx2 Hmx))
      (HPC: rs PC = Vptr b (Ptrofs.repr 3))
      (HB: Genv.find_symbol se secret_main_id = Some b)
      (HSP: Mach.valid_blockv nb sp)
      (HLSP: Mem.loadv Mptr mx3 (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some sp)
      (HLRA: Mem.loadv Mptr mx3 (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some ra)
      (HCALLEE: forall r, Conventions1.is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r))
      (HM0: Mem.unchanged_on (fun b ofs => True) mx2 mx3)
      (HNEXTBLOCK: Mem.nextblock mx2 = Mem.nextblock mx3)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB1: Plt sp_b (Mem.nextblock mx2))
      (HSPB2: ~ Plt sp_b nb)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB3: forall b d, jx b = Some (sp_b, d) -> False)
      (* (HOUT: forall ofs, loc_out_of_reach j m1 sp_b ofs) *)
      (HFREE: Mem.range_perm mx2 sp_b 0 16 Cur Freeable)  :
    secret_match_state  (se, wi, caw sg rs0 m2)
      (secret3, mx1) (nb, State rs mx3 true)
  | secret_match_state4 rs nb se b1 b2 b3 sp ra sg wi m1 m2 j jx Hm mx1 mx2 mx3 Hmx sp_b rs0
      (HWI: wi = injpw j m1 m2 Hm)
      (HACC: injp_acc wi (injpw jx mx1 mx2 Hmx))
      (HB1: Genv.find_symbol se secret_write_id = Some b1)
      (HB2: Genv.find_symbol se secret_main_id = Some b2)
      (HB3: Genv.find_symbol se secret_msg_id = Some b3)
      (HPC: rs PC = Vptr b1 Ptrofs.zero)
      (HRA: rs RA = Vptr b2 (Ptrofs.repr 7))
      (HRDX: rs (IR RDX) = Vlong (Int64.repr 5))
      (HRSI: rs (IR RSI) = Vptr b3 Ptrofs.zero)
      (HRDI: rs (IR RDI) = Vint (Int.repr 1))
      (HLSP: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some sp)
      (HLRA: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some ra)
      (HM0: Mem.unchanged_on (fun b ofs => True) mx2 mx3)
      (HNEXTBLOCK: Mem.nextblock mx2 = Mem.nextblock mx3)
      (HCALLEE: forall r, Conventions1.is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r))
      (HSP: Mach.valid_blockv nb sp)
      (HSPB1: Plt sp_b (Mem.nextblock mx2))
      (HSPB2: ~ Plt sp_b nb)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB3: forall b d, jx b = Some (sp_b, d) -> False)
      (* (HOUT: forall ofs, loc_out_of_reach j m1 sp_b ofs) *)
      (HFREE: Mem.range_perm mx2 sp_b 0 16 Cur Freeable) :
    secret_match_state (se, wi, caw sg rs0 m2)
      (secret4, mx1) (nb, State rs mx3 true)

  (* | secret_match_state4 m mt rs nb b1 b2 b3 sp ra rs0 m0 sg sp_b *)
  (*     (HPC: rs PC = Vptr b1 Ptrofs.zero) *)
  (*     (HB1: Genv.find_symbol se secret_write_id = Some b1) *)
  (*     (HRA: rs RA = Vptr b2 (Ptrofs.repr 7)) *)
  (*     (HB2: Genv.find_symbol se secret_main_id = Some b2) *)
  (*     (HRDX: rs (IR RDX) = Vlong (Int64.repr 5)) *)
  (*     (HB3: Genv.find_symbol se secret_msg_id = Some b3) *)
  (*     (HRSI: rs (IR RSI) = Vptr b3 Ptrofs.zero) *)
  (*     (HRDI: rs (IR RDI) = Vint (Int.repr 1)) *)
  (*     (HSP: Mach.valid_blockv nb sp) *)
  (*     (HLSP: Mem.loadv Mptr mt (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some sp) *)
  (*     (HLRA: Mem.loadv Mptr mt (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some ra) *)
  (*     (HMT: Mem.unchanged_on (fun b ofs => True) m mt) *)
  (*     (HM0: Mem.unchanged_on (fun b ofs => False) m0 mt) *)
  (*     (HNEXTBLOCK: Mem.nextblock m = Mem.nextblock mt) *)
  (*     (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero) *)
  (*     (HFREE: Mem.range_perm mt sp_b 0 16 Cur Freeable) : *)
  (*   secret_match_state se (caw sg rs0 m0) (secret4, m) (nb, State rs mt true) *)
  (* | secret_match_state5 m mt rs nb b sp ra rs0 m0 sg sp_b *)
  (*     (HPC: rs PC = Vptr b (Ptrofs.repr 7)) *)
  (*     (HB: Genv.find_symbol se secret_main_id = Some b) *)
  (*     (HSP: Mach.valid_blockv nb sp) *)
  (*     (HSP': Mach.valid_blockv (Mem.nextblock m) rs#RSP) *)
  (*     (HLIVE: inner_sp nb rs#RSP = Some true) *)
  (*     (HLSP: Mem.loadv Mptr mt (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some sp) *)
  (*     (HLRA: Mem.loadv Mptr mt (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some ra) *)
  (*     (HMT: Mem.unchanged_on (fun b ofs => True) m mt) *)
  (*     (HM0: Mem.unchanged_on (fun b ofs => False) m0 mt) *)
  (*     (HNEXTBLOCK: Mem.nextblock m = Mem.nextblock mt) *)
  (*     (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero) *)
  (*     (HFREE: Mem.range_perm mt sp_b 0 16 Cur Freeable) : *)
  (*   secret_match_state se (caw sg rs0 m0) (secret5, m) (nb, State rs mt true) *)
  | secret_match_state6 rs mx1 mx2 mx3 m1 m2 j Hm jx Hmx wi nb rs0 sg se
      (HACC:injp_acc wi (injpw jx mx1 mx2 Hmx))
      (HWI: wi = injpw j m1 m2 Hm)
      (HRAX: rs (IR RAX) = Vint Int.zero)
      (HCALLEE: forall r, Conventions1.is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r))
      (HSG: sg = signature_main)
      (HMT: Mem.unchanged_on (fun b ofs => True) mx2 mx3)
      (HNEXTBLOCK: Mem.nextblock mx2 = Mem.nextblock mx3)
      (HPC: rs PC = rs0 RA)
      (HSP: rs RSP = rs0 RSP):
      secret_match_state  (se, wi, caw sg rs0 m2)
        (secret6, mx1) (nb, State rs mx3 false).

  Transparent Archi.ptr64.
  Hypothesis (Hwin64: Archi.win64 = false).

  Lemma secret_prog_defmap_msg:
    (prog_defmap secret_asm_program) ! secret_msg_id = Some (Gvar msg_globvar).
  Proof. reflexivity. Qed.
  Lemma secret_prog_defmap_rot13:
    (prog_defmap secret_asm_program) ! secret_rot13_id = Some (Gfun rot13).
  Proof. reflexivity. Qed.
  Lemma secret_prog_defmap_write:
    (prog_defmap secret_asm_program) ! secret_write_id = Some (Gfun write).
  Proof. reflexivity. Qed.
  Lemma msg_block se:
    Genv.valid_for (AST.erase_program secret_asm_program) se ->
    exists b, Genv.find_symbol se secret_msg_id = Some b.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_msg).
    destruct H as (b & Hb1 & Hb2); eauto.
  Qed.
  Lemma rot13_block se:
    Genv.valid_for (AST.erase_program secret_asm_program) se ->
    exists b, Genv.find_symbol se secret_rot13_id = Some b.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_rot13).
    destruct H as (b & Hb1 & Hb2); eauto.
  Qed.
  Lemma write_block se:
    Genv.valid_for (AST.erase_program secret_asm_program) se ->
    exists b, Genv.find_symbol se secret_write_id = Some b.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_write).
    destruct H as (b & Hb1 & Hb2); eauto.
  Qed.

  Ltac one_step := eapply star_left with (t1 := E0) (t2 := E0); [ | | reflexivity ].
  Ltac rewrite_pc :=
    match goal with
    | [ H: (_ PC) = _ |- _ ] => rewrite H
    | [ H: _ = (_ PC) |- _ ] => rewrite <- H
    end.
  Ltac asm_step :=
    instantiate (1 := (_, _)); split; eauto; eapply exec_step_internal;
    [ cbn; rewrite_pc; reflexivity
    | setoid_rewrite find_funct_spec; eauto; reflexivity
    | cbn; rewrite zeq_true by easy; repeat rewrite zeq_false by easy; reflexivity
    | ].

  Lemma main_size_arguments:
    Conventions.size_arguments signature_main = 0.
  Proof. cbn. rewrite Hwin64. reflexivity. Qed.
  Lemma rot13_size_arguments:
    Conventions.size_arguments rot13_sig = 0.
  Proof. cbn. rewrite Hwin64. reflexivity. Qed.
  Lemma write_size_arguments:
    Conventions.size_arguments write_sig = 0.
  Proof. cbn. rewrite Hwin64. reflexivity. Qed.

  Lemma no_init_args sp:
    CallConv.not_init_args 0 sp = fun (_: block) (_: Z) => True.
  Proof.
    repeat (apply Axioms.functional_extensionality; intros).
    apply PropExtensionality.propositional_extensionality.
    split; eauto. intros.
    red. intros A. inv A. lia.
  Qed.

  Lemma no_init_args_loc sp:
    Mach.loc_init_args 0 sp = fun (_: block) (_: Z) => False.
  Proof.
    repeat (apply Axioms.functional_extensionality; intros).
    apply PropExtensionality.propositional_extensionality.
    split.
    - intros. inv H. lia.
    - inversion 1.
  Qed.

  Lemma match_program_id:
    Linking.match_program (fun _ f0 tf => tf = id f0) eq secret_asm_program secret_asm_program.
  Proof.
    red. red. constructor; eauto.
    constructor. constructor. eauto. simpl. econstructor; eauto.
    apply Linking.linkorder_refl.
    constructor. constructor; eauto. cbn. econstructor; eauto.
    apply Linking.linkorder_refl.
    constructor; eauto.
    constructor; eauto. econstructor; eauto.
    apply Linking.linkorder_refl.
    repeat econstructor; eauto.
  Qed.

  Lemma loadv_unchanged_on : forall P m m' chunk b ptrofs v,
      Mem.unchanged_on P m m' ->
      (forall i, let ofs := Ptrofs.unsigned ptrofs in
            ofs <= i < ofs + size_chunk chunk -> P b i) ->
      Mem.loadv chunk m (Vptr b ptrofs) = Some v ->
      Mem.loadv chunk m' (Vptr b ptrofs) = Some v.
  Proof.
    intros. unfold Mem.loadv in *. cbn in *.
    eapply Mem.load_unchanged_on; eauto.
  Qed.

  Lemma secret_correct':
    forward_simulation (cc_c injp @ cc_c_asm) (cc_c injp @ cc_c_asm)
      secret_spec (semantics secret_asm_program).
  Proof.
    constructor. econstructor. reflexivity. reflexivity.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_plus with
      (match_states := fun s1 s2 => secret_match_state wB s1 s2).
    - intros * Hq Hi. cbn in *. destruct wB as [[se winjp] wca].
      destruct H as [Hse ->]. inv Hse. destruct Hq as (qx & Hq1 & Hq2).
      inv Hq1. inv Hq2. inv Hi. inv H5.
      inv HRM. 2: { pose proof main_size_arguments. extlia. }
      eexists (Mem.nextblock m3, Asm.State rs m3 true).
      pose proof match_program_id as Hmatch.
      eapply Genv.find_funct_transf in Hmatch; eauto.
      2: { inv H3. erewrite find_funct_spec; eauto. reflexivity. }
      cbn in *.
      split. split; eauto. econstructor; eauto. inv HV. congruence.
      eapply Genv.find_symbol_match in HF as (bf & Hbf1 & Hbf2); eauto.
      inv H3. rewrite Hbf1 in H10. inv H10. rewrite Ptrofs.add_zero_l in H9.
      econstructor; eauto.
    - (* final state *)
      intros * Hs Hf. inv Hf. inv Hs.
      exists (rs, mx3). split. constructor.
      exists (cr (Vint Int.zero) mx2). split.
      exists (injpw jx m mx2 Hmx). split; eauto.
      constructor; eauto. constructor; eauto.
      constructor; eauto with mem.
      + rewrite main_size_arguments. rewrite no_init_args. eauto.
      + rewrite main_size_arguments. rewrite no_init_args_loc.
        inv HACC. split. etransitivity. apply H10. apply HMT.
        inversion 1. inversion 1. etransitivity. apply H10. apply HMT.
      + rewrite main_size_arguments. rewrite no_init_args_loc. inversion 1.
    - (* at external *)
      intros * Hs Ha. inv Ha; inv Hs.
      + (* external call rot13 *)
        eexists (se, injpw j m mx2 Hmx, caw rot13_sig rs mx2), (rs, mx2).
        destruct H as (Hse1 & Hse2). inv Hse2. inv Hse1.
        repeat apply conj.
        * econstructor. rewrite_pc; eauto.
          erewrite find_funct_spec; eauto. reflexivity.
        (* match_query *)
        * eexists (cq _ _ _ _). split; econstructor; eauto; cbn; try congruence.
          (* pc injection *)
          -- rewrite_pc.
             eapply Genv.find_symbol_match in HB1 as (bf & Hbf1 & Hbf2); eauto.
             inv HACC. eapply val_inject_incr; eauto.
             econstructor. 2: rewrite Ptrofs.add_zero_l; reflexivity. congruence.
          (* args injection *)
          -- rewrite Hwin64. cbn. rewrite HRDI. rewrite HRSI. admit.
          (* match_mem *)
          -- constructor.
          (* args_removed *)
          -- constructor. unfold rot13_sig. red. cbn.
             rewrite Hwin64. reflexivity.
          (* rsp has type *)
          -- rewrite HSPB. constructor.
          (* rs has type *)
          -- rewrite HRA. constructor.
          (* valid_blockv *)
          -- rewrite HSPB. constructor. apply HSPB1.
        (* match_senv *)
        * split. 2: reflexivity. inv HACC. constructor.
          -- eapply Genv.match_stbls_incr; eauto.
             intros. specialize (H14 _ _ _ H H1) as (HA & HB).
             unfold Mem.valid_block in HA, HB. split; extlia.
          -- etransitivity; eauto. apply H11.
          -- etransitivity; eauto. apply H12.
        (* after external *)
        * intros * Hr Ha. destruct s1' as (st1 & mx).
          destruct Hr as (rx1 & (wx & Hwx & Hr1) & Hr2).
          inv Hr1. inv Hr2. inv Ha.
          exists (nb, State rs' tm' true).
          split. split; eauto. econstructor.
          -- apply H13.
          -- rewrite H17. rewrite HSPB. cbn.
             destruct plt; eauto. exfalso. apply HSPB2. eauto.
          -- (* match_state *)
             inv Hwx. inv H1.
             assert (HFREE1: Mem.range_perm m2' sp_b 0 16 Cur Freeable).
             {
               red. intros. red in HFREE. inv H15.
               eapply unchanged_on_perm; eauto.
               red. intros. exploit HSPB3; eauto.
             }
             eapply secret_match_state3 with (jx := f'); eauto; try congruence.
             (* acc *)
             ++ etransitivity; eauto. constructor; eauto.
             (* load sp *)
             ++ rewrite H17. rewrite HSPB in HLSP |- *. cbn in HLSP |- *.
                rewrite Ptrofs.add_zero_l in HLSP |- *.
                rewrite Ptrofs.unsigned_repr in HLSP |- * by (cbn; lia).
                eapply Mem.load_unchanged_on. apply H12.
                intros. rewrite rot13_size_arguments. rewrite no_init_args. easy.
                eapply Mem.load_unchanged_on; eauto.
                intros. red. intros. exploit HSPB3; eauto.
             (* load ra *)
             ++ admit.
             (* HCALLEE *)
             ++ intros. rewrite <- HCALLEE; eauto.
             ++ rewrite rot13_size_arguments in H12.
                rewrite no_init_args in H12. easy.
             (* Plt sp_b nextblock *)
             ++ eapply Plt_Ple_trans. apply HSPB1. apply H15.
             ++ intros. destruct (j b5) as [[sb dsb]|] eqn: Hf.
                ** apply H20 in Hf as Hf'. rewrite H1 in Hf'. inv Hf'. eauto.
                ** specialize (H21 _ _ _ Hf H1) as [A B]. eauto.
      + (* external call write *)
        assert (Hmx3: Mem.inject jx m mx3).
        { admit.
        }
        eexists (se, injpw jx m mx3 Hmx3, caw write_sig rs mx3), (rs, mx3).
        destruct H as (Hse1 & Hse2). inv Hse2. inv Hse1.
        repeat apply conj.
        * econstructor. rewrite_pc; eauto.
          erewrite find_funct_spec; eauto. reflexivity.
        (* match_query *)
        * eexists (cq _ _ _ mx3). split; econstructor; eauto; cbn; try congruence.
          (* pc injection *)
          -- rewrite_pc.
             eapply Genv.find_symbol_match in HB1 as (bf & Hbf1 & Hbf2); eauto.
             inv HACC. eapply val_inject_incr; eauto.
             econstructor. 2: rewrite Ptrofs.add_zero_l; reflexivity. congruence.
          (* args injection *)
          -- rewrite Hwin64. cbn. rewrite HRDI. rewrite HRSI. admit.
          (* match_mem *)
          -- constructor.
          (* args_removed *)
          -- constructor. unfold write_sig. red. cbn.
             rewrite Hwin64. reflexivity.
          (* rsp has type *)
          -- rewrite HSPB. constructor.
          (* rs has type *)
          -- rewrite HRA. constructor.
          (* valid_blockv *)
          -- rewrite HSPB. constructor. rewrite <- HNEXTBLOCK. apply HSPB1.
        (* match_senv *)
        * admit.
        (* after external *)
        * admit.
    - (* internal step *)
      intros * HS * Hs. inv HS; inv Hs.
      + (* initial state to call rot13 *)
        edestruct msg_block as [b1 Hb1]; eauto.
        edestruct rot13_block as [b2 Hb2]; eauto.
        assert (exists m1 stk, Mem.alloc m 0 16 = Some (m1, stk))
          as (m1 & stk & HM1).
        { edestruct Mem.alloc_succeed as ((? & ?) & ?). admit.
          eexists _, _; eauto. }
        assert (exists m2, Mem.store Mint64 m1 stk 0 (rs RSP) = Some m2)
          as (m2 & HM2).
        { edestruct Mem.valid_access_store as (? & ?); eauto.
          admit. }
        assert (exists m3, Mem.store Mint64 m2 stk 8 (rs RA) = Some m3)
          as (m3 & HM3) by admit.
        eexists (_, _). split.
        eapply plus_left. asm_step.
        { cbn. rewrite HM1.
          rewrite Ptrofs.add_zero_l. rewrite Ptrofs.unsigned_repr by (cbn; lia).
          rewrite HM2.
          rewrite Ptrofs.add_zero_l. rewrite Ptrofs.unsigned_repr by (cbn; lia).
          rewrite HM3. reflexivity. }
        2: { instantiate (1 := E0). reflexivity. }
        one_step. asm_step.
        { cbn. unfold Genv.symbol_address. rewrite Hb1.
          rewrite Ptrofs.add_zero_l.
          replace (Ptrofs.of_int64 Int64.zero) with Ptrofs.zero by reflexivity.
          reflexivity. }
        one_step. asm_step. reflexivity.
        one_step. asm_step.
        { cbn. rewrite_pc.
          replace (Val.offset_ptr (Val.offset_ptr (Val.offset_ptr (Vptr b Ptrofs.zero) Ptrofs.one) Ptrofs.one) Ptrofs.one)
            with (Vptr b (Ptrofs.repr 3)) by easy. reflexivity. }
        apply star_refl.
        { econstructor
          - unfold Genv.symbol_address. rewrite Hb2. reflexivity.
          -
        }
      + (* after rot13 to call write *)
        edestruct msg_block as [b1 Hb1]; eauto.
        edestruct write_block as [b2 Hb2]; eauto.
        eexists (_, _). split.
        eapply plus_left. asm_step.

    - easy.
  Admitted.


End CODE_PROOF.

Require Import CallconvAlgebra CKLR.

Lemma secret_spec_self_sim (R: cklr):
  forward_simulation (cc_c R) (cc_c R) secret_spec secret_spec.
Proof.
Admitted.

Lemma cc_join_fsim {liA1 liA2 liB1 liB2}
  (ccA1 ccA2: callconv liA1 liA2)
  (ccB1 ccB2: callconv liB1 liB2) L1 L2:
  forward_simulation ccA1 ccB1 L1 L2 ->
  forward_simulation ccA2 ccB2 L1 L2 ->
  forward_simulation (cc_join ccA1 ccA2) (cc_join ccB1 ccB2) L1 L2.
Proof.
  intros A B.
  rewrite cc_join_l in A, B by reflexivity.
  rewrite cc_join_comm in B.
  eapply cc_join_fsim; eauto.
Qed.

Lemma secret_correct:
  forward_simulation cc_compcert cc_compcert secret_spec
    (Asm.semantics secret_asm).
Proof.
  unfold cc_compcert.
  eapply compose_forward_simulations.
  apply cc_star_fsim.
  repeat apply cc_join_fsim; try apply secret_spec_self_sim.
  rewrite <- cc_compose_assoc at 2. rewrite <- cc_compose_assoc.
  rewrite <- cc_compose_assoc at 2. rewrite <- cc_compose_assoc.
  eapply compose_forward_simulations.
  rewrite cc_compose_assoc at 2. rewrite cc_compose_assoc.
  apply secret_correct'.
  apply Asmrel.semantics_asm_rel.
Qed.
