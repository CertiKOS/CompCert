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
    | secret_spec_after_external_intro1 m m' v
        (HM: Ple (Mem.nextblock m) (Mem.nextblock m')):
        secret_spec_after_external (secret2, m) (cr v m') (secret3, m')
    | secret_spec_after_external_intro2 m m' v
        (HM: Ple (Mem.nextblock m) (Mem.nextblock m')):
        secret_spec_after_external (secret4, m) (cr v m') (secret5, m').
    Inductive secret_spec_final_state: secret_state * mem -> reply li_c -> Prop :=
    | secret_spec_final_state_intro m:
        secret_spec_final_state (secret6, m) (cr (Vint Int.zero) m).
    Inductive secret_step : secret_state * mem -> trace -> secret_state * mem -> Prop :=
    | secret_step1 m: secret_step (secret1, m) E0 (secret2, m)
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
          Smallstep.after_external := secret_spec_after_external;
          Smallstep.final_state := secret_spec_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := AST.erase_program secret_asm_program;
      footprint := AST.footprint_of_program secret_asm_program;
    |}.

End SECRET_SPEC.


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

  Inductive secret_match_state se: secret_state * mem -> block * Asm.state -> Prop :=
  | secret_match_state1 m rs nb b
      (HPC: rs PC = Vptr b Ptrofs.zero)
      (HB: Genv.find_symbol se secret_main_id = Some b)
      (HSP: Mach.valid_blockv (Mem.nextblock m) (rs RSP))
      (HNB: nb = Mem.nextblock m):
    secret_match_state se (secret1, m) (nb, State rs m true)
  | secret_match_state2 m rs nb b1 b2 b3 sp ra
      (HPC: rs PC = Vptr b1 Ptrofs.zero)
      (HB1: Genv.find_symbol se secret_rot13_id = Some b1)
      (HRA: rs RA = Vptr b2 (Ptrofs.repr 3))
      (HB2: Genv.find_symbol se secret_main_id = Some b2)
      (HRSI: rs (IR RSI) = Vlong (Int64.repr 5))
      (HB3: Genv.find_symbol se secret_msg_id = Some b3)
      (HRDI: rs (IR RDI) = Vptr b3 Ptrofs.zero)
      (HLSP: Mem.loadv Mptr m (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some sp)
      (HLRA: Mem.loadv Mptr m (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some ra)
      (HSP: Mach.valid_blockv nb sp)
      (HSP': Mach.valid_blockv (Mem.nextblock m) rs#RSP)
      (HLIVE: inner_sp nb rs#RSP = Some true):
    secret_match_state se (secret2, m) (nb, State rs m true)
  | secret_match_state3 m mt rs nb b sp ra
      (HPC: rs PC = Vptr b (Ptrofs.repr 3))
      (HB: Genv.find_symbol se secret_main_id = Some b)
      (HSP: Mach.valid_blockv nb sp)
      (HSP': Mach.valid_blockv (Mem.nextblock m) rs#RSP)
      (HLIVE: inner_sp nb rs#RSP = Some true)
      (HLSP: Mem.loadv Mptr mt (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some sp)
      (HLRA: Mem.loadv Mptr mt (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some ra)
      (HMT: Mem.unchanged_on (fun b ofs => True) m mt):
    secret_match_state se (secret3, m) (nb, State rs mt true)
  | secret_match_state4 m mt rs nb b1 b2 b3 sp ra
      (HPC: rs PC = Vptr b1 Ptrofs.zero)
      (HB1: Genv.find_symbol se secret_write_id = Some b1)
      (HRA: rs RA = Vptr b2 (Ptrofs.repr 7))
      (HB2: Genv.find_symbol se secret_main_id = Some b2)
      (HRDX: rs (IR RDX) = Vlong (Int64.repr 5))
      (HB3: Genv.find_symbol se secret_msg_id = Some b3)
      (HRSI: rs (IR RSI) = Vptr b3 Ptrofs.zero)
      (HRDI: rs (IR RDI) = Vint (Int.repr 1))
      (HSP: Mach.valid_blockv nb sp)
      (HLSP: Mem.loadv Mptr mt (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some sp)
      (HLRA: Mem.loadv Mptr mt (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some ra)
      (HMT: Mem.unchanged_on (fun b ofs => True) m mt):
    secret_match_state se (secret4, m) (nb, State rs mt true).

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
    end.
  Ltac asm_step :=
    instantiate (1 := (_, _)); split; eauto; eapply exec_step_internal;
    [ cbn; rewrite_pc; reflexivity
    | setoid_rewrite find_funct_spec; eauto; reflexivity
    | cbn; rewrite zeq_true by easy; repeat rewrite zeq_false by easy; reflexivity
    | ].

  Lemma secret_correct':
    forward_simulation
      (Invariant.cc_inv Invariant.wt_c @ CallConv.lessdef_c @ cc_c_asm)
      (Invariant.cc_inv Invariant.wt_c @ CallConv.lessdef_c @ cc_c_asm)
      secret_spec
      (semantics secret_asm_program).
  Proof.
    constructor. econstructor. reflexivity. reflexivity.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    assert (se1 = se2) as <-.
    { cbn in *. eprod_crush. subst. inv H. reflexivity. }
    eapply forward_simulation_plus with
      (match_states := fun s1 s2 => secret_match_state se1 s1 s2).
    - intros * Hq Hi. cbn in *. eprod_crush.
      inv H3. inv H4. inv H5. destruct H6. subst.
      inv Hi.
      assert (m0 = m) as ->.
      { inv HRM; eauto.
        red in H7. unfold signature_main in H7. cbn in H7.
        rewrite Hwin64 in H7. easy. }
      eexists (Mem.nextblock m, Asm.State r m true).
      cbn in *.
      split. split; eauto. econstructor.
      + rewrite <- H4. erewrite find_funct_spec; eauto. reflexivity.
      + inv HV. easy.
      + eauto.
      + econstructor; eauto.
    - admit.
    - (* after external *)
      intros * Hs Ha. inv Ha; inv Hs.
      + (* after rot13 *)
        eexists (se1, (se1, rot13_sig), (se1, tt, (caw rot13_sig rs m))).
        eexists (rs, m).
        split. 2: split. 3: split.
        * econstructor. rewrite HPC; eauto.
          erewrite find_funct_spec; eauto. reflexivity.
        * eexists. split. constructor. constructor. reflexivity. easy.
          eexists. split. constructor. repeat constructor.
          econstructor; eauto; cbn; try congruence.
          -- rewrite Hwin64. cbn. congruence.
          -- inv HSP. eapply CallConv.args_removed_tailcall_possible.
             red. cbn. rewrite Hwin64. reflexivity.
          -- inv HSP'. easy.
          -- rewrite HRA. easy.
        * cbn. easy.
        * intros * Hr Ha. destruct s1' as (st1 & mt).
          destruct Hr as (rx1 & Hr1 & Hr2).
          destruct Hr2 as (rx2 & Hr2 & Hr3). inv Hr3.
          inv Ha. cbn in *. rewrite Hwin64 in *. cbn in *.
          inv Hr1. inv Hr2.
          exists (nb, State rs' tm' true).
          split. split; eauto. econstructor.
          -- apply H7.
          -- rewrite H12. eauto.
          -- (* match_state *)
            replace (CallConv.not_init_args 0 sp0)
               with (fun (_: block) (_: Z) => True) in H6.
             2: { repeat (apply Axioms.functional_extensionality; intros).
                  apply PropExtensionality.propositional_extensionality.
                  split; eauto. intros.
                  red. intros A. inv A. lia. }
             econstructor; eauto; try congruence.
             ++ rewrite H12. inv HSP'. econstructor.
                eapply Pos.lt_le_trans; eauto.
             ++ rewrite H12. admit.
             ++ admit.
      + (* after write *)
        admit.
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
        { econstructor.
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
