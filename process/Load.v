Require Import Coqlib Integers.

Require Import Events LanguageInterface Smallstep Globalenvs Values Memory.
Require Import AST Ctypes Clight.
Require Import Lifting Encapsulation.

Require Import List Maps.
Import ListNotations.
Require Import Conventions Mach Asm.

Require Import InitMem With.

(* Conventions.cc_c_locset @ cc_locset_mach @ cc_mach_asm *)

Section CA.
  Require Import Locations CallConv.

  Record cc_ca_world :=
    caw {
        caw_sg : signature;
        caw_rs : regset;
        caw_m : mem
      }.

  Definition make_locset_rs (rs: regset) (m:mem) (sp: val) (l:loc):=
    match l with
    |R r => rs (preg_of r)
    |S Outgoing ofs ty =>
       let v := load_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) in Val.maketotal v
    |_ => Vundef
    end.

  Inductive cc_c_asm_mq : cc_ca_world -> c_query -> query li_asm -> Prop:=
    cc_c_asm_mq_intro sg args m (rs: regset) tm (ls : Locmap.t):
      let sp := rs#SP in
      let ra := rs#RA in
      let vf := rs#PC in
      args = (map (fun p => Locmap.getpair p ls) (loc_arguments sg)) ->
      ls = make_locset_rs rs tm sp ->
      args_removed sg sp tm m ->
      Val.has_type sp Tptr ->
      Val.has_type ra Tptr ->
      valid_blockv (Mem.nextblock tm) sp ->
      vf <> Vundef -> ra <> Vundef ->
      cc_c_asm_mq
        (caw sg rs tm)
        (cq vf sg args m)
        (rs,tm).

  Definition rs_getpair (p: rpair preg) (rs : regset) :=
    match p with
    |One r => rs r
    |Twolong r1 r2 => Val.longofwords (rs r1) (rs r2)
    end.

  Inductive cc_c_asm_mr : cc_ca_world -> c_reply -> reply li_asm -> Prop :=
    cc_c_asm_mr_intro sg res tm m' tm' (rs rs' :regset) :
      let sp := rs#SP in
      res = rs_getpair (map_rpair preg_of (loc_result sg)) rs' ->
      (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
      Mem.unchanged_on (not_init_args (size_arguments sg) sp) m' tm' ->
      Mem.unchanged_on (loc_init_args (size_arguments sg) sp) tm tm' ->
      Mem.nextblock m' = Mem.nextblock tm' ->
      (forall b ofs k p, loc_init_args (size_arguments sg) sp b ofs ->
                    ~ Mem.perm m' b ofs k p) ->
      rs'#SP = rs#SP -> rs'#PC = rs#RA ->
      cc_c_asm_mr
        (caw sg rs tm)
        (cr res m')
        (rs', tm').

  Program Definition cc_c_asm : callconv li_c li_asm :=
    {|
      match_senv _ := eq;
      match_query := cc_c_asm_mq;
      match_reply := cc_c_asm_mr
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. inv H0. cbn. subst vf0. reflexivity. Qed.
  Next Obligation. inv H. cbn. subst vf0. reflexivity. Qed.

  Definition rs_to_mrs (rs : regset) := fun r: mreg => rs (preg_of r).

  Require Import CallconvAlgebra.

  Lemma cc_ca_cllmma :
    ccref (cc_c_asm) (cc_c_locset @ cc_locset_mach @ cc_mach_asm).
  Proof.
    intros [sg rs tm] se1 se2 q1 q2 Hse. destruct Hse.
    intros Hq. inversion Hq. subst sg0 rs0 tm0 q1 q2.
    exists (se1,sg,(se1,(lmw sg (rs_to_mrs rs) tm sp),
                (rs,Mem.nextblock tm))).
    repeat apply conj; cbn in *; eauto.
    - exists (lq vf sg ls m). split.
      econstructor; eauto.
      exists (mq vf sp ra (rs_to_mrs rs) tm). split. rewrite H3.
      econstructor; eauto.
      econstructor; eauto.
    - intros cr ar [lr [Hr1 [mr [Hr2 Hr3]]]].
      inv Hr1. inv Hr2. inv Hr3.
      econstructor; eauto.
      + destruct (loc_result sg).
        -- simpl. rewrite <- H13. rewrite H9. reflexivity. simpl. auto.
        -- simpl. f_equal.
           rewrite <- H13. rewrite H9. reflexivity. simpl. eauto.
           rewrite <- H13. rewrite H9. reflexivity. simpl. eauto.
      + intros. rewrite <- H13. rewrite H12. reflexivity. eauto.
  Qed.

  Lemma cc_cllmma_ca :
    ccref (cc_c_locset @ cc_locset_mach @ cc_mach_asm) (cc_c_asm).
  Proof.
    intros [[se' sg] [[se'' w2] [rs tm]]] se''' se q1 q2 Hse Hq.
    destruct Hse. inv H. destruct H0. inv H. inv H0.
    destruct Hq as [lq [Hq1 [mq [Hq2 Hq3]]]]. cbn in *.
    inv Hq1. inv Hq2. inv Hq3.
    rename rs1 into mrs. rename m0 into tm.
    exists (caw sg rs tm).
    repeat apply conj; eauto.
    - econstructor; eauto.
      apply Axioms.extensionality.
      intro r. destruct r; simpl; eauto.
    - intros r1 r2 Hr. inv Hr.
      set (ls' loc :=
             match loc with
             |R r => rs' (preg_of r)
             |_ => Vundef
             end
          ).
      exists (lr ls'  m'). split.
      constructor; eauto.
      destruct (loc_result); simpl; eauto.
      exists (mr (rs_to_mrs rs') tm'). split.
      constructor; eauto.
      intros. unfold rs_to_mrs. rewrite H3. eauto. eauto.
      constructor; eauto.
      inversion H8. eauto.
  Qed.

  Lemma ca_cllmma_equiv :
    cceqv cc_c_asm (cc_c_locset @ cc_locset_mach @ cc_mach_asm).
  Proof. split. apply cc_ca_cllmma. apply cc_cllmma_ca. Qed.

End CA.

Notation tint := (Tint I32 Unsigned noattr).

Definition main_sig := signature_of_type Tnil tint cc_default.

Section INIT_C.
  Context (prog: Clight.program).
  Let sk := erase_program prog.
  Section WITH_SE.

    Context (se: Genv.symtbl).
    Let ge := Genv.globalenv se prog.
    Inductive init_c_initial_state (q: query li_wp) : option int -> Prop :=
    | init_c_initial_state_intro: init_c_initial_state q None.
    Inductive init_c_at_external: option int -> query li_c -> Prop :=
    | init_c_at_external_intro vf m f main b:
      init_mem se sk = Some m ->
      Genv.invert_symbol se b = Some main ->
      vf = Vptr b Ptrofs.zero ->
      prog_main prog = Some main ->
      (prog_defmap prog) ! main = Some (Gfun f) ->
      init_c_at_external None (cq vf main_sig [] m).
    Inductive init_c_after_external: option int -> reply li_c -> option int -> Prop :=
    | init_c_after_external_intro i m:
      init_c_after_external None (cr (Vint i) m) (Some i).
    Inductive init_c_final_state: option int -> reply li_wp -> Prop :=
    | inic_c_final_state_intro i: init_c_final_state (Some i) i.

  End WITH_SE.
  Program Definition init_c: Smallstep.semantics li_c li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := init_c_initial_state;
          Smallstep.at_external := init_c_at_external se;
          Smallstep.after_external := init_c_after_external;
          Smallstep.final_state := init_c_final_state;
          Smallstep.globalenv := Genv.globalenv se prog;
        |};
      skel := sk;
      footprint i := False
    |}.
End INIT_C.

Section INIT_ASM.
  Context (prog: program).
  Let sk := erase_program prog.
  Section WITH_SE.

    Context (se: Genv.symtbl).
    Let ge := Genv.globalenv se prog.
    Inductive init_asm_initial_state (q: query li_wp) : option int -> Prop :=
    | init_asm_initial_state_intro: init_asm_initial_state q None.
    Inductive init_asm_at_external: option int -> query li_asm -> Prop :=
    | init_asm_at_external_intro m rs f main vf b:
      init_mem se sk = Some m ->
      AST.prog_main prog = Some main ->
      (prog_defmap prog) ! main = Some (Gfun f) ->
      Genv.invert_symbol se b = Some main ->
      vf = Vptr b Ptrofs.zero ->
      (* (* TODO: use invert_symbol to associate main with a block *) *)
      (* Genv.find_funct ge vf = Some f -> *)
      (* [RSP] need to be qualified as Mach.valid_blockv, so it's using vf instead
      of Vnullptr. See Mach.v for more details *)
      rs = (((Pregmap.init Vundef) # PC <- vf) # RSP <- vf) # RA <- Vnullptr ->
      init_asm_at_external None (rs, m).
    Inductive init_asm_after_external: option int -> reply li_asm -> option int -> Prop :=
    | init_asm_after_external_intro i rs m:
      rs#(IR RAX) = Vint i ->
      init_asm_after_external None (rs, m) (Some i).
    Inductive init_asm_final_state: option int -> reply li_wp -> Prop :=
    | inic_asm_final_state_intro i: init_asm_final_state (Some i) i.

  End WITH_SE.
  Program Definition init_asm: Smallstep.semantics li_asm li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := init_asm_initial_state;
          Smallstep.at_external := init_asm_at_external se;
          Smallstep.after_external := init_asm_after_external;
          Smallstep.final_state := init_asm_final_state;
          Smallstep.globalenv := Genv.globalenv se prog;
        |};
      skel := sk;
      footprint i := False
    |}.
End INIT_ASM.

Section VA.

  Require Import ValueDomain ValueAnalysis VAInject.

  Context (se: Genv.symtbl) sk m (Hm: init_mem se sk = Some m).
  Let bc := bc_of_symtbl se.

  Lemma init_mem_block_classification:
    genv_match bc se
    /\ bc_below bc (Mem.nextblock m)
    /\ bc_nostack bc
    /\ (forall b id, bc b = BCglob id -> Genv.find_symbol se id = Some b)
    /\ (forall b, Mem.valid_block m b -> bc b <> BCinvalid).
  Admitted.

  Lemma init_mem_matches:
    forall cu, Genv.valid_for (erase_program cu) se -> romatch bc m (romem_for cu).
  Proof.
    intros. red. intros * Hb Hid.
    assert (B: romem_consistent (prog_defmap cu) (romem_for cu))
      by apply romem_for_consistent.
  Admitted.

End VA.

Require Import Compiler.

Section INIT_C_ASM.

  Local Transparent Archi.ptr64.

  Lemma match_stbls_flat_inj se:
    Genv.match_stbls (Mem.flat_inj (Genv.genv_next se)) se se.
  Proof.
    split; eauto; unfold Mem.flat_inj; intros.
    - destruct plt; try easy. eexists. reflexivity.
    - intros. unfold Mem.flat_inj. exists b2. destruct plt; try easy.
    - destruct plt; try easy. inv H. reflexivity.
    - destruct plt; try easy. inv H. reflexivity.
    - destruct plt; try easy. inv H. reflexivity.
  Qed.

  Lemma match_prog_skel p tp:
    match_prog p tp -> erase_program p = erase_program tp.
  Proof.
    intros. edestruct clight_semantic_preservation as [H1 ?]; eauto.
    destruct H1. destruct X. apply fsim_skel.
  Qed.

  Lemma init_c_asm p tp:
    match_prog p tp -> forward_simulation cc_compcert 1 (init_c p) (init_asm tp).
  Proof.
    intros H. assert (Hsk: erase_program p = erase_program tp).
    eapply match_prog_skel; eauto.
    constructor. econstructor. apply Hsk.
    intros. reflexivity.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta. destruct H0.
    eapply forward_simulation_step with (match_states := eq).
    - intros. inv H0. inv H2.
      eexists; split; eauto. constructor.
    - intros. inv H2. exists r1. split; constructor.
    - intros. inv H2.
      eexists _, (_, m).
      repeat apply conj.
      + assert (exists tf, (prog_defmap tp) ! main = Some (Gfun tf)) as (tf & Htf).
        { assert ((prog_defmap (erase_program p)) ! main = Some (Gfun tt)).
          rewrite erase_program_defmap. unfold option_map. rewrite H7. reflexivity.
          rewrite Hsk in H0. rewrite erase_program_defmap in H0.
          unfold option_map in H0.
          destruct (prog_defmap tp) ! main as [[tf|]|] eqn: Htf; inv H0.
          exists tf. split; eauto. }
        econstructor; eauto.
        * rewrite <- Hsk. eauto.
        * replace (AST.prog_main tp) with (AST.prog_main (erase_program tp))
            by reflexivity.
          rewrite <- Hsk. apply H6.
      + unfold cc_compcert.
        (* cklr *)
        instantiate (1 := (se1, existT _ 0%nat _, _)).
        exists (cq (Vptr b Ptrofs.zero) main_sig [] m). split.
        { reflexivity. }
        (* inv wt_c *)
        instantiate (1 := (se1, (se1, main_sig), _)).
        exists (cq (Vptr b Ptrofs.zero) main_sig [] m). split.
        { repeat constructor. }
        (* lessdef_c *)
        instantiate (1 := (se1, tt, _)).
        exists (cq (Vptr b Ptrofs.zero) main_sig [] m). split.
        { repeat constructor. }
        (* cc_c_locset *)
        instantiate (1 := (se1, main_sig, _)).
        eexists (Conventions.lq (Vptr b Ptrofs.zero) main_sig (CallConv.make_locset (Mach.Regmap.init Vundef) m (Vptr b Ptrofs.zero)) m). split.
        { constructor. unfold Conventions1.loc_arguments. cbn.
          destruct Archi.win64; reflexivity. }
        (* cc_locset_mach *)
        set (rs := ((((Pregmap.init Vundef) # PC <- (Vptr b Ptrofs.zero)) # SP <- (Vptr b Ptrofs.zero)) # RA <- Vnullptr)).
        instantiate (1 := (se1, CallConv.lmw main_sig (Mach.Regmap.init Vundef) m (Vptr b Ptrofs.zero), _)).
        eexists (Mach.mq rs#PC rs#SP rs#RA (Mach.Regmap.init Vundef) m). split.
        { repeat constructor.
          red. unfold Conventions.size_arguments. cbn. destruct Archi.win64; reflexivity. }
        (* cc_mach_asm *)
        instantiate (1 := (se1, ((((Pregmap.init Vundef) # PC <- (Vptr b Ptrofs.zero)) # RSP <- (Vptr b Ptrofs.zero)) # RA <- Vnullptr, Mem.nextblock m), _)).
        eexists ((((Pregmap.init Vundef) # PC <- (Vptr b Ptrofs.zero)) # RSP <- (Vptr b Ptrofs.zero)) # RA <- Vnullptr, m). split.
        { econstructor; cbn; try congruence.
          - constructor. erewrite init_mem_nextblock; eauto.
            apply Genv.invert_find_symbol in H4.
            exploit @Genv.genv_symb_range; eauto.
          - intros. destruct r; eauto. }
        (* cc_asm vainj *)
        instantiate (1 := (se1, Inject.injw (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m) (Mem.nextblock m))).
        repeat apply conj; cbn; eauto; try easy.
        * intros.
          assert (Val.inject (Mem.flat_inj (Mem.nextblock m)) (Vptr b Ptrofs.zero) (Vptr b Ptrofs.zero)).
          { eapply Val.inject_ptr. unfold Mem.flat_inj.
             destruct plt. reflexivity.
             exfalso. apply n. erewrite init_mem_nextblock; eauto.
             eapply Genv.genv_symb_range; eauto.
             apply Genv.invert_find_symbol; eauto. reflexivity. }
          destruct r; eauto; cbn; try constructor; eauto.
          destruct i; eauto; cbn.
        * constructor; cbn.
          -- erewrite init_mem_nextblock; eauto. reflexivity.
          -- intros x Hx. eapply init_mem_matches; eauto.
          -- constructor. eapply initmem_inject; eauto.
      + cbn. repeat apply conj; eauto. constructor. eauto.
        constructor; cbn; erewrite init_mem_nextblock; eauto; try easy.
        apply match_stbls_flat_inj.
      + intros. inv H2. exists (Some i). split; eauto.
        cbn in H0.
        destruct H0 as (r3 & Hr3 & HR). inv Hr3.
        destruct HR as (r3 & Hr3 & HR). inv Hr3.
        destruct HR as (r3 & Hr3 & HR). inv Hr3. inv H9.
        destruct HR as (r3 & Hr3 & HR). inv Hr3. cbn in H9.
        destruct HR as (r3 & Hr3 & HR). inv Hr3.
        specialize (H13 AX). rewrite <- H9 in H13.
        exploit H13. cbn. left. reflexivity. intros HAX.
        destruct HR as ((rs & mx) & Hr3 & Hr4). inv Hr3.
        specialize (H20 AX). rewrite HAX in H20. cbn in H20.
        destruct Hr4 as ((? & ?) & ? & Hr). destruct r2.
        inv Hr. specialize (H5 RAX). rewrite <- H20 in H5.
        destruct H2. cbn in H10. cbn in H5. inv H5.
        constructor. easy.
    - easy.
    - easy.
    Unshelve. cbn. exact tt.
  Qed.

End INIT_C_ASM.

Variant sys_query :=
  | write_query: list byte -> sys_query
  | read_query: int64 -> sys_query.

Variant sys_reply :=
  | write_reply: int -> sys_reply
  | read_reply: list byte -> sys_reply.

Definition li_sys :=
  {|
    query := sys_query;
    reply := sys_reply;
    entry q := Vundef;
  |}.

Notation tvoid := (Tvoid).
Notation tchar := (Tint I8 Unsigned noattr).
Notation tlong := (Tlong Unsigned noattr).
Notation tptr := (fun ty => Tpointer ty noattr).

Definition rw_parameters := Tcons tint (Tcons (tptr tchar) (Tcons tlong Tnil)).
Definition rw_type :=
  Tfunction rw_parameters tint cc_default.
Definition rw_sig : signature :=
  signature_of_type rw_parameters tvoid cc_default.
Definition write : Clight.fundef :=
  External (EF_external "write" rw_sig) rw_parameters tint cc_default.
Definition read : Clight.fundef :=
  External (EF_external "read" rw_sig) rw_parameters tint cc_default.

Section SYS.
  Context (prog: Clight.program).
  Let sk := erase_program prog.
  Section WITH_SE.
    Context (se: Genv.symtbl).
    Let ge := globalenv se prog.
    Variant sys_state :=
      | sys_read_query (n: int64) (b: block) (ofs: ptrofs) (m: mem)
      | sys_read_reply (bytes: list byte) (b: block) (ofs: ptrofs) (m: mem)
      | sys_write_query (bytes: list byte) (m: mem)
      | sys_write_reply (n: int) (m: mem).

    Inductive sys_c_initial_state: query li_c -> sys_state -> Prop :=
    | sys_c_initial_state_read vf args m n b ofs:
      Genv.find_funct ge vf = Some read ->
      args = [ Vint (Int.repr 0); Vptr b ofs; Vlong n ] ->
      sys_c_initial_state (cq vf rw_sig args m) (sys_read_query n b ofs m)
    | sys_c_initial_state_write vf args m bytes bytes_val b ofs len:
      Genv.find_funct ge vf = Some write ->
      args = [ Vint (Int.repr 1); Vptr b ofs; Vlong (Int64.repr len) ] ->
      Mem.loadbytes m b (Ptrofs.unsigned ofs) len = Some bytes_val ->
      map Byte bytes = bytes_val ->
      sys_c_initial_state (cq vf rw_sig args m) (sys_write_query bytes m).

    Inductive sys_c_at_external: sys_state -> query (li_sys + li_sys) -> Prop :=
    | sys_c_at_external_read n b ofs m:
      sys_c_at_external (sys_read_query n b ofs m) (inl (read_query n))
    | sys_c_at_external_write bytes m:
      sys_c_at_external (sys_write_query bytes m) (inr (write_query bytes)).

    Inductive sys_c_after_external: sys_state -> reply (li_sys + li_sys) -> sys_state -> Prop :=
    | sys_c_after_external_read n b ofs m bytes:
      Z.of_nat (length bytes) <= Int64.unsigned n ->
      sys_c_after_external (sys_read_query n b ofs m) (inl (read_reply bytes)) (sys_read_reply bytes b ofs m)
    | sys_c_after_external_write n m bytes:
      sys_c_after_external (sys_write_query bytes m) (inr (write_reply n)) (sys_write_reply n m).

    Inductive sys_c_final_state: sys_state -> reply li_c -> Prop :=
    | sys_c_final_state_read bytes b ofs bytes_val m len m':
      len = Z.of_nat (length bytes) ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes_val = Some m' ->
      map Byte bytes = bytes_val ->
      sys_c_final_state (sys_read_reply bytes b ofs m) (cr (Vint (Int.repr len)) m')
    | sys_c_final_state_write n m:
      sys_c_final_state (sys_write_reply n m) (cr (Vint n) m).

  End WITH_SE.
  Definition sys_c: Smallstep.semantics (li_sys + li_sys) li_c :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := sys_c_initial_state se;
          Smallstep.at_external := sys_c_at_external;
          Smallstep.after_external := sys_c_after_external;
          Smallstep.final_state := sys_c_final_state;
          Smallstep.globalenv := Genv.globalenv se prog;
        |};
      skel := sk;
      footprint i := False
    |}.

End SYS.

Section SYS_ASM.
  Context (prog: Asm.program).
  Let sk := erase_program prog.
  Section WITH_SE.
    Context (se: Genv.symtbl).
    Let ge := Genv.globalenv se prog.

    Definition read_asm : fundef := AST.External (EF_external "read_asm" rw_sig).
    Definition write_asm : fundef := AST.External (EF_external "write_asm" rw_sig).
    Inductive sys_asm_initial_state: query li_asm -> sys_state -> Prop :=
    | sys_asm_initial_state_read m n b ofs rs:
      Genv.find_funct ge rs#PC = Some read_asm ->
      rs#RDI = Vint (Int.repr 0) ->
      rs#RSI = Vptr b ofs ->
      rs#RDX = Vlong n ->
      sys_asm_initial_state (rs, m) (sys_read_query n b ofs m)
    | sys_asm_initial_state_write m bytes bytes_val b ofs n rs:
      Genv.find_funct ge rs#PC = Some write_asm ->
      rs#RDI = Vint (Int.repr 1) ->
      rs#RSI = Vptr b ofs ->
      rs#RDX = Vlong n ->
      Mem.loadbytes m b (Ptrofs.unsigned ofs) (Int64.unsigned n) = Some bytes_val ->
      map Byte bytes = bytes_val ->
      sys_asm_initial_state (rs, m) (sys_write_query bytes m).

    Inductive sys_asm_at_external: sys_state -> query (li_sys + li_sys) -> Prop :=
    | sys_asm_at_external_read n b ofs m:
      sys_asm_at_external (sys_read_query n b ofs m) (inl (read_query n))
    | sys_asm_at_external_write bytes m:
      sys_asm_at_external (sys_write_query bytes m) (inr (write_query bytes)).

    Inductive sys_asm_after_external: sys_state -> reply (li_sys + li_sys) -> sys_state -> Prop :=
    | sys_asm_after_external_read n b ofs m bytes:
      Z.of_nat (length bytes) <= Int64.unsigned n ->
      sys_asm_after_external (sys_read_query n b ofs m) (inl (read_reply bytes)) (sys_read_reply bytes b ofs m)
    | sys_asm_after_external_write n m bytes:
      sys_asm_after_external (sys_write_query bytes m) (inr (write_reply n)) (sys_write_reply n m).

    Inductive sys_asm_final_state: sys_state -> reply li_asm -> Prop :=
    | sys_asm_final_state_read bytes b ofs bytes_val m len m' (rs: regset):
      len = Z.of_nat (length bytes) ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes_val = Some m' ->
      map Byte bytes = bytes_val ->
      rs#RAX = Vint (Int.repr len) ->
      sys_asm_final_state (sys_read_reply bytes b ofs m) (rs, m')
    | sys_asm_final_state_write n m (rs: regset):
      rs#RAX = Vint n ->
      sys_asm_final_state (sys_write_reply n m) (rs, m).

  End WITH_SE.
  Definition sys_asm: Smallstep.semantics (li_sys + li_sys) li_asm :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := sys_asm_initial_state se;
          Smallstep.at_external := sys_asm_at_external;
          Smallstep.after_external := sys_asm_after_external;
          Smallstep.final_state := sys_asm_final_state;
          Smallstep.globalenv := Genv.globalenv se prog;
        |};
      skel := sk;
      footprint i := False
    |}.

End SYS_ASM.

Section SYS_C_ASM.

  Local Transparent Archi.ptr64.

  Require Import CallconvAlgebra CallConv CKLR.
  Require Import Inject.
  Require Import InjectFootprint.
  Require Import Extends.
  Require Import VAInject.
  Require Import VAExtends.

(* Definition cc_cklrs : callconv li_c li_c := *)
(*   injp + inj + ext + vainj + vaext. *)

  Inductive mm_cklr: ccworld cc_cklrs -> mem -> mem -> Prop :=
  | mm_cklr_vaext w m m' (HM: match_mem vaext w m m'): mm_cklr (inr w) m m'
  | mm_cklr_vainj w m m' (HM: match_mem vainj w m m'): mm_cklr (inl (inr w)) m m'
  | mm_cklr_ext w m m' (HM: match_mem ext w m m'): mm_cklr (inl (inl (inr w))) m m'
  | mm_cklr_inj w m m' (HM: match_mem inj w m m'): mm_cklr (inl (inl (inl (inr w)))) m m'
  | mm_cklr_injp w m m' (HM: match_mem injp w m m'): mm_cklr (inl (inl (inl (inl w)))) m m'.

  Inductive mp_cklr: ccworld cc_cklrs -> block -> ptrofs -> block -> ptrofs -> Prop :=
  | mp_cklr_vaext w b ofs b' ofs'
      (HP: ptr_inject (mi vaext w) (b, (Ptrofs.unsigned ofs)) (b', (Ptrofs.unsigned ofs'))):
      mp_cklr (inr w) b ofs b' ofs'
  | mp_cklr_vainj w b ofs b' ofs'
      (HP: ptr_inject (mi vainj w) (b, (Ptrofs.unsigned ofs)) (b', (Ptrofs.unsigned ofs'))):
      mp_cklr (inl (inr w)) b ofs b' ofs'
  | mp_cklr_ext w b ofs b' ofs'
      (HP: ptr_inject (mi ext w) (b, (Ptrofs.unsigned ofs)) (b', (Ptrofs.unsigned ofs'))):
      mp_cklr (inl (inl (inr w))) b ofs b' ofs'
  | mp_cklr_inj w b ofs b' ofs'
      (HP: ptr_inject (mi inj w) (b, (Ptrofs.unsigned ofs)) (b', (Ptrofs.unsigned ofs'))):
      mp_cklr (inl (inl (inl (inr w)))) b ofs b' ofs'
  | mp_cklr_injp w b ofs b' ofs'
      (HP: ptr_inject (mi injp w) (b, (Ptrofs.unsigned ofs)) (b', (Ptrofs.unsigned ofs'))):
      mp_cklr (inl (inl (inl (inl w)))) b ofs b' ofs'.

  Lemma inject_bytes j bytes y:
    list_rel (memval_inject j) (map Byte bytes) y ->
    y = map Byte bytes.
  Proof.
    revert y. induction bytes; intros; inv H; eauto.
    cbn. f_equal.
    - inv H2. reflexivity.
    - eapply IHbytes. eauto.
  Qed.

  Lemma match_cklr_loadbytes w m b ofs m' b' ofs' len bytes:
    mm_cklr w m m' ->
    mp_cklr w b ofs b' ofs' ->
    Mem.loadbytes m b (Ptrofs.unsigned ofs) len = Some (map Byte bytes) ->
    Mem.loadbytes m' b' (Ptrofs.unsigned ofs') len = Some (map Byte bytes).
  Proof.
    intros Hm Hp Hl. inv Hm; inv Hp.
    - exploit cklr_loadbytes; eauto. unfold k1, uncurry. rewrite Hl.
      intros Ho. inv Ho. apply inject_bytes in H1. congruence.
    - exploit cklr_loadbytes; eauto. unfold k1, uncurry. rewrite Hl.
      intros Ho. inv Ho. apply inject_bytes in H1. congruence.
    - exploit cklr_loadbytes; eauto. unfold k1, uncurry. rewrite Hl.
      intros Ho. inv Ho. apply inject_bytes in H1. congruence.
    - exploit cklr_loadbytes; eauto. unfold k1, uncurry. rewrite Hl.
      intros Ho. inv Ho. apply inject_bytes in H1. congruence.
    - exploit cklr_loadbytes; eauto. unfold k1, uncurry. rewrite Hl.
      intros Ho. inv Ho. apply inject_bytes in H1. congruence.
  Qed.

  Hint Resolve ptr_ptrbits_inject_unsigned.

  Lemma bytes_inject j bytes:
    list_rel j (map Byte bytes) (map Byte bytes).
  Proof.
  Admitted.

  Lemma match_cklr_storebytes w m1 m2 m3 b1 ofs1 b2 ofs2 bytes:
    mm_cklr w m1 m2 ->
    mp_cklr w b1 ofs1 b2 ofs2 ->
    Mem.storebytes m1 b1 (Ptrofs.unsigned ofs1) (map Byte bytes) = Some m3 ->
    exists wx m4, Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) (map Byte bytes) = Some m4
             /\ mm_cklr wx m3 m4.
  Proof.
    intros Hm Hp Hs. inv Hm; inv Hp.
    - exploit @cklr_storebytes; eauto.
      apply ptrbits_rptr_inject_unsigned; eauto.
      apply bytes_inject.
      unfold k1, uncurry. rewrite Hs. intros. inv H.
      destruct H2 as (wx & Hw & Hm).
      eexists (inr wx), y. split; eauto. constructor. eauto.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Inductive mm_cklrs: ccworld (cc_cklrs^{*}) -> mem -> mem -> Prop :=
  | mm_cklrs_zero m: mm_cklrs (existT _ 0%nat tt) m m
  | mm_cklrs_succ n se w wn m1 m2 m3:
        mm_cklr w m1 m2 -> mm_cklrs (existT _ n wn) m2 m3 ->
        mm_cklrs (existT _ (S n) (se, w, wn)) m1 m3.

  Inductive mp_cklrs: ccworld (cc_cklrs^{*}) -> block -> ptrofs -> block -> ptrofs -> Prop :=
  | mp_cklrs_zero b ofs: mp_cklrs (existT _ 0%nat tt) b ofs b ofs
  | mp_cklrs_succ n se w wn b1 ofs1 b2 ofs2 b3 ofs3:
        mp_cklr w b1 ofs1 b2 ofs2 -> mp_cklrs (existT _ n wn) b2 ofs2 b3 ofs3 ->
        mp_cklrs (existT _ (S n) (se, w, wn)) b1 ofs1 b3 ofs3.

  Require Import Classical.

  Ltac subst_dep :=
    subst;
    lazymatch goal with
    | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
        apply inj_pair2 in H; subst_dep
    | _ => idtac
    end.

  (* Lemma match_cklrs_loadbytes n w m1 b1 ofs1 m2 b2 ofs2 len bytes: *)
  (*   match_cklrs n w m1 b1 ofs1 m2 b2 ofs2 -> *)
  (*   Mem.loadbytes m1 b1 ofs1 len = Some (map Byte bytes) -> *)
  (*   Mem.loadbytes m2 b2 ofs2 len = Some (map Byte bytes). *)
  (* Proof. *)
  (*   revert w m1 b1 ofs1 m2 b2 ofs2 bytes. *)
  (*   induction n; intros; inv H; eauto. *)
  (*   subst_dep. eauto using match_cklr_loadbytes. *)
  (* Qed. *)

  Inductive mm_ca: ccworld (cc_cklrs^{*}) -> world inj -> mem -> mem -> Prop :=
  | mm_ca_intro wn wi m1 m2 m3:
    mm_cklrs wn m1 m2 -> match_mem inj wi m2 m3 -> mm_ca wn wi m1 m3.

  Inductive mp_ca: ccworld (cc_cklrs^{*}) -> world inj -> block -> ptrofs -> block -> ptrofs -> Prop :=
  | mp_ca_intro wn wi b1 ofs1 b2 ofs2 b3 ofs3:
    mp_cklrs wn b1 ofs1 b2 ofs2 ->
    ptr_inject (mi inj wi) (b2, (Ptrofs.unsigned ofs2)) (b3, (Ptrofs.unsigned ofs3)) ->
    mp_ca wn wi b1 ofs1 b3 ofs3.

  Lemma ca_storebytes n w m1 b1 ofs1 m2 b2 ofs2 bytes m3:
    mm_ca n w m1 m2 ->
    Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) (map Byte bytes) = Some m3 ->
    exists m4, Mem.storebytes m1 b1 (Ptrofs.unsigned ofs1) (map Byte bytes) = Some m4
          /\ mm_ca n w m4 m3.
  Admitted.

  Inductive match_sys_state:
    ccworld (cc_cklrs^{*}) -> world inj -> sys_state -> sys_state -> Prop :=
  | match_sys_state_read_query wn wi len b1 ofs1 m1 b2 ofs2 m2:
      mm_ca wn wi m1 m2 ->
      mp_ca wn wi b1 ofs1 b2 ofs2 ->
      match_sys_state wn wi (sys_read_query len b1 ofs1 m1) (sys_read_query len b2 ofs2 m2)
  | match_sys_state_read_reply wn wi bytes b1 ofs1 m1 b2 ofs2 m2:
      mm_ca wn wi m1 m2 ->
      mp_ca wn wi b1 ofs1 b2 ofs2 ->
      match_sys_state wn wi (sys_read_reply bytes b1 ofs1 m1) (sys_read_reply bytes b2 ofs2 m2).

  (*   Variant sys_state := *)
  (*     | sys_read_query (n: int64) (b: block) (ofs: ptrofs) (m: mem) *)
  (*     | sys_read_reply (bytes: list byte) (b: block) (ofs: ptrofs) (m: mem) *)
  (*     | sys_write_query (bytes: list byte) (m: mem) *)
  (*     | sys_write_reply (n: int) (m: mem). *)

  Definition nw_of_world (w: ccworld cc_compcert): sigT (fun n => ccworld (cc_cklrs ^ n)).
  Proof. cbn in w. destruct w. destruct p. exact s0. Defined.

  Definition injw_of_world (w: ccworld cc_compcert): world inj.
  Proof. cbn in w. eprod_crush. exact i. Defined.

  Import ListNotations.

  Lemma cklrs_match_query_inv (nw: ccworld (cc_cklrs ^ {*})) b ofs len m q vf:
    match_query (cc_cklrs ^ {*}) nw
                (cq vf rw_sig [Vint (Int.repr 0); Vptr b ofs; Vlong len] m)
                q ->
    exists m' b' ofs' vf',
      q = (cq vf' rw_sig [Vint (Int.repr 0); Vptr b' ofs'; Vlong len] m')
      /\ mm_cklrs nw m m' /\ mp_cklrs nw b ofs b' ofs'.
  Proof.
  Admitted.

  Hypothesis (Hwin64: Archi.win64 = false).

  Lemma free_empty: forall m b x m',
      Mem.free m b x x = Some m' -> m = m'.
  Proof.
    intros. apply Mem.free_result in H. subst.
    unfold Mem.unchecked_free. destruct m. cbn.
    eapply Mem.mkmem_ext; eauto.
    destruct mem_access. unfold PMap.set. cbn. f_equal.
    induction t.
    (* PTree.extensionality_empty *)
  Admitted.

  Lemma sys_c_asm p tp:
    match_prog p tp -> forward_simulation 1 cc_compcert (sys_c p) (sys_asm tp).
  Proof.
    intros H. assert (Hsk: erase_program p = erase_program tp).
    eapply match_prog_skel; eauto.
    constructor. econstructor. apply Hsk.
    intros. reflexivity.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    set (ms := match_sys_state (nw_of_world wB) (injw_of_world wB)).
    eapply forward_simulation_step with (match_states := fun s1 s2 => ms s1 s2).
    - intros. inv H3.
      + unfold cc_compcert in *. cbn in wB, H2 |- *.
        eprod_crush. destruct s9. inv H3. destruct H10; subst. cbn in *.
        (* cklrs *)
        eapply (cklrs_match_query_inv (existT _ x4 c0)) in H2 as
            (mx & bx & ofsx & vfx & Hqx & Hmx & Hpx). subst x0.
        (* lessdef *)
        inv H5.
        repeat match goal with
        | [ H: Val.lessdef_list _ _ |- _ ] => inv H
        | [ H: Val.lessdef _ _ |- _ ] => inv H
        end.
        (* cc_c_locset *)
        inv H6.
        (* cc_locset_mach: need to show args_removed changes nothing *)
        inv H7.
        inv H14. inv H2.
        { admit. }
        cbn in H2. rewrite Hwin64 in H2. cbn in H2. apply free_empty in H2. subst m1.
        (* cc_mach_asm *)
        inv H8.
        (* cc_asm vainj *)
        destruct q2. destruct H9. destruct H8.
        (* arguments *)
        cbn in H13. rewrite Hwin64 in H13. cbn in H13. inv H13.
        assert (exists b' ofs', r0#RSI = Vptr b' ofs' /\ Val.inject i (Vptr bx ofsx) (Vptr b' ofs')) as (b' & ofs' & Hofs & Hb').
        { admit. }
        eexists (sys_read_query n b' ofs' m1). split.
        * econstructor; eauto.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
        * constructor.
          (* mem *)
          -- econstructor; eauto. inv H9; auto.
          (* ptr *)
          -- econstructor; eauto. admit.
             (* ptr_ptrbits_inject_unsigned *)
      + admit.
    - intros. inv H3.
      + admit.



  Admitted.

End SYS_C_ASM.

Require Import CategoricalComp.

Definition load_c (prog: Clight.program) : Smallstep.semantics (li_sys + li_sys) li_wp :=
  let sk := AST.erase_program prog in
  comp_semantics' (init_c prog)
    (comp_semantics' (semantics1 prog) (sys_c prog) sk) sk.
