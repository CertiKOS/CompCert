Require Import Coqlib Integers.

Require Import Events LanguageInterface Smallstep Globalenvs Values Memory.
Require Import AST Ctypes Clight.
Require Import Lifting Encapsulation.

Require Import List Maps.
Import ListNotations.
Require Import Machregs Asm.

Require Import InitMem With.

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

Require Import Compiler.

Section INIT_C_ASM.

  Local Transparent Archi.ptr64.

  Lemma init_c_asm p tp:
    match_prog p tp -> forward_simulation cc_compcert 1 (init_c p) (init_asm tp).
  Proof.
    intros H. assert (Hsk: erase_program p = erase_program tp).
    { apply clight_semantic_preservation in H as [H1 ?].
      apply H1. }
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
        * intros. destruct r; eauto; cbn; try constructor.
          eapply Val.inject_ptr. unfold Mem.flat_inj. admit. admit. admit.
        * constructor; cbn.
          -- erewrite init_mem_nextblock; eauto. reflexivity.
          -- intros x Hx.  admit.
          -- constructor. unfold Mem.inject.
             (* Search (Mem.inject _ ?m ?m). *)
             (* Search Mem.inject_neutral. *)
             admit.
      + cbn. repeat apply conj; eauto. constructor. eauto.
        constructor; cbn.
        (* Search (Genv.match_stbls _ ?se ?se). *)
        admit. admit. admit.
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
  Admitted.

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

  Lemma sys_c_asm p tp:
    match_prog p tp -> forward_simulation 1 cc_compcert (sys_c p) (sys_asm tp).
  Proof.
    intros H. assert (Hsk: erase_program p = erase_program tp).
    { apply clight_semantic_preservation in H as [H1 ?].
      apply H1. }
    constructor. econstructor. apply Hsk.
    intros. reflexivity.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := eq).
    - intros. inv H3.
      + unfold cc_compcert in *. cbn in wB, H2 |- *.
        eprod_crush. destruct s9. inv H3.
  Admitted.

End SYS_C_ASM.

Require Import CategoricalComp.

Definition load_c (prog: Clight.program) : Smallstep.semantics (li_sys + li_sys) li_wp :=
  let sk := AST.erase_program prog in
  comp_semantics' (init_c prog)
    (comp_semantics' (semantics1 prog) (sys_c prog) sk) sk.
