Require Import Coqlib Integers.

Require Import Events LanguageInterface Smallstep Globalenvs Values Memory.
Require Import AST Ctypes Clight.
Require Import Lifting Encapsulation.

Require Import List Maps.
Import ListNotations.

Notation hello_bytes := [ Byte.repr 104; Byte.repr 101; Byte.repr 108; Byte.repr 108; Byte.repr 111 ].
Notation urbby_bytes := [ Byte.repr 117; Byte.repr 114; Byte.repr 98; Byte.repr 98; Byte.repr 121].
Definition rot13_byte : byte -> byte. Admitted.
Definition rot13_bytes_i : list byte -> Z -> list byte. Admitted.
Definition rot13_bytes : list byte -> list byte. Admitted.
Lemma rot13_bytes_hello: rot13_bytes hello_bytes = urbby_bytes. Admitted.
Lemma rot13_bytes_urbby: rot13_bytes urbby_bytes = hello_bytes. Admitted.

Notation tvoid := (Tvoid).
Notation tchar := (Tint I8 Unsigned noattr).
Notation tint := (Tint I32 Unsigned noattr).
Notation tlong := (Tlong Unsigned noattr).
Notation tarray := (fun ty size => Tarray ty size noattr).
Notation tptr := (fun ty => Tpointer ty noattr).

Definition rw_parameters := Tcons tint (Tcons (tptr tchar) (Tcons tlong Tnil)).
Definition rw_type :=
  Tfunction rw_parameters tint cc_default.
Definition rw_sig : signature :=
  signature_of_type rw_parameters tvoid cc_default.
Definition write : fundef :=
  External (EF_external "write" rw_sig) rw_parameters tint cc_default.
Definition read : fundef :=
  External (EF_external "read" rw_sig) rw_parameters tint cc_default.

Definition main_sig := signature_of_type Tnil tint cc_default.

Definition secret_main_id: positive := 1.
Definition secret_write_id: positive := 2.
Definition secret_msg_id: positive := 3.

Definition msg_il : list init_data :=
  [ Init_int8 (Int.repr 117); (* u *)
    Init_int8 (Int.repr 114); (* r *)
    Init_int8 (Int.repr 98); (* b *)
    Init_int8 (Int.repr 98); (* b *)
    Init_int8 (Int.repr 121) ]. (* y *)

Definition msg_globvar : globvar type :=
  {|
    gvar_info := tarray tchar 6%Z;
    gvar_init := msg_il;
    gvar_readonly := false;
    gvar_volatile := false;
  |}.

Definition secret_main_body : statement :=
  Ssequence
    (* write(1, msg, sizeof msg - 1) *)
    (Scall None (Evar secret_write_id rw_type)
       [ Econst_int (Int.repr 1) tint;
         Eaddrof (Evar secret_msg_id (tptr tchar)) (tptr tchar);
         Econst_long (Int64.repr 5) tlong ]) (* sizeof msg - 1 *)
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).

Definition secret_main : function :=
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := [];
    fn_temps := [];
    fn_vars := [];
    fn_body := secret_main_body;
  |}.

Program Definition secret_program : Clight.program :=
  {|
    prog_defs := [ (secret_main_id, Gfun (Internal secret_main));
                   (secret_write_id, Gfun write);
                   (secret_msg_id, Gvar msg_globvar)
    ];
    prog_public := [ secret_main_id ];
    prog_main := Some secret_main_id;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.

Section INIT_MEM.
  Context (se: Genv.symtbl).

  Program Definition empty : mem :=
    Mem.mkmem (PMap.init (ZMap.init Undef))
      (PMap.init (fun ofs k => None))
      (Genv.genv_next se) true _ _ _.

  (* like [Mem.alloc], but only changes the perm *)
  Program Definition init_perm (m: mem) (b: block) (lo hi: Z) :=
    if plt b m.(Mem.nextblock) then
      Some
        (Mem.mkmem
           m.(Mem.mem_contents)
           (PMap.set b
              (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
              m.(Mem.mem_access))
           m.(Mem.nextblock) m.(Mem.alloc_flag) _ _ _)
    else None.
  Next Obligation.
    repeat rewrite PMap.gsspec. destruct (peq b0 b).
    - subst b. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
    - apply Mem.access_max.
  Qed.
  Next Obligation.
    repeat rewrite PMap.gsspec. destruct (peq b0 b).
    - subst b. elim H0. exact H.
    - eapply Mem.nextblock_noaccess. exact H0.
  Qed.
  Next Obligation. apply Mem.contents_default. Qed.

  Definition init_global' (m: mem) (b: block) (g: globdef unit unit): option mem :=
    match g with
    | Gfun f =>
        match init_perm m b 0 1 with
        | Some m1 => Mem.drop_perm m1 b 0 1 Nonempty
        | None => None
        end
    | Gvar v =>
        let init := v.(gvar_init) in
        let sz := init_data_list_size init in
        match init_perm m b 0 sz with
        | Some m1 =>
            match store_zeros m1 b 0 sz with
            | None => None
            | Some m2 =>
                match Genv.store_init_data_list se m2 b 0 init with
                | None => None
                | Some m3 => Mem.drop_perm m3 b 0 sz (Genv.perm_globvar v)
                end
            end
        | None => None
        end
    end.

  Definition init_global (m: mem) (idg: ident * globdef unit unit): option mem :=
    match idg with
    | (id, g) =>
        match Genv.find_symbol se id with
        | Some b => init_global' m b g
        | None => None
        end
    end.

  Fixpoint init_globals (m: mem) (gl: list (ident * globdef unit unit)): option mem :=
    match gl with
    | [] => Some m
    | g :: gl' =>
        match init_global m g with
        | None => None
        | Some m' => init_globals m' gl'
        end
    end.

  Definition init_mem (p: AST.program unit unit) : option mem :=
    init_globals empty p.(AST.prog_defs).

  Lemma init_perm_inv m1 m2 lo hi b:
    init_perm m1 b lo hi = Some m2 ->
    forall ofs k, lo <= ofs < hi -> Mem.perm m2 b ofs k Freeable.
  Proof.
    intros. unfold init_perm in H. destruct plt; inv H.
    unfold Mem.perm. cbn. rewrite PMap.gss.
    destruct (zle lo ofs && zlt ofs hi) eqn: H1; try constructor.
    exfalso. destruct zle eqn: H2; try lia. destruct zlt eqn: H3; try lia.
    cbn in H1. congruence.
  Qed.

  Lemma init_global_exists:
    forall m idg,
      (exists b, Genv.find_symbol se (fst idg) = Some b /\
              Plt b m.(Mem.nextblock)) ->
      match idg with
      | (id, Gfun f) => True
      | (id, Gvar v) =>
          Genv.init_data_list_aligned 0 v.(gvar_init)
          /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, Genv.find_symbol se i = Some b
      end ->
      exists m', init_global m idg = Some m'.
  Proof.
    intros m [id [f|v]] [b [Hb1 Hb2]]; intros; simpl in *; rewrite Hb1.
    - destruct (init_perm m b 0 1) as [m1|] eqn:H1.
      2: { exfalso. unfold init_perm in H1. destruct plt; [ inv H1 | contradiction ]. }
      destruct (Mem.range_perm_drop_2 m1 b 0 1 Nonempty) as [m2 DROP].
      red; intros; eapply init_perm_inv; eauto.
      exists m2. eauto.
    - destruct H as [P Q].
      set (sz := init_data_list_size (gvar_init v)).
      destruct (init_perm m b 0 sz) as [m1|] eqn:H1.
      2: { exfalso. unfold init_perm in H1. destruct plt; [ inv H1 | contradiction ]. }
      assert (P1: Mem.range_perm m1 b 0 sz Cur Freeable) by (red; intros; eapply init_perm_inv; eauto).
      exploit (@Genv.store_zeros_exists m1 b 0 sz).
      { red; intros. apply Mem.perm_implies with Freeable; auto with mem. }
      intros [m2 ZEROS]. rewrite ZEROS.
      assert (P2: Mem.range_perm m2 b 0 sz Cur Freeable).
      { red; intros. erewrite <- Genv.store_zeros_perm by eauto. eauto. }
      exploit (@Genv.store_init_data_list_exists se b (gvar_init v) m2 0); eauto.
      { red; intros. apply Mem.perm_implies with Freeable; auto with mem. }
      intros [m3 STORE]. rewrite STORE.
      assert (P3: Mem.range_perm m3 b 0 sz Cur Freeable).
      { red; intros. erewrite <- Genv.store_init_data_list_perm by eauto. eauto. }
      destruct (Mem.range_perm_drop_2 m3 b 0 sz (Genv.perm_globvar v)) as [m4 DROP]; auto.
      exists m4; auto.
  Qed.

  Lemma init_perm_nextblock m1 m2 b lo hi:
    init_perm m1 b lo hi = Some m2 ->
    Mem.nextblock m2 = Mem.nextblock m1.
  Proof.
    intros. unfold init_perm in H. destruct plt; inv H.
    cbn. reflexivity.
  Qed.

  Lemma init_global_nextblock m1 m2 idg:
    init_global m1 idg = Some m2 ->
    Mem.nextblock m1 = Mem.nextblock m2.
  Proof.
    intros. unfold init_global in H. destruct idg as [id [f|v]]; simpl in H.
    - destruct (Genv.find_symbol se id) as [b|] eqn: H1; inv H.
      destruct (init_perm m1 b 0 1) as [m|] eqn: A1; inv H2.
      erewrite <- init_perm_nextblock; [ | eauto ].
      erewrite <- Mem.nextblock_drop; eauto.
    - destruct (Genv.find_symbol se id) as [b|] eqn: H1; inv H.
      destruct init_perm as [m3|] eqn: A1; inv H2.
      destruct store_zeros as [m4|] eqn: A2; inv H0.
      destruct Genv.store_init_data_list as [m5|] eqn: A3; inv H2.
      erewrite <- init_perm_nextblock; [ | eauto ].
      erewrite <- Genv.store_zeros_nextblock; [ | eauto ].
      erewrite <- Genv.store_init_data_list_nextblock; [ | eauto ].
      erewrite <- Mem.nextblock_drop; eauto.
  Qed.

  Lemma init_mem_exists p:
    (forall id v, In (id, Gvar v) (AST.prog_defs p) ->
             Genv.init_data_list_aligned 0 v.(gvar_init)
             /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, Genv.find_symbol se i = Some b) ->
    Genv.valid_for p se ->
    exists m, init_mem p = Some m.
  Proof.
    intros. unfold init_mem.
    assert (H1: forall id g,
               In (id, g) (AST.prog_defs p) ->
               exists b, Genv.find_symbol se id = Some b
                    /\ Plt b (Mem.nextblock empty)).
    {
      intros. edestruct prog_defmap_dom as [g' Hg'].
      unfold prog_defs_names. apply in_map_iff.
      exists (id, g). split; eauto. cbn in Hg'.
      specialize (H0 _ _ Hg') as (b & ? & Hb & ? & ?).
      exists b; split; eauto.
      unfold empty. cbn. eapply Genv.genv_symb_range.
      apply Hb.
    }
    clear H0.
    revert H H1. generalize (AST.prog_defs p) empty.
    induction l as [ | idg l ]; simpl; intros.
    - exists m. reflexivity.
    - destruct (@init_global_exists m idg) as [m1 A1].
      + destruct idg as [id g]. apply (H1 id g). left; easy.
      + destruct idg as [id [f|v]]; eauto.
      + rewrite A1. edestruct (IHl m1) as [m2 IH]; eauto.
        intros. erewrite <- init_global_nextblock; eauto.
  Qed.

  Lemma init_mem_nextblock p m:
    init_mem p = Some m ->
    Mem.nextblock m = Genv.genv_next se.
  Proof.
    assert (H: Mem.nextblock empty = Genv.genv_next se) by reflexivity.
    revert H. unfold init_mem. generalize (AST.prog_defs p) empty.
    induction l as [ | idg l ]; simpl; intros.
    - inv H0. eauto.
    - destruct init_global eqn: A1; inv H0.
      erewrite <- IHl; [ eauto | | eauto ].
      rewrite <- H. symmetry.  eapply init_global_nextblock; eauto.
  Qed.

  Lemma init_mem_alloc_flag p m:
    init_mem p = Some m ->
    Mem.alloc_flag m = true.
  Proof.
  Admitted.

End INIT_MEM.

Section INIT_C.
  Context (prog: program).
  Let sk := erase_program prog.
  Section WITH_SE.

    Context (se: Genv.symtbl).
    Let ge := Genv.globalenv se prog.
    Inductive init_c_initial_state (q: query li_wp) : option int -> Prop :=
    | init_c_initial_state_intro: init_c_initial_state q None.
    Inductive init_c_at_external: option int -> query li_c -> Prop :=
    | init_c_at_external_intro vf m f main:
      init_mem se sk = Some m ->
      Genv.find_funct ge vf = Some f ->
      prog_main prog = Some main ->
      (prog_defmap prog) ! main = Some (Gfun f) ->
      init_c_at_external None (cq vf main_sig [] m).
    Inductive init_c_after_external: option int -> reply li_c -> option int -> Prop :=
    | init_c_after_external_intro i m:
      init_c_after_external None (cr (Vint i) m) (Some i).
    Inductive init_c_final_state: option int -> reply li_wp -> Prop :=
    | inic_c_final_state_intro i: init_c_final_state (Some i) i.

  End WITH_SE.
  Program Definition init_c: semantics li_c li_wp :=
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

Require Import Machregs Asm.

Section INIT_ASM.
  Context (prog: program).
  Let sk := erase_program prog.
  Section WITH_SE.

    Context (se: Genv.symtbl).
    Let ge := Genv.globalenv se prog.
    Inductive init_asm_initial_state (q: query li_wp) : option int -> Prop :=
    | init_asm_initial_state_intro: init_asm_initial_state q None.
    Inductive init_asm_at_external: option int -> query li_asm -> Prop :=
    | init_asm_at_external_intro m rs f main:
      init_mem se sk = Some m ->
      AST.prog_main prog = Some main ->
      (prog_defmap prog) ! main = Some (Gfun f) ->
      Genv.find_funct ge rs#PC = Some f ->
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
    intros H. assert (Hsk: erase_program p = erase_program tp). admit.
    constructor. econstructor. apply Hsk.
    intros. reflexivity.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta. destruct H0.
    eapply forward_simulation_step with (match_states := eq).
    - intros. inv H0. inv H2.
      eexists; split; eauto. constructor.
    - intros. inv H2. exists r1. split; constructor.
    - intros. inv H2.
      eexists _, ((Pregmap.init Vundef)#PC <- vf, m).
      repeat apply conj.
      + admit.
      + unfold cc_compcert.
        (* cklr *)
        instantiate (1 := (se1, existT _ 0%nat _, _)).
        exists (cq vf main_sig [] m). split.
        { reflexivity. }
        (* inv wt_c *)
        instantiate (1 := (se1, (se1, main_sig), _)).
        exists (cq vf main_sig [] m). split.
        { repeat constructor. }
        (* lessdef_c *)
        instantiate (1 := (se1, tt, _)).
        exists (cq vf main_sig [] m). split.
        { repeat constructor. }
        (* cc_c_locset *)
        instantiate (1 := (se1, main_sig, _)).
        eexists (Conventions.lq vf main_sig (CallConv.make_locset (Mach.Regmap.init Vundef) m Vundef) m). split.
        { constructor. unfold Conventions1.loc_arguments. cbn.
          destruct Archi.win64; reflexivity. }
        (* cc_locset_mach *)
        instantiate (1 := (se1, CallConv.lmw main_sig (Mach.Regmap.init Vundef) m Vundef, _)).
        eexists (Mach.mq vf Vundef Vundef (Mach.Regmap.init Vundef) m). split.
        { repeat constructor. red.
          unfold Conventions.size_arguments. cbn.
          destruct Archi.win64; reflexivity. }
        (* cc_mach_asm *)
        instantiate (1 := (se1, ((Pregmap.init Vundef)#PC <- vf, Mem.nextblock m), _)).
        eexists ((Pregmap.init Vundef)#PC <- vf, m). split.
        {
          admit.
        }
        (* cc_asm vainj *)
        instantiate (1 := (se1, Inject.injw inject_id _ _)).
        repeat apply conj.
        * cbn. admit.
        * admit.
        * cbn. admit.
      + cbn. repeat apply conj; eauto. constructor. eauto.
        constructor. cbn. admit. admit. admit.
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
        inv Hr. specialize (H7 RAX). rewrite <- H20 in H7.
        destruct H2. cbn in H10. cbn in H7. inv H7.
        constructor. easy.
    - easy.
    - easy.
  Admitted.

End INIT_C_ASM.

Definition with_ (liA liB: language_interface): language_interface :=
  {|
    query := sum (query liA) (query liB);
    reply := sum (reply liA) (reply liB);
    entry := fun q => match q with
                  | inl qA => entry qA
                  | inr qB => entry qB
                  end;
  |}.
Infix "+" := with_ (at level 50, left associativity).

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

Section SYS.
  Context (prog: program).
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

    Search int64.

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
  Definition sys_c: semantics (li_sys + li_sys) li_c :=
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

Require Import CategoricalComp.

Definition load_c (prog: program) : semantics (li_sys + li_sys) li_wp :=
  let sk := AST.erase_program prog in
  comp_semantics' (init_c prog)
    (comp_semantics' (semantics1 prog) (sys_c prog) sk) sk.

Definition secret_c : semantics (li_sys + li_sys) li_wp := load_c secret_program.

Section SECRET_SPEC.

  Variant secret_state :=
    | secret1 | secret2 | secret3 | secret4.

  Inductive secret_spec_initial_state: query li_wp -> secret_state -> Prop :=
  | secret_spec_initial_state_intro q: secret_spec_initial_state q secret1.
  Inductive secret_spec_at_external: secret_state -> query (li_sys + li_sys) -> Prop :=
  | secret_spec_at_external_intro bytes:
    bytes = urbby_bytes ->
    secret_spec_at_external secret2 (inr (write_query bytes)).
  Inductive secret_spec_after_external: secret_state -> reply (li_sys + li_sys) -> secret_state -> Prop :=
  | secret_spec_after_external_intro n:
    secret_spec_after_external secret2 (inr (write_reply n)) secret3.
  Inductive secret_spec_final_state: secret_state -> reply li_wp -> Prop :=
  | secret_spec_final_state_intro: secret_spec_final_state secret4 Int.zero.
  Inductive secret_step : secret_state -> trace -> secret_state -> Prop :=
  | secret_step1: secret_step secret1 E0 secret2
  | secret_step2: secret_step secret3 E0 secret4.

  Definition secret_spec: semantics (li_sys + li_sys) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ := secret_step;
          Smallstep.initial_state := secret_spec_initial_state;
          Smallstep.at_external := secret_spec_at_external;
          Smallstep.after_external := secret_spec_after_external;
          Smallstep.final_state := secret_spec_final_state;
          Smallstep.globalenv := tt;

        |};
      skel := AST.erase_program secret_program;
      footprint := AST.footprint_of_program secret_program;
    |}.

End SECRET_SPEC.

Ltac one_step := eapply star_left with (t1 := E0) (t2 := E0); [ | | reflexivity ].

Require Import Lia.

Ltac ptree_tac :=
  cbn -[PTree.get];
  lazymatch goal with
  | [ |- PTree.get ?x (PTree.set ?x _ _) = _ ] =>
      rewrite PTree.gss; reflexivity
  | [ |- PTree.get ?x (PTree.set ?y _ _) = _ ] =>
      rewrite PTree.gso by (unfold x, y; lia); eauto; ptree_tac
  end.

Ltac solve_ptree := solve [ eauto | ptree_tac ].

Ltac crush_eval_expr :=
  cbn;
  lazymatch goal with
  | [ |- eval_expr _ _ _ _ (Etempvar _ _) _ ] => apply eval_Etempvar; reflexivity
  | [ |- eval_expr _ _ _ _ (Econst_int _ _) _ ] => apply eval_Econst_int
  | [ |- eval_expr _ _ _ _ (Econst_long _ _) _ ] => apply eval_Econst_long
  | [ |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ ] => eapply eval_Ebinop
  | [ |- eval_expr _ _ _ _ (Evar _ _) _ ] => eapply eval_Elvalue
  | [ |- eval_expr _ _ _ _ (Ederef _ _) _ ] => eapply eval_Elvalue
  | [ |- eval_expr _ _ _ _ (Eaddrof _ _) _ ] => eapply eval_Eaddrof
  | [ |- eval_expr _ _ _ _ (Esizeof _ _) _ ] => eapply eval_Esizeof
  end.
Ltac crush_eval_lvalue :=
  cbn;
  lazymatch goal with
  | [ |- eval_lvalue _ _ _ _ (Evar _ _) _ _ _ ] =>
      solve [ apply eval_Evar_local; reflexivity
            | apply eval_Evar_global; [ reflexivity | eassumption ] ]
  | _ => constructor
  end.
Ltac crush_deref :=
  cbn;
  lazymatch goal with
  | [ |- deref_loc (Tarray _ _ _) _ _ _ _ _] => eapply deref_loc_reference; reflexivity
  | [ |- deref_loc (Tfunction _ _ _) _ _ _ _ _] => eapply deref_loc_reference; reflexivity
  | [ |- deref_loc (Tint _ _ _) _ _ _ _ _] => eapply deref_loc_value; [ reflexivity | ]
  end.

Ltac crush_expr :=
  repeat (cbn;
    match goal with
    | [ |- eval_expr _ _ _ _ _ _ ] => crush_eval_expr
    | [ |- eval_lvalue _ _ _ _ _ _ _ _ ] => crush_eval_lvalue
    | [ |- eval_exprlist _ _ _ _ _ _ _ ] => econstructor
    | [ |- deref_loc _ _ _ _ _ _ ] => crush_deref
    | [ |- Cop.sem_binary_operation _ _ _ _ _ _ _ = Some _] => try reflexivity
    | [ |- Cop.sem_cast _ ?ty ?ty _ = Some _ ] =>
        apply Cop.cast_val_casted; eauto
    | [ |- assign_loc _ (Tint _ _ _) _ _ _ _ _ _ ] =>
        eapply assign_loc_value; [ reflexivity | ]
    | _ => try solve [ easy | eassumption ]
    end).

Ltac prove_norepet H :=
  match type of H with
  | False => inversion H
  | (?a = ?b) \/ _ =>
      destruct H as [H|H]; [inversion H|prove_norepet H]
  end.

Ltac solve_list_norepet :=
  simpl;
  match goal with
  | |- list_norepet nil =>  apply list_norepet_nil
  | |- list_norepet (?x :: ?l) =>
      apply list_norepet_cons;
      [simpl; let H := fresh "H" in intro H; prove_norepet H |solve_list_norepet]
  end.
Ltac destruct_or H :=
  match type of H with
  | _ \/ _ => destruct H as [H|H]; [ |destruct_or H]
  | _ => idtac
  end.

Ltac solve_list_disjoint :=
  simpl; unfold list_disjoint; simpl; red;
  let x := fresh "x" in
  let y := fresh "y" in
  let Lx := fresh "Lx" in
  let Ly := fresh "Ly" in
  let xyEq := fresh "xyEq" in
  intros x y Lx Ly xyEq; try rewrite xyEq in *; clear xyEq;
  destruct_or Lx; destruct_or Ly; subst; try solve [inversion Lx]; try solve [inversion Ly].

Ltac crush_step := cbn;
  match goal with
  | [ |- Step _ (Callstate _ _ _ _) _ _ ] =>
      eapply step_internal_function;
      [ eauto | econstructor; cbn
        (* [ solve_list_norepet *)
        (* | solve_list_norepet *)
        (* | solve_list_disjoint *)
        (* | repeat (econstructor; simpl; auto) *)
        (* | reflexivity | eauto ] *) ]
  | [ |- Step _ (State _ (Ssequence _ _) _ _ _ _) _ _ ] => apply step_seq
  | [ |- Step _ (State _ (Sset _ _) _ _ _ _) _ _ ] => apply step_set
  | [ |- Step _ (State _ (Scall _ _ _) _ _ _ _) _ _ ] => eapply step_call
  | [ |- Step _ (Returnstate _ _ _) _ _ ] => eapply step_returnstate
  | [ |- Step _ (State _ Sskip (Kseq _ _) _ _ _) _ _ ] => apply step_skip_seq
  | [ |- Step _ (State _ (Sassign _ _) _ _ _ _) _ _ ] => eapply step_assign
  | [ |- Step _ (State _ (Sreturn None) _ _ _ _) _ _ ] => eapply step_return_0
  | [ |- Step _ (State _ (Sreturn (Some _)) _ _ _ _) _ _ ] => eapply step_return_1
  | [ |- Step _ (State _ (Sloop _ _) _ _ _ _) _ _ ] => eapply step_loop
  | [ |- Step _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ ] => eapply step_ifthenelse
  | [ |- Step _ (State _ Sbreak _ _ _ _) _ _ ] => eapply step_break_loop1
  | [ |- Step _ (State _ ?s _ _ _ _) _ _ ] => is_const s; unfold s; crush_step
  end.

Lemma genv_funct_symbol se id b f (p: program):
  Genv.find_symbol se id = Some b ->
  (prog_defmap p) ! id = Some (Gfun f) ->
  Genv.find_funct (globalenv se p) (Vptr b Ptrofs.zero) = Some f.
Proof.
  intros H1 H2.
  unfold Genv.find_funct, Genv.find_funct_ptr.
  destruct Ptrofs.eq_dec; try congruence.
  apply Genv.find_invert_symbol in H1. cbn.
  rewrite Genv.find_def_spec. rewrite H1.
  rewrite H2. reflexivity.
Qed.

Require Example.

Section SECRET_FSIM.

  Notation L1 := (comp_semantics' (semantics1 secret_program) (sys_c secret_program) (erase_program secret_program)).
  Opaque semantics1.

  Inductive secret_match_state (se: Genv.symtbl): secret_state -> Smallstep.state secret_c -> Prop :=
  | secret_match_state1:
    secret_match_state se secret1 (st1 (init_c secret_program) L1 None)
  | secret_match_state2 vf m args:
    secret_match_state se secret2
      (st2 (init_c secret_program) L1 None
         (st2 (semantics1 secret_program) (sys_c secret_program)
         (Callstate vf args (Kcall None secret_main empty_env (PTree.empty val) (Kseq (Sreturn (Some (Econst_int (Int.repr 0) tint))) Kstop)) m)
         (sys_write_query urbby_bytes m)))
  | secret_match_state3 vf n m args:
    secret_match_state se secret3
      (st2 (init_c secret_program) L1 None
         (st2 (semantics1 secret_program) (sys_c secret_program)
         (Callstate vf args (Kcall None secret_main empty_env (PTree.empty val) (Kseq (Sreturn (Some (Econst_int (Int.repr 0) tint))) Kstop)) m)
         (sys_write_reply n m)))
  | secret_match_state4:
    secret_match_state se secret4 (st1 (init_c secret_program) L1 (Some Int.zero)).

  Lemma secret_prog_defmap_main:
    (prog_defmap secret_program) ! secret_main_id =
      Some (Gfun (Internal secret_main)).
  Proof. reflexivity. Qed.

  Lemma secret_prog_defmap_write:
    (prog_defmap secret_program) ! secret_write_id = Some (Gfun write).
  Proof. reflexivity. Qed.

  Lemma secret_prog_defmap_msg:
    (prog_defmap secret_program) ! secret_msg_id = Some (Gvar msg_globvar).
  Proof. reflexivity. Qed.

  Import Ptrofs.

  Lemma secret_init_mem se:
    Genv.valid_for (erase_program secret_program) se ->
    exists m, init_mem se (erase_program secret_program) = Some m /\
           (forall b, Genv.find_symbol se secret_msg_id = Some b ->
                 Mem.loadbytes m b (unsigned zero) 5 = Some (map Byte urbby_bytes)).
  Proof.
    intros Hvalid.
    edestruct init_mem_exists with
      (p := (erase_program secret_program)) as [m Hm]; eauto.
    - split.
      + cbn in H. destruct_or H; inv H. cbn.
        repeat apply conj; solve [ easy | apply Z.divide_1_l ].
      + cbn in H. destruct_or H; inv H. cbn. intros.
        destruct_or H; inv H.
    - exists m. split; eauto. intros b Hb.
      unfold init_mem in Hm.
      Opaque Genv.store_init_data_list.
      cbn in Hm.
      Ltac destruct_match :=
        match goal with
        | [ H: context [ match ?x with | Some _ => _ | None => _ end ] |- _ ] =>
            let H' := fresh "H" in destruct x eqn:H'; [ | inv H ]
        end.
      repeat (destruct_match; eprod_crush).
      inv Hb. inv Hm.
      eapply (@Genv.store_init_data_list_loadbytes se b msg_il) in H5.
      + erewrite Mem.loadbytes_drop; eauto.
        right. right. right. constructor.
      + eapply Genv.store_zeros_loadbytes. eauto.
  Qed.

  Lemma main_block se:
    Genv.valid_for (AST.erase_program secret_program) se ->
    exists b, Genv.find_symbol (globalenv se secret_program) secret_main_id = Some b /\
           Genv.find_funct (globalenv se secret_program) (Vptr b zero) = Some (Internal secret_main).
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_main).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma write_block se:
    Genv.valid_for (AST.erase_program secret_program) se ->
    exists b, Genv.find_symbol (globalenv se secret_program) secret_write_id = Some b /\
           Genv.find_funct (globalenv se secret_program) (Vptr b zero) = Some write.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_write).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma msg_block se:
    Genv.valid_for (AST.erase_program secret_program) se ->
    exists b, Genv.find_symbol (globalenv se secret_program) secret_msg_id = Some b.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_msg).
    destruct H as (b & Hb1 & Hb2); eauto.
  Qed.

  Lemma secret_fsim: forward_simulation 1 1 secret_spec secret_c.
  Proof.
    constructor. econstructor. reflexivity. cbn.
    { intros; split; intros.
      - right. left. apply H.
      - destruct_or H; easy. }
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    destruct H.
    eapply forward_simulation_plus with
      (match_states := fun s1 s2 => secret_match_state se1 s1 s2).
    - intros. inv H1. inv H.
      exists (st1 (init_c secret_program) L1 None).
      split; repeat constructor.
    - intros. inv H1. inv H. cbn in *. exists Int.zero.
      split; repeat constructor.
    - intros. inv H1. inv H. exists tt, (inr (write_query urbby_bytes)).
      repeat apply conj; try repeat constructor.
      intros. inv H. inv H1.
      eexists. split. 2: constructor.
      repeat constructor.
    - intros. inv H; inv H1.
      + edestruct secret_init_mem as [m [Hm1 Hm2]]; eauto.
        edestruct main_block as [b [Hb1 Hb2]]; eauto.
        edestruct write_block as [b1 [Hb3 Hb4]]; eauto.
        edestruct msg_block as [b2 Hb5]; eauto.
        eexists. split. 2: constructor.
        eapply plus_left. (* init calls secret.c *)
        {
          eapply step_push.
          - econstructor; try reflexivity; eauto.
          - constructor. econstructor; eauto.
            + constructor.
            + cbn. apply init_mem_nextblock in Hm1.
              rewrite Hm1. reflexivity.
        }
        2: { instantiate (1 := E0). reflexivity. }
        one_step. (* internal step of secret.c *)
        { eapply step2. eapply step1. crush_step; try solve [ constructor | easy ].
          eapply init_mem_alloc_flag. apply Hm1. }
        one_step. (* internal step of secret.c *)
        { eapply step2. eapply step1. crush_step. }
        one_step. (* internal step of secret.c *)
        { eapply step2. eapply step1. crush_step; crush_expr.
          unfold rw_type. crush_deref. }
        one_step. (* secret.c calls sys *)
        { eapply step2. eapply step_push.
          - econstructor. eauto.
          - eapply sys_c_initial_state_write; eauto. }
        eapply star_refl.
      + eexists. split. 2: constructor.
        eapply plus_left. (* sys returns to secret.c *)
        { eapply step2. eapply step_pop; econstructor. }
        2: { instantiate (1 := E0). reflexivity. }
        one_step. (* internal step of secret.c *)
        { eapply step2. eapply step1. crush_step. }
        one_step. (* internal step of secret.c *)
        { eapply step2. eapply step1. crush_step. }
        one_step. (* internal step of secret.c *)
        { eapply step2. eapply step1. crush_step; crush_expr. }
        one_step. (* secret.c returns to init *)
        { eapply step_pop; repeat constructor. }
        eapply star_refl.
    - easy.
  Qed.

End SECRET_FSIM.

Definition rot13_rot13_id: positive := 1.
Definition rot13_main_id: positive := 2.
Definition rot13_read_id: positive := 3.
Definition rot13_write_id: positive := 4.
Definition rot13_rot13_c_id: positive := 5.
Definition rot13_main_buf_id: positive := 6.
Definition rot13_main_n_id: positive := 7.
Definition rot13_main_i_id: positive := 8.
Definition rot13_main_t_id: positive := 9.

Require Import Cop.

Definition rot13_rot13_body : statement :=
  let c := Evar rot13_rot13_c_id tchar in
  (* let a := Econst_int (Int.repr 65) tint in *)
  (* let z := Econst_int (Int.repr 91) tint in *)
  let m := Econst_int (Int.repr 109) tint in
  let thirteen := Econst_int (Int.repr 13) tint in
  (* Sifthenelse *)
  (*   (* if c >= 'a' && c <= 'z' *) *)
  (*   (Ebinop Oand (Ebinop Oge c a tint) (Ebinop Ole c z tint) tint) *)
  (*   ( *)
      (* if c <= 'm' *)
      Sifthenelse (Ebinop Ole c m tint)
        (* return c + 13 *)
        (Sreturn (Some (Ebinop Osub c thirteen tint)))
        (* return c - 13 *)
        (Sreturn (Some (Ebinop Oadd c thirteen tint))).
    (* ) *)
    (* (* return c *) *)
    (* (Sreturn (Some c)). *)

Definition rot13_rot13 : function :=
  {|
    fn_return := tchar;
    fn_callconv := cc_default;
    fn_params := [ (rot13_rot13_c_id, tchar) ];
    fn_temps := [];
    fn_vars := [];
    fn_body := rot13_rot13_body;
  |}.

Definition rot13_type := Tfunction (Tcons tchar Tnil) tchar cc_default.

Program Definition rot13_main_body : statement :=
  let zero := Econst_int (Int.repr 0) tint in
  let one := Econst_int (Int.repr 1) tint in
  let n := Etempvar rot13_main_n_id tint in
  let i := Etempvar rot13_main_i_id tint in
  let t := Etempvar rot13_main_t_id tint in
  let buf := Evar rot13_main_buf_id (tarray tchar 100) in
  let buf_i := Ederef (Ebinop Oadd buf i tchar) tchar in
  let for_loop :=
    (* for i = 0; i < n; i++ *)
    Sfor (Sset rot13_main_i_id zero) (Ebinop Olt i n tint)
      (Ssequence
         (* t = rot13(buf[i]) *)
         (Scall (Some rot13_main_t_id) (Evar rot13_rot13_id rot13_type) [ buf_i ])
         (* buf[i] = t *)
         (Sassign buf_i t))
      (* i++ *)
      (Sset rot13_main_i_id (Ebinop Oadd i one tint))
  in
  let read_buf :=
    (* n = read(0, buf, sizeof buf) *)
    Scall (Some rot13_main_n_id) (Evar rot13_read_id rw_type) [ zero; buf; Esizeof (tarray tchar 100) tlong ]
  in
  let write_buf :=
    (* write(1, buf, n) *)
    Scall None (Evar rot13_write_id rw_type) [ one; buf; n ]
  in
  Ssequence read_buf (Ssequence for_loop (Ssequence write_buf (Sreturn (Some zero)))).

Definition rot13_main : function :=
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := [];
    fn_temps := [ (rot13_main_n_id, tint); (rot13_main_i_id, tint); (rot13_main_t_id, tint) ];
    fn_vars := [ (rot13_main_buf_id, tarray tchar 100) ];
    fn_body := rot13_main_body;
  |}.

Program Definition rot13_program : Clight.program :=
  {|
    prog_defs := [(rot13_rot13_id, Gfun (Internal rot13_rot13));
                  (rot13_main_id, Gfun (Internal rot13_main));
                  (rot13_read_id, Gfun read);
                  (rot13_write_id, Gfun write)];
    prog_public := [ rot13_main_id ];
    prog_main := Some rot13_main_id;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.

Definition rot13_c : semantics (li_sys + li_sys) li_wp := load_c rot13_program.

Section ROT13_SPEC.

  Variant rot13_state :=
    | rot13_read0 | rot13_write0 (bytes: list byte) | rot13_ret0
    | rot13_read | rot13_write (bytes: list byte) | rot13_ret
    (* The first i bytes have been decoded. These intermediate steps correspond
       to internal steps in the loop of rot13.c, so that we don't have to do
       induction proof on the Clight loops *)
    | rot13_writei (bytes: list byte) (i: Z).

  Inductive rot13_spec_initial_state: query li_wp -> rot13_state -> Prop :=
  | rot13_spec_initial_state_intro q: rot13_spec_initial_state q rot13_read0.
  Inductive rot13_spec_at_external: rot13_state -> query (li_sys + li_sys) -> Prop :=
  | rot13_spec_at_external_read:
    rot13_spec_at_external rot13_read (inl (read_query (Int64.repr 100)))
  | rot13_spec_at_external_write bytes:
    rot13_spec_at_external (rot13_write bytes) (inr (write_query bytes)).
  Inductive rot13_spec_after_external: rot13_state -> reply (li_sys + li_sys) -> rot13_state -> Prop :=
  | rot13_spec_after_external_read bytes:
    Z.of_nat (length bytes) <= 100 ->
    rot13_spec_after_external rot13_read (inl (read_reply bytes)) (rot13_write0 bytes)
  | rot13_spec_after_external_write bytes n:
    rot13_spec_after_external (rot13_write bytes) (inr (write_reply n)) rot13_ret0.
  Inductive rot13_spec_final_state: rot13_state -> reply li_wp -> Prop :=
  | rot13_spec_final_state_intro: rot13_spec_final_state rot13_ret Int.zero.
  Inductive rot13_spec_step: rot13_state -> trace -> rot13_state -> Prop :=
  | rot13_spec_step1: rot13_spec_step rot13_read0 E0 rot13_read
  | rot13_spec_step2 bytes:
    rot13_spec_step (rot13_write0 bytes) E0 (rot13_writei bytes 0)
  | rot13_spec_stepi bytes bytes' i:
    i < Z.of_nat (length bytes) ->
    bytes' = rot13_bytes_i bytes i ->
    rot13_spec_step (rot13_writei bytes i) E0 (rot13_writei bytes' (i + 1))
  | rot13_spec_step3 bytes i:
    i = Z.of_nat (length bytes) ->
    rot13_spec_step (rot13_writei bytes i) E0 (rot13_write bytes)
  | rot13_spec_step4: rot13_spec_step rot13_ret0 E0 rot13_ret.

  Definition rot13_spec: semantics (li_sys + li_sys) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ := rot13_spec_step;
          Smallstep.initial_state := rot13_spec_initial_state;
          Smallstep.at_external := rot13_spec_at_external;
          Smallstep.after_external := rot13_spec_after_external;
          Smallstep.final_state := rot13_spec_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := AST.erase_program rot13_program;
      footprint := AST.footprint_of_program rot13_program;
    |}.

End ROT13_SPEC.

Section ROT13_FSIM.

  Notation L1 := (comp_semantics' (semantics1 rot13_program) (sys_c rot13_program) (erase_program rot13_program)).
  Opaque semantics1.
  Import Ptrofs.

  Lemma rot13_prog_defmap_main:
    (prog_defmap rot13_program) ! rot13_main_id =
      Some (Gfun (Internal rot13_main)).
  Proof. reflexivity. Qed.

  Lemma rot13_prog_defmap_read:
    (prog_defmap rot13_program) ! rot13_read_id = Some (Gfun read).
  Proof. reflexivity. Qed.

  Lemma rot13_prog_defmap_write:
    (prog_defmap rot13_program) ! rot13_write_id = Some (Gfun write).
  Proof. reflexivity. Qed.

  Lemma rot13_prog_defmap_rot13:
    (prog_defmap rot13_program) ! rot13_rot13_id = Some (Gfun (Internal rot13_rot13)).
  Proof. reflexivity. Qed.

  Lemma rot13_main_block se:
    Genv.valid_for (AST.erase_program rot13_program) se ->
    exists b, Genv.find_symbol (globalenv se rot13_program) rot13_main_id = Some b /\
           Genv.find_funct (globalenv se rot13_program) (Vptr b zero) = Some (Internal rot13_main).
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H rot13_prog_defmap_main).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma rot13_read_block se:
    Genv.valid_for (AST.erase_program rot13_program) se ->
    exists b, Genv.find_symbol (globalenv se rot13_program) rot13_read_id = Some b /\
           Genv.find_funct (globalenv se rot13_program) (Vptr b zero) = Some read.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H rot13_prog_defmap_read).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma rot13_write_block se:
    Genv.valid_for (AST.erase_program rot13_program) se ->
    exists b, Genv.find_symbol (globalenv se rot13_program) rot13_write_id = Some b /\
           Genv.find_funct (globalenv se rot13_program) (Vptr b zero) = Some write.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H rot13_prog_defmap_write).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma rot13_rot13_block se:
    Genv.valid_for (AST.erase_program rot13_program) se ->
    exists b, Genv.find_symbol (globalenv se rot13_program) rot13_rot13_id = Some b /\
           Genv.find_funct (globalenv se rot13_program) (Vptr b zero) = Some (Internal rot13_rot13).
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H rot13_prog_defmap_rot13).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma rot13_init_mem se:
    Genv.valid_for (erase_program rot13_program) se ->
    exists m, init_mem se (erase_program rot13_program) = Some m.
  Proof.
    intros Hvalid. eapply init_mem_exists; eauto.
    split; cbn in H; destruct_or H; inv H.
  Qed.

  Definition kont1 buf_block :=
    (Kcall (Some rot13_main_n_id) rot13_main (PTree.set rot13_main_buf_id (buf_block, Tarray tchar 100 noattr) empty_env)
       (PTree.set rot13_main_n_id Vundef
          (PTree.set rot13_main_i_id Vundef (PTree.set rot13_main_t_id Vundef (PTree.empty val))))
       (Kseq
          (Ssequence
             (Sfor (Sset rot13_main_i_id (Econst_int (Int.repr 0) tint))
                (Ebinop Olt (Etempvar rot13_main_i_id tint) (Etempvar rot13_main_n_id tint) tint)
                (Ssequence
                   (Scall (Some rot13_main_t_id) (Evar rot13_rot13_id rot13_type)
                      [Ederef
                         (Ebinop Oadd (Evar rot13_main_buf_id (Tarray tchar 100 noattr)) (Etempvar rot13_main_i_id tint)
                            tchar) tchar])
                   (Sassign
                      (Ederef
                         (Ebinop Oadd (Evar rot13_main_buf_id (Tarray tchar 100 noattr)) (Etempvar rot13_main_i_id tint)
                            tchar) tchar) (Etempvar rot13_main_t_id tint)))
                (Sset rot13_main_i_id (Ebinop Oadd (Etempvar rot13_main_i_id tint) (Econst_int (Int.repr 1) tint) tint)))
             (Ssequence
                (Scall None (Evar rot13_write_id rw_type)
                   [Econst_int (Int.repr 1) tint; Evar rot13_main_buf_id (Tarray tchar 100 noattr);
                    Etempvar rot13_main_n_id tint]) (Sreturn (Some (Econst_int (Int.repr 0) tint))))) Kstop)).

  Definition state_i m len buf_block i :=
    State rot13_main
      (Sloop
         (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar rot13_main_i_id tint) (Etempvar rot13_main_n_id tint) tint) Sskip Sbreak)
            (Ssequence
               (Scall (Some rot13_main_t_id) (Evar rot13_rot13_id rot13_type)
                  [Ederef (Ebinop Oadd (Evar rot13_main_buf_id (Tarray tchar 100 noattr)) (Etempvar rot13_main_i_id tint) tchar)
                     tchar])
               (Sassign
                  (Ederef (Ebinop Oadd (Evar rot13_main_buf_id (Tarray tchar 100 noattr)) (Etempvar rot13_main_i_id tint) tchar)
                     tchar) (Etempvar rot13_main_t_id tint)))
         )
         (Sset rot13_main_i_id (Ebinop Oadd (Etempvar rot13_main_i_id tint) (Econst_int (Int.repr 1) tint) tint))
      )
      (Kseq
         (Ssequence
            (Scall None (Evar rot13_write_id rw_type)
               [Econst_int (Int.repr 1) tint; Evar rot13_main_buf_id (Tarray tchar 100 noattr); Etempvar rot13_main_n_id tint])
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))) Kstop)
      (PTree.set rot13_main_buf_id (buf_block, Tarray tchar 100 noattr) empty_env)
      (PTree.set rot13_main_i_id (Vint (Int.repr i))
         (PTree.set rot13_main_n_id (Vint (Int.repr len))
            (PTree.set rot13_main_i_id Vundef (PTree.set rot13_main_t_id Vundef (PTree.empty val))))) m.

  Definition sys_st s1 s2 :=
    st2 (init_c rot13_program) L1 None
         (st2 (semantics1 rot13_program) (sys_c rot13_program) s1 s2).

  Definition c_st s :=
    st2 (init_c rot13_program) L1 None
         (st1 (semantics1 rot13_program) (sys_c rot13_program) s).

  Inductive rot13_match_state (se: Genv.symtbl): rot13_state -> Smallstep.state rot13_c -> Prop :=
  | rot13_match_state1:
    rot13_match_state se rot13_read0 (st1 (init_c rot13_program) L1 None)
  | rot13_match_state2 vf m args kont buf_block:
    kont = kont1 buf_block ->
    Mem.range_perm m buf_block 0 100 Cur Writable ->
    rot13_match_state se rot13_read
      (sys_st (Callstate vf args kont m) (sys_read_query (Int64.repr 100) buf_block Ptrofs.zero m))
  | rot13_match_state3 vf m args kont bytes buf_block:
    kont = kont1 buf_block ->
    Mem.range_perm m buf_block 0 (Z.of_nat (Datatypes.length bytes)) Cur Writable ->
    rot13_match_state se (rot13_write0 bytes)
      (sys_st (Callstate vf args kont m) (sys_read_reply bytes buf_block Ptrofs.zero m))
  | rot13_match_state_i m bytes i buf_block len:
    len = Z.of_nat (length bytes) -> i <= len ->
    Mem.loadbytes m buf_block 0 len = Some (map Byte bytes) ->
    rot13_match_state se (rot13_writei bytes i)
      (c_st (state_i m len buf_block i))
  | rot13_match_state4 vf m args kont bytes:
    rot13_match_state se (rot13_write bytes)
      (st2 (init_c rot13_program) L1 None
         (st2 (semantics1 rot13_program) (sys_c rot13_program)
         (Callstate vf args kont m)
         (sys_write_query bytes m)))
  | rot13_match_state5 vf m args kont n:
    rot13_match_state se rot13_ret0
      (st2 (init_c rot13_program) L1 None
         (st2 (semantics1 rot13_program) (sys_c rot13_program)
         (Callstate vf args kont m)
         (sys_write_reply n m)))
  | rot13_match_state6:
    rot13_match_state se rot13_ret (st1 (init_c rot13_program) L1 (Some Int.zero)).

  Lemma rot13_fsim: forward_simulation 1 1 rot13_spec rot13_c.
  Proof.
    constructor. econstructor. reflexivity. cbn.
    { intros; split; intros.
      - right. left. apply H.
      - destruct_or H; easy. }
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    destruct H.
    eapply forward_simulation_plus with
      (match_states := fun s1 s2 => rot13_match_state se1 s1 s2).
    - intros. inv H1. inv H.
      exists (st1 (init_c rot13_program) L1 None).
      split; repeat constructor.
    - intros. inv H1. inv H. cbn in *. exists Int.zero.
      split; repeat constructor.
    - intros. inv H; inv H1.
      + exists tt, (inl (read_query (Int64.repr 100))).
        repeat apply conj; try repeat constructor.
        intros. inv H. inv H1.
        eexists. split. 2: econstructor; eauto. repeat constructor; eauto.
        (* range_perm *)
        intros p Hperm. apply H3. lia.
      + exists tt, (inr (write_query bytes)).
        repeat apply conj; try repeat constructor.
        intros. inv H. inv H1.
        eexists. split. 2: constructor. repeat constructor.
    - intros. inv H; inv H1.
      (* transition to the call to read *)
      + edestruct rot13_init_mem as [m Hm]; eauto.
        edestruct rot13_main_block as [b [Hb1 Hb2]]; eauto.
        edestruct rot13_read_block as [b1 [Hb3 Hb4]]; eauto.
        exploit init_mem_alloc_flag; eauto. intros Hflag.
        edestruct (@Mem.alloc_succeed m 0 100); eauto. destruct x as (m1 & b2).
        eexists. split.
        2: { econstructor; eauto.
             (* range_perm *)
             intros p Hperm.
             eapply Mem.perm_alloc_2 in e; eauto.
             eauto with mem. }
        eapply plus_left. (* init calls rot13.c *)
        {
          eapply step_push.
          - econstructor; try reflexivity; eauto.
          - constructor. econstructor; eauto.
            + constructor.
            + cbn. apply init_mem_nextblock in Hm.
              rewrite Hm. reflexivity.
        }
        2: { instantiate (1 := E0). reflexivity. }
        one_step. (* internal step of rot13.c *)
        { eapply step2. eapply step1; crush_step; try solve [ constructor | easy ].
          - solve_list_norepet.
          - repeat econstructor. eauto. }
        one_step. (* internal step of rot13.c *)
        { eapply step2. eapply step1; crush_step. }
        one_step. (* internal step of rot13.c *)
        { eapply step2. eapply step1; crush_step; crush_expr.
          - unfold rw_type. crush_deref.
          - constructor. }
        one_step. (* rot13.c calls sys *)
        {
          eapply step2. eapply step_push.
          - econstructor. eauto.
          - eapply sys_c_initial_state_read; eauto. reflexivity.
        }
        eapply star_refl.
      (* enter the loop *)
      + edestruct Mem.range_perm_storebytes with (ofs := 0) (bytes := map Byte bytes) as (m1 & Hm1).
        (* range_perm *)
        intros p Hperm. apply H3. rewrite map_length in Hperm. eauto.
        eexists. split.
        eapply plus_left. (* sys returns to rot13.c, and storebytes "urbby" *)
        { eapply step2. eapply step_pop; econstructor; eauto. }
        2: { instantiate (1 := E0). reflexivity. }
        one_step. (* internal step of rot13.c: Returnstate -> Sskip *)
        { eapply step2. eapply step1; crush_step. }
        one_step. (* internal step of rot13.c: Sskip *)
        { eapply step2. eapply step1; crush_step. }
        one_step. (* internal step of rot13.c: Ssequence *)
        { eapply step2. eapply step1; crush_step. }
        one_step. (* internal step of rot13.c: Sfor *)
        { eapply step2. eapply step1. unfold Sfor. crush_step. }
        one_step. (* internal step of rot13.c: Sset *)
        { eapply step2. eapply step1; crush_step; crush_expr. }
        one_step. (* internal step of rot13.c: Sskip *)
        { eapply step2. eapply step1; crush_step. }
        rewrite PTree.set2. eapply star_refl.
        { econstructor; eauto; try lia.
          (* loadbytes *)
          apply Mem.loadbytes_storebytes_same in Hm1.
          rewrite map_length in Hm1. apply Hm1. }
      (* looping *)
      + edestruct rot13_rot13_block as [b [Hb1 Hb2]]; eauto.
        edestruct (Mem.alloc_succeed m 0 1) as ((m1 & b1) & Hmb). admit.
        assert (exists m2, Mem.store Mint8unsigned m1 b1 (unsigned zero) (Vint (Int.repr (Byte.unsigned (nth (Z.to_nat i) bytes (Byte.repr 0))))) = Some m2)
                 as (m2 & Hm2). admit.
        assert (exists m3,   Mem.free_list m2
                          (blocks_of_env (Smallstep.globalenv (semantics1 rot13_program se1)) (PTree.set rot13_rot13_c_id (b1, tchar) empty_env)) =
                          Some m3) as (m3 & Hm3). admit.
        eexists. split.
        eapply plus_left. (* internal step of rot13.c: Sloop *)
        { eapply step2. eapply step1. unfold state_i. crush_step. }
        2: { instantiate (1 := E0). reflexivity. }
        one_step. (* internal step of rot13.c: Ssequence *)
        { eapply step2. eapply step1; crush_step. }
        one_step. (* internal step of rot13.c: Sifthenelse *)
        { eapply step2. eapply step1; crush_step; crush_expr.
          instantiate (1 := true).
          destruct Int.ltu eqn: Hltu. cbn. reflexivity.
          exfalso. unfold Int.ltu in Hltu. admit.
        }
        one_step. (* internal step of rot13.c: Sskip *)
        { eapply step2. eapply step1; crush_step. }
        one_step. (* internal step of rot13.c: Ssequence *)
        { eapply step2. eapply step1; crush_step. }
        one_step. (* internal step of rot13.c: Scall *)
        { eapply step2. eapply step1; crush_step; crush_expr.
          - apply deref_loc_reference. reflexivity.
          - replace (unsigned (add zero (mul (repr 1) (of_intu (Int.repr i))))) with i.
            2: admit.
            (* instantiate (1 := decode_val Mint8unsigned [nth (Z.to_nat i) (map Byte bytes) Undef]). *)
            instantiate (1 := Vint (Int.repr (Byte.unsigned (nth (Z.to_nat i) bytes (Byte.repr 0))))).
            admit.
          - constructor. cbn.  admit.
        }
        one_step. (* internal step of rot13.c: call rot13 *)
        { eapply step2. eapply step1; crush_step; crush_expr.
          - solve_list_norepet.
          - econstructor. apply Hmb. constructor.
          - econstructor.
            + reflexivity.
            + eapply assign_loc_value. reflexivity. cbn. apply Hm2.
            + constructor.
          - admit.
        }
        one_step.
        { eapply step2. eapply step1; crush_step.
          - admit.
          - instantiate (1 := true). admit.
        }
        one_step.
        { eapply step2. eapply step1; crush_step; crush_expr.
          - erewrite Mem.load_store_same; eauto.
          - cbn. crush_expr.
          - cbn. reflexivity.
        }
        one_step.
        { eapply step2. eapply step1; crush_step. }
        one_step.
        { eapply step2. eapply step1; crush_step. }

  Admitted.

End ROT13_FSIM.

Definition empty_skel: AST.program unit unit :=
  {|
    AST.prog_defs := [];
    AST.prog_public := [];
    AST.prog_main := None;
  |}.

Section SEQ.

  Variant seq_state := | seq1 | seq2 | ret (n: int).
  Inductive seq_initial_state: query li_wp -> seq_state -> Prop :=
  | seq_initial_state_intro q: seq_initial_state q seq1.
  Inductive seq_at_external: seq_state -> query (li_wp + li_wp) -> Prop :=
  | seq_at_external1: seq_at_external seq1 (inl tt)
  | seq_at_external2: seq_at_external seq2 (inr tt).
  Inductive seq_after_external: seq_state -> reply (li_wp + li_wp) -> seq_state -> Prop :=
  | seq_after_external1 n: seq_after_external seq1 (inl n) seq2
  | seq_after_external2 n: seq_after_external seq2 (inr n) (ret n).
  Inductive seq_final_state: seq_state -> reply li_wp -> Prop :=
  | seq_final_state_intro n: seq_final_state (ret n) n.

  Definition seq: semantics (li_wp + li_wp) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := seq_initial_state;
          Smallstep.at_external := seq_at_external;
          Smallstep.after_external := seq_after_external;
          Smallstep.final_state := seq_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := empty_skel;
      footprint i := False;
    |}.

End SEQ.

Section WITH.
  Context {liA1 liA2 liB1 liB2}
    (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
  Section WITH_SE.
    Context (se: Genv.symtbl).
    Definition with_state := (Smallstep.state L1 + Smallstep.state L2)%type.
    Inductive with_initial_state: query (liB1 + liB2) -> with_state -> Prop :=
    | with_initial_state1 q s:
      Smallstep.initial_state (L1 se) q s ->
      with_initial_state (inl q) (inl s)
    | with_initial_state2 q s:
      Smallstep.initial_state (L2 se) q s ->
      with_initial_state (inr q) (inr s).
    Inductive with_at_external: with_state -> query (liA1 + liA2) -> Prop :=
    | with_at_external1 s q:
      Smallstep.at_external (L1 se) s q ->
      with_at_external (inl s) (inl q)
    | with_at_external2 s q:
      Smallstep.at_external (L2 se) s q ->
      with_at_external (inr s) (inr q).
    Inductive with_after_external: with_state -> reply (liA1 + liA2) -> with_state -> Prop :=
    | with_after_external1 s r s':
      Smallstep.after_external (L1 se) s r s' ->
      with_after_external (inl s) (inl r) (inl s')
    | with_after_external2 s r s':
      Smallstep.after_external (L2 se) s r s' ->
      with_after_external (inr s) (inr r) (inr s').
    Inductive with_final_state: with_state -> reply (liB1 + liB2) -> Prop :=
    | with_final_state1 s r:
      Smallstep.final_state (L1 se) s r ->
      with_final_state (inl s) (inl r)
    | with_final_state2 s r:
      Smallstep.final_state (L2 se) s r ->
      with_final_state (inr s) (inr r).
    Inductive with_step: with_state -> trace -> with_state -> Prop :=
    | with_step1 s1 s1' t:
      Step (L1 se) s1 t s1' -> with_step (inl s1) t (inl s1')
    | with_step2 s2 s2' t:
      Step (L2 se) s2 t s2' -> with_step (inr s2) t (inr s2').

  End WITH_SE.

  Definition with_semantics: semantics (liA1 + liA2) (liB1 + liB2) :=
    {|
      activate se :=
        {|
          Smallstep.step := with_step;
          Smallstep.initial_state := with_initial_state se;
          Smallstep.at_external := with_at_external se;
          Smallstep.after_external := with_after_external se;
          Smallstep.final_state := with_final_state se;
          Smallstep.globalenv := se;
        |};
      skel := empty_skel;
      footprint i := False;
    |}.

End WITH.

Section PIPE.

  Definition pipe_state := list byte.
  Definition pipe_in := (((li_sys + li_sys) + (li_sys + li_sys)) @ pipe_state)%li.
  Definition encap_pipe_in := ((li_sys + li_sys) + (li_sys + li_sys))%li.
  Definition pipe_out := (li_sys + li_sys)%li.
  Variant pipe_internal_state :=
    | pipe1_read_query (n: int) (s: pipe_state)
    | pipe1_read_reply (bytes: list byte) (s: pipe_state)
    | pipe1_write (bytes: list byte) (s: pipe_state)
    | pipe2_read (n: int) (s: pipe_state)
    | pipe2_write_query (bytes: list byte) (s: pipe_state)
    | pipe2_write_reply (n: int) (s: pipe_state).

  Inductive pipe_initial_state: query pipe_in -> pipe_internal_state -> Prop :=
  | pipe_initial_state1 n s:
    pipe_initial_state (inl (inl (read_query n)), s) (pipe1_read_query n s)
  | pipe_initial_state2 bytes s:
    pipe_initial_state (inl (inr (write_query bytes)), s) (pipe1_write bytes s)
  | pipe_initial_state3 n s:
    pipe_initial_state (inr (inl (read_query n)), s) (pipe2_read n s)
  | pipe_initial_state4 bytes s:
    pipe_initial_state (inr (inr (write_query bytes)), s) (pipe2_write_query bytes s).
  Inductive pipe_at_external: pipe_internal_state -> query pipe_out -> Prop :=
  | pipe_at_external1 n s:
    pipe_at_external (pipe1_read_query n s) (inl (read_query n))
  | pipe_at_external2 bytes s:
    pipe_at_external (pipe2_write_query bytes s) (inr (write_query bytes)).
  Inductive pipe_after_external: pipe_internal_state -> reply pipe_out -> pipe_internal_state -> Prop :=
  | pipe_after_external1 bytes n s:
    pipe_after_external (pipe1_read_query n s) (inl (read_reply bytes)) (pipe1_read_reply bytes s)
  | pipe_after_external2 n bytes s:
    pipe_after_external (pipe2_write_query bytes s) (inr (write_reply n)) (pipe2_write_reply n s).
  Inductive pipe_final_state: pipe_internal_state -> reply pipe_in -> Prop :=
  | pipe_final_state1 bytes s:
    pipe_final_state (pipe1_read_reply bytes s) ((inl (inl (read_reply bytes))), s)
  | pipe_final_state2 n bytes s:
    n = Int.repr (Z.of_nat (length bytes)) ->
    pipe_final_state (pipe1_write bytes s) ((inl (inr (write_reply n)), bytes ++ s))
  | pipe_final_state3 n s s' bytes:
    s = bytes ++ s' ->
    n = Int.repr (Z.of_nat (length bytes)) ->
    pipe_final_state (pipe2_read n s) ((inr (inl (read_reply bytes)), s'))
  | pipe_final_state4 n s:
    pipe_final_state (pipe2_write_reply n s) ((inr (inr (write_reply n)), s)).

  Definition pipe_operator: semantics pipe_out pipe_in :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := pipe_initial_state;
          Smallstep.at_external := pipe_at_external;
          Smallstep.after_external := pipe_after_external;
          Smallstep.final_state := pipe_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := empty_skel;
      footprint i := False;
    |}.

  Instance pset_pipe_state : PSet pipe_state :=
    { pset_init _ := [] }.

  Definition encap_pipe_operator: pipe_out +-> encap_pipe_in :=
    {|
      pstate := pipe_state;
      esem := pipe_operator;
    |}.

End PIPE.

Definition hello_skel: AST.program unit unit. Admitted.

Definition pipe (L1 L2: semantics (li_sys + li_sys) li_wp) sk: (li_sys + li_sys) +-> li_wp :=
  comp_esem'
    (semantics_embed (comp_semantics' seq (with_semantics L1 L2) sk))
    encap_pipe_operator sk.

Section HELLO_SPEC.

  (* The redundant internal step makes the simulation easier. *)
  Variant hello_state :=
    | hello1 | hello2 | hello3 (n: int) | hello4 (n: int).
  Inductive hello_spec_initial_state: query li_wp -> hello_state -> Prop :=
  | hello_spec_initial_state_intro q: hello_spec_initial_state q hello1.
  Inductive hello_spec_at_external: hello_state -> query (li_sys + li_sys) -> Prop :=
  | hello_spec_at_external_intro bytes:
    bytes = [ Byte.repr 104; Byte.repr 101; Byte.repr 108; Byte.repr 108; Byte.repr 111 ] ->
    hello_spec_at_external hello2 (inr (write_query bytes)).
  Inductive hello_spec_after_external: hello_state -> reply (li_sys + li_sys) -> hello_state -> Prop :=
  | hello_spec_after_external_intro n:
    hello_spec_after_external hello2 (inr (write_reply n)) (hello3 n).
  Inductive hello_spec_final_state: hello_state -> reply li_wp -> Prop :=
  | hello_spec_final_state_intro n: hello_spec_final_state (hello4 n) n.
  Inductive hello_spec_step: hello_state -> trace -> hello_state -> Prop :=
  | hello_spec_step1: hello_spec_step hello1 E0 hello2
  | hello_spec_step2 n: hello_spec_step (hello3 n) E0 (hello4 n).

  Definition hello_spec: semantics (li_sys + li_sys) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ := hello_spec_step;
          Smallstep.initial_state := hello_spec_initial_state;
          Smallstep.at_external := hello_spec_at_external;
          Smallstep.after_external := hello_spec_after_external;
          Smallstep.final_state := hello_spec_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := hello_skel;
      footprint i := False;
    |}.
  Definition encap_hello_spec: li_sys + li_sys +-> li_wp := semantics_embed hello_spec.

End HELLO_SPEC.

Section PIPE_CORRECT.

  Notation L1 :=
        (TensorComp.semantics_map (comp_semantics' seq (with_semantics secret_spec rot13_spec) hello_skel)
           TensorComp.lf (TensorComp.li_iso_inv TensorComp.li_iso_unit) @ pipe_state)%lts.

  Inductive pipe_match_state: hello_state -> Smallstep.state (pipe secret_spec rot13_spec hello_skel) -> Prop :=
  | pipe_match_state1 buf:
    pipe_match_state hello1
      (st1 L1 pipe_operator (st1 seq (with_semantics secret_spec rot13_spec) seq1, buf))
  | pipe_match_state2 buf:
    pipe_match_state hello2
      (st2 L1 pipe_operator
         (st2 seq (with_semantics secret_spec rot13_spec) seq2 (inr (rot13_write hello_bytes)), buf)
         (pipe2_write_query hello_bytes buf))
  | pipe_match_state3 buf n:
    pipe_match_state (hello3 n)
      (st2 L1 pipe_operator
         (st2 seq (with_semantics secret_spec rot13_spec) seq2 (inr (rot13_write hello_bytes)), buf)
         (pipe2_write_reply n buf))
  | pipe_match_state4 n buf:
    pipe_match_state (hello4 n)
      (st1 L1 pipe_operator (st1 seq (with_semantics secret_spec rot13_spec) (ret n), buf)).

  Local Opaque app.

  Lemma pipe_spec_correct: E.forward_simulation &1 &1 encap_hello_spec (pipe secret_spec rot13_spec hello_skel).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
          (ltof _ (fun (_: unit) => 0%nat))
          (fun _se1 _se2 _wb _sa _sb _i s1 s2 => pipe_match_state s1 s2)
          (fun _ _ => True);
          try easy. intros; cbn. firstorder.
    intros. constructor.
    - intros. cbn in *. eprod_crush. inv H4.
      eexists tt, (st1 L1 _ (_, _)). split. repeat constructor; eauto.
      eexists tt, (tt, (tt, (tt, p0))). split; repeat constructor; eauto.
    - intros. cbn in *. eprod_crush. inv H3. inv H2.
      exists (i0, (tt, buf)). split.
      * exists (i0, tt, buf). split; repeat constructor; eauto.
        cbn. exists i0. split; repeat constructor.
      * exists (tt, (tt, (tt, buf))). split; repeat constructor; eauto.
    - intros. cbn in *. eprod_crush. inv H3. unfold id in H5. subst. inv H2.
      exists (inr (write_query hello_bytes)). split.
      * repeat constructor.
      * exists tt, tt. repeat split; eauto.
        destruct H3 as (r' & Hr1 & Hr2). unfold id in Hr1. subst. inv Hr2.
        exists (st2 L1 pipe_operator
             (st2 seq (with_semantics secret_spec rot13_spec) seq2 (inr (rot13_write hello_bytes)), buf)
             (pipe2_write_reply n buf)). split.
        -- exists (inr (write_reply n)). split; eauto. repeat constructor.
        -- exists tt, (tt, (tt, (tt, buf))). split; repeat constructor.
    - intros. cbn in *. eprod_crush. exists tt. inv H2; inv H3.
      * eexists (st2 L1 pipe_operator
                   (st2 seq (with_semantics secret_spec rot13_spec) seq2 (inr (rot13_write hello_bytes)), buf)
                   (pipe2_write_query hello_bytes buf)).
        split.
        -- left. eapply plus_left. (* seq calls secret *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_push; repeat constructor. }
           2: { instantiate (1 := E0). reflexivity. }
           step1. (* secret calls write to pipe *)
           { eapply step_push.
             instantiate (1 := (_, _)). repeat constructor. constructor. }
           step1. (* pipe returns to secret *)
           { eapply step_pop. repeat constructor.
             instantiate (1 := (_, _)). repeat constructor; cbn.
             eexists. split; eauto. reflexivity.
             repeat constructor. }
           step1. (* secret returns to seq *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_pop; repeat constructor. }
           step1. (* seq calls rot13 *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_push; repeat constructor. }
           step1. (* rot13 calls read to pipe *)
           { eapply step_push.
             instantiate (1 := (_, _)). repeat constructor. constructor. }
           step1. (* pipe returns to rot13 *)
           { eapply step_pop. repeat constructor.
             instantiate (1 := (_, _)). repeat constructor; cbn.
             eexists. split; eauto. reflexivity.
             repeat constructor. }
           step1. (* rot13 calls write to pipe *)
           { eapply step_push.
             instantiate (1 := (_, _)). repeat constructor. constructor. }
           rewrite rot13_bytes_urbby. apply star_refl.
        -- exists tt, (tt, (tt, (tt, buf))). split; repeat constructor.
      * exists (st1 L1 pipe_operator (st1 seq (with_semantics secret_spec rot13_spec) (ret n), buf)).
        split.
        -- left. eapply plus_left. (* pipe returns to rot13 *)
           { eapply step_pop. repeat constructor.
             instantiate (1 := (_, _)). repeat constructor; cbn.
             eexists. split; eauto. reflexivity.
             repeat constructor. }
           2: { instantiate (1 := E0). reflexivity. }
           step1. (* rot13 returns to seq *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_pop; repeat constructor. }
           apply star_refl.
        -- exists tt, (tt, (tt, (tt, buf))). split; repeat constructor.
  Qed.

End PIPE_CORRECT.
