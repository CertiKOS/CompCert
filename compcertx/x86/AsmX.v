Require Asm.
Require MemoryX.

Import Coqlib.
Import Integers.
Import Floats.
Import AST.
Import Values.
Import MemoryX.
Import Globalenvs.
Import Events.
Import Smallstep.
Import Locations.
Import Conventions.
Export Asm.
Require Import LocationsX.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

(** Execution of Asm functions with Asm-style arguments (long long 64-bit integers NOT allowed) *)

Inductive initial_state
          (lm: regset) (p: Asm.program) (i: ident)
          (sg: signature) (args: list val) (m: mem): state -> Prop :=
| initial_state'_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    (Hpc: lm PC = Vptr b Ptrofs.zero)
    (Hargs: extcall_arguments lm m sg args):
    initial_state lm p i sg args m (State lm (Mem.push_new_stage m)).

Definition get_pair (p: rpair preg) (rs:regset) : val :=
  match p with
    One l => rs l
  | Twolong l1 l2 => Val.longofwords (rs l1) (rs l2)
  end.

Inductive final_state (lm: regset) (sg: signature) : state -> (val * mem) -> Prop :=
  | final_state_intro:
      forall rs,
        eq (lm # RA) (rs # PC) ->
        eq (lm # RSP) (rs # RSP) ->
        forall v,
          v = get_pair (loc_external_result sg) rs ->
          forall
            (RA_VUNDEF: rs # RA = Vundef)
            (CALLEE_SAVE: forall r,
                ~ In r destroyed_at_call ->
                Val.lessdef (lm (preg_of r)) (rs (preg_of r))),
          forall m_,
            final_state lm sg (State rs m_) (v, m_).

Section WITH_MEM_ACCESSORS_DEFAULT.
  Local Existing Instance mem_accessors_default.

  Definition semantics (lm: regset) (p: Asm.program) (i: ident) (sg: signature) (args: list val) (m: mem) :=
    Semantics (step (Mem.stack m)) (initial_state lm p i sg args m) (final_state lm sg) (Genv.globalenv p).

End WITH_MEM_ACCESSORS_DEFAULT.

(** Properties of arguments *)

Lemma extcall_args_64_inject_neutral `{Hmem: !Mem.MemoryModel mem}:
  forall rs,
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)),
    forall tl ir fr ofs vl,
      list_forall2 (Asm.extcall_arg_pair rs m) (loc_arguments_64 tl ir fr ofs) vl ->
      Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl.
Proof.
  Opaque int_param_regs float_param_regs.
  induction tl; simpl.
  - inversion 4; subst. constructor.
  -
    assert ( forall ir fr ofs (vl : list val),
               list_forall2 (extcall_arg_pair rs m)
                            (One (S Outgoing ofs a) :: loc_arguments_64 tl ir fr (ofs + typesize a)) vl ->
               Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl).
    {
      inversion 1; subst.
      inv H3. inv H2.
      constructor.
      eapply Mem.loadv_inject_neutral; eauto.
      eauto.
    }
    assert ( forall ty (ir fr ofs : Z) (vl : list val),
  list_forall2 (extcall_arg_pair rs m)
    match list_nth_z int_param_regs ir with
    | Some ireg => One (R ireg) :: loc_arguments_64 tl (ir + 1) fr ofs
    | None => One (S Outgoing ofs ty) :: loc_arguments_64 tl ir fr (ofs + 2)
    end vl -> Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl). {
      inversion 1; subst.
      constructor.
      inv H3.
      - inv H5.
        + destruct (list_nth_z int_param_regs ir); inv H2.
          constructor; eauto.
        + destruct (list_nth_z int_param_regs ir); inv H2.
          constructor; eauto.
          eapply Mem.loadv_inject_neutral; eauto.
      - destruct (list_nth_z int_param_regs ir); inv H2.
    }
    assert (forall ty (ir fr ofs : Z) (vl : list val),
               list_forall2 (extcall_arg_pair rs m)
                            match list_nth_z float_param_regs fr with
                            | Some freg => One (R freg) :: loc_arguments_64 tl ir (fr + 1) ofs
                            | None => One (S Outgoing ofs ty) :: loc_arguments_64 tl ir fr (ofs + 2)
                            end vl -> Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl).
    {
      inversion 1; subst.
      constructor.
      inv H4.
      - inv H6. constructor; eauto.
        + destruct (list_nth_z float_param_regs fr); inv H3. eauto. 
        + destruct (list_nth_z float_param_regs fr); inv H3.
          inv H2. constructor; eauto.
          eapply Mem.loadv_inject_neutral; eauto.
      - destruct (list_nth_z float_param_regs fr); inv H3.
    }
    destruct a; eauto.
Qed.

Lemma extcall_args_32_inject_neutral `{Hmem: !Mem.MemoryModel mem}:
  forall rs,
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)),
    forall tl ofs vl,
      list_forall2 (Asm.extcall_arg_pair rs m) (loc_arguments_32 tl ofs) vl ->
      Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl.
Proof.
  induction tl; simpl.
  - inversion 2; subst. constructor.
  -
    assert ( forall ofs (vl : list val),
               list_forall2 (extcall_arg_pair rs m)
                            (One (S Outgoing ofs a) :: loc_arguments_32 tl (ofs + typesize a)) vl ->
               Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl).
    {
      inversion 1; subst.
      inv H3. inv H2.
      constructor.
      eapply Mem.loadv_inject_neutral; eauto.
      eauto.
    }
    assert ( forall ty (ofs : Z) (vl : list val),
  list_forall2 (extcall_arg_pair rs m)
               (One (S Outgoing ofs ty) :: loc_arguments_32 tl (ofs + typesize ty))
               vl ->
  Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl). {
      inversion 1; subst.
      constructor.
      inv H4.
      inv H3.
      eapply Mem.loadv_inject_neutral; eauto.
      eauto. 
    }
    destruct a; eauto.
    intros. inv H2. constructor; eauto.
    inv H5.
    eapply Val.longofwords_inject.
    inv H4. eapply Mem.loadv_inject_neutral; eauto.
    inv H8. eapply Mem.loadv_inject_neutral; eauto.
Qed.

Lemma extcall_args_inject_neutral `{Gmem: !Mem.MemoryModel mem}:
  forall rs,
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)),
    forall tl vl,
      list_forall2 (Asm.extcall_arg_pair rs m) (loc_arguments tl) vl ->
      Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vl vl.
Proof.
  intros rs m MINJ Hinj_reg tl vl.
  unfold loc_arguments. destruct Archi.ptr64.
  eapply extcall_args_64_inject_neutral; eauto.
  eapply extcall_args_32_inject_neutral; eauto.
Qed.

(** Invariants *)

Definition mreg_of (r: preg) : option mreg :=
  match r with
  | IR RAX => Some AX
  | IR RBX => Some BX
  | IR RCX => Some CX
  | IR RDX => Some DX
  | IR RSI => Some SI
  | IR RDI => Some DI
  | IR RBP => Some BP
  | IR R8 => Some Machregs.R8
  | IR R9 => Some Machregs.R9
  | IR R10 => Some Machregs.R10
  | IR R11 => Some Machregs.R11
  | IR R12 => Some Machregs.R12
  | IR R13 => Some Machregs.R13
  | IR R14 => Some Machregs.R14
  | IR R15 => Some Machregs.R15
  | FR XMM0 => Some X0
  | FR XMM1 => Some X1
  | FR XMM2 => Some X2
  | FR XMM3 => Some X3
  | FR XMM4 => Some X4
  | FR XMM5 => Some X5
  | FR XMM6 => Some X6
  | FR XMM7 => Some X7
  | FR XMM8 => Some X8
  | FR XMM9 => Some X9
  | FR XMM10 => Some X10
  | FR XMM11 => Some X11
  | FR XMM12 => Some X12
  | FR XMM13 => Some X13
  | FR XMM14 => Some X14
  | FR XMM15 => Some X15
  | ST0 => Some FP0
  | PC
  | IR RSP
  | CR _
  | RA => None
  end.

Lemma mreg_of_complete:
  forall r,
    mreg_of (preg_of r) = Some r.
Proof.
  destruct r; reflexivity.
Qed.

Lemma mreg_of_correct:
  forall r m,
    mreg_of r = Some m -> preg_of m = r.
Proof.
  intros r m MO.
  destruct r; simpl in MO; repeat destr_in MO; reflexivity.
Qed.

Definition typ_of_preg (r: preg): typ :=
  match mreg_of r with
    Some m => Machregs.mreg_type m
  | None => match r with
           | PC | IR RSP | RA => Tptr
           | _ => Tany64
           end
  end.

Definition wt_regset (rs: regset) :=
  forall r, Val.has_type (rs # r) (typ_of_preg r).

Record inject_neutral_invariant {F V: Type} (ge: Genv.t F V) (rs: regset) (m: mem): Prop :=
  {
    inv_mem_valid:
      (Genv.genv_next ge <= Mem.nextblock m)%positive;
    inv_mem_inject_neutral:
      Mem.inject_neutral (Mem.nextblock m) m;
    inv_reg_inject_neutral r:
      Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs # r) (rs # r)
  }.

Record asm_invariant {F V: Type} (ge: Genv.t F V) (rs: regset) (m: mem): Prop :=
  {
    inv_inject_neutral :> inject_neutral_invariant ge rs m;
    inv_reg_wt: wt_regset rs
  }.

(** Proof that the invariants are preserved by Asm steps. *)

(** For the proof of [exec_instr_inject_neutral] below, we need
[MemoryX.inject_neutral_incr] for [Pallocframe]. *)
Context `{memory_model_x: !Mem.MemoryModelX mem}.


(** Typing invariant on registers *)

Lemma set_reg_wt: 
 forall v r',
   Val.has_type v (typ_of_preg r') ->
   forall rs,
     wt_regset rs ->
     wt_regset (rs # r' <- v)
.
Proof.
  red. intros. destruct (preg_eq r r').
   subst. repeat rewrite Pregmap.gss. assumption.
  repeat rewrite Pregmap.gso; eauto.
Qed.

Lemma undef_reg_wt:
  forall rs,
    wt_regset rs ->
    forall r',
    wt_regset (rs # r' <- Vundef).
Proof.
  intros; eapply set_reg_wt; simpl; eauto.
Qed.

Lemma undef_regs_wt:
  forall rs,
    wt_regset rs ->
    forall l, wt_regset (undef_regs l rs).
Proof.
  intros until l. revert rs H. induction l; simpl; eauto using undef_reg_wt.
Qed.

Lemma nextinstr_wt:
  forall rs sz,
    wt_regset rs ->
    wt_regset (nextinstr rs sz).
Proof.
  unfold nextinstr.  intros.
  apply set_reg_wt; eauto.
  simpl. generalize (H PC); simpl.
  destruct (rs PC); simpl; clear; tauto.
Qed.

Lemma nextinstr_nf_wt:
  forall rs sz,
    wt_regset rs ->
    wt_regset (nextinstr_nf rs sz).
Proof.
  unfold nextinstr_nf.
  intros.
  apply nextinstr_wt.
  apply undef_regs_wt.
  assumption.
Qed.


(** Inject_neutral *)

Lemma set_reg_inject: 
 forall j v v',
   Val.inject j v v' ->
   forall rs rs',
     (forall r, Val.inject j (rs#r) (rs'#r)) ->
     forall r' r, Val.inject j ((rs#r' <- v)#r) ((rs'#r' <- v')#r)
.
Proof.
  intros. destruct (preg_eq r r').
   subst. repeat rewrite Pregmap.gss. assumption.
  repeat rewrite Pregmap.gso; eauto.
Qed.

Lemma undef_reg_inject:
  forall j rs rs',
    (forall r, Val.inject j (rs#r) (rs'#r)) ->
    forall r' r, Val.inject j ((rs#r' <- Vundef)#r) ((rs'#r' <- Vundef)#r).
Proof.
  intros; apply set_reg_inject; auto.
Qed.

Lemma undef_regs_inject:
  forall j rs rs',
    (forall r, Val.inject j (rs#r) (rs'#r)) ->
    forall l r, Val.inject j ((undef_regs l rs)#r) ((undef_regs l rs')#r).
Proof.
  intros until l. revert rs rs' H. induction l; simpl; eauto using undef_reg_inject.
Qed.

Lemma nextinstr_inject:
  forall j rs rs' sz,
    (forall r, Val.inject j (rs#r) (rs'#r)) ->
    forall r, Val.inject j ((nextinstr rs sz)#r) ((nextinstr rs' sz)#r).
Proof.
  unfold nextinstr.  intros.
  apply set_reg_inject; eauto.
  eapply Val.offset_ptr_inject; eauto.
Qed.

Lemma nextinstr_nf_inject:
  forall j rs rs' sz,
    (forall r, Val.inject j (rs#r) (rs'#r)) ->
    forall r, Val.inject j ((nextinstr_nf rs sz)#r) ((nextinstr_nf rs' sz)#r).
Proof.
  unfold nextinstr_nf.
  intros.
  apply nextinstr_inject.
  apply undef_regs_inject.
  assumption.
Qed.

Lemma regs_inject_map:
  forall j rs rs',
    (forall r: preg, Val.inject j (rs#r) (rs'#r)) ->
    forall args,
  list_forall2 (Val.inject j) (map rs args) (map rs' args).
Proof.
  induction args; simpl; constructor; auto.
Qed.

Lemma val_inject_neutral_incr: forall thr v, Val.inject (Mem.flat_inj thr) v v -> forall thr', Ple thr thr' -> Val.inject (Mem.flat_inj thr') v v.
Proof.
  inversion 1; try constructor.
  clear H4. subst. unfold Mem.flat_inj in *. destruct (plt b1 thr); try discriminate. inv H3.
  econstructor. destruct (plt b1 thr'); try xomega. reflexivity. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma extcall_arg_inject_neutral':
  forall m rs
         (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         l v,
    extcall_arg rs m l v ->
    Val.inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof.
  induction 3; auto.
  generalize H0. unfold Mem.loadv. case_eq (rs RSP); try discriminate. simpl.
  intros. eapply Mem.loadv_inject_neutral; eauto.
Qed.

Lemma extcall_arg_pair_inject_neutral':
  forall m rs
         (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         l v,
    extcall_arg_pair rs m l v ->
    Val.inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof.
  destruct l; simpl; intros v H; inv H;
  repeat match goal with
           H: extcall_arg _ _ _ _ |- _ => 
           eapply extcall_arg_inject_neutral' in H; eauto
         end.
  eapply Val.longofwords_inject; eauto.
Qed.

Lemma extcall_args_inject_neutral':
  forall m rs
         (Hinj_reg: forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         sg args,
    extcall_arguments rs m sg args ->
    list_forall2 (Val.inject (Mem.flat_inj (Mem.nextblock m))) args args.
Proof.
  unfold extcall_arguments. intros until sg. generalize (loc_arguments sg). clear sg.
  induction 1; constructor; eauto using extcall_arg_pair_inject_neutral'.
Qed.

Lemma shl_inject_neutral:
  forall f v1 v2,
    Val.inject f (Val.shl v1 v2) (Val.shl v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma shr_inject_neutral:
  forall f v1 v2,
    Val.inject f (Val.shr v1 v2) (Val.shr v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma shru_inject_neutral:
  forall f v1 v2,
    Val.inject f (Val.shru v1 v2) (Val.shru v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma ror_inject_neutral:
  forall f v1 v2,
    Val.inject f (Val.ror v1 v2) (Val.ror v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
Qed.

Lemma of_bool_inject_neutral:
  forall f b,
    Val.inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  destruct b; simpl; constructor.
Qed.

Lemma compare_floats_inject_neutral:
  forall f rs,
    (forall r: preg, Val.inject f (rs r) (rs r)) ->
    forall a b r,
      Val.inject f (compare_floats a b rs r) (compare_floats a b rs r).
Proof with (simpl;
            repeat apply undef_reg_inject;
            auto using of_bool_inject_neutral).
  intros. unfold compare_floats. destruct a...
  destruct b...
  repeat apply set_reg_inject...
Qed.

Lemma cmpu_inject_neutral:
  forall f p c a b,
    Val.inject f (Val.cmpu p c a b) (Val.cmpu p c a b).
Proof.
  intros.
  unfold Val.cmpu. destruct (Val.cmpu_bool p c a b); simpl; auto.
  destruct b0; constructor.
Qed.

Lemma cmp_inject_neutral:
  forall f p c a,
    Val.inject f (Val.cmp p c a) (Val.cmp p c a).
Proof.
  intros.
  unfold Val.cmp. destruct (Val.cmp_bool p c a); simpl; auto.
  destruct b; constructor.
Qed.

Lemma sub_overflow_inject_neutral:
  forall f a b,
    Val.inject f (Val.sub_overflow a b) (Val.sub_overflow a b).
Proof.
  intros.
  unfold Val.sub_overflow.
  destruct a; destruct b; constructor.
Qed.

Lemma negative_inject_neutral:
  forall f a,
    Val.inject f (Val.negative a) (Val.negative a).
Proof.
  unfold Val.negative.
  destruct a; constructor.
Qed.

Lemma compare_ints_inject_neutral:
  forall f rs,
    (forall r: preg, Val.inject f (rs r) (rs r)) ->
    forall a b m r,
      Val.inject f (compare_ints a b rs m r) (compare_ints a b rs m r).
Proof.
  unfold compare_ints.
  intros.
  apply undef_reg_inject.
  eauto using set_reg_inject, cmpu_inject_neutral, undef_reg_inject, negative_inject_neutral, sub_overflow_inject_neutral.
Qed.

Lemma symbol_address_inject_neutral_gen
      se i ofs j:
  (forall (id : ident) (b : block),
      Senv.find_symbol se id = Some b -> j b = Some (b, 0)) ->
  Val.inject j (Senv.symbol_address se i ofs) (Senv.symbol_address se i ofs).
Proof.
  intros.
  unfold Senv.symbol_address.
  destruct (Senv.find_symbol se i) eqn:SYMB; auto.
  econstructor; eauto.
  rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma symbol_address_inject_neutral_preserves_global
      {F V}
      ge i ofs j:
  meminj_preserves_globals (F := F) (V := V) ge j ->
  Val.inject j (Senv.symbol_address ge i ofs) (Senv.symbol_address ge i ofs).
Proof.
  unfold meminj_preserves_globals.
  destruct 1 as (H & _ & _).
  eapply symbol_address_inject_neutral_gen; eauto.
Qed.

Lemma symbol_address_inject_neutral_le_nextblock
      se n i ofs:
  Ple (Senv.nextblock se) n ->
  Val.inject (Mem.flat_inj n) (Senv.symbol_address se i ofs) (Senv.symbol_address se i ofs).
Proof.
  intros H.
  eapply symbol_address_inject_neutral_gen; eauto.
  intros id0 b H0.
  unfold Mem.flat_inj.
  destruct (plt _ _) as [ | N ] ; auto.
  destruct N.
  apply Senv.find_symbol_below in H0.
  xomega.
Qed.

Lemma symbol_address_inject_neutral_le_nextblock_genv
      {F V} (ge: Genv.t F V) n i ofs:
  Ple (Genv.genv_next ge) n ->
  Val.inject (Mem.flat_inj n) (Genv.symbol_address ge i ofs) (Genv.symbol_address ge i ofs).
Proof.
  intro.
  replace (Genv.symbol_address ge) with (Senv.symbol_address ge) by reflexivity.
  eapply symbol_address_inject_neutral_le_nextblock; eauto.
Qed.

Lemma eval_addrmode_inject_neutral:
  forall {F V} (ge: Genv.t F V) m,
    Ple (Genv.genv_next ge) (Mem.nextblock m) ->
    forall rs,
      (forall r, Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)) ->
    forall a,
    Val.inject (Mem.flat_inj (Mem.nextblock m)) (eval_addrmode ge a rs) (eval_addrmode ge a rs).
Proof.
  intros.
  unfold eval_addrmode.
  destruct Archi.ptr64.
  - destruct a.
    simpl. apply Val.addl_inject. destruct base; auto.
    apply Val.addl_inject. destruct ofs; auto.
    destruct p; auto. destruct zeq; auto.
    destruct (rs i) eqn:?; simpl; auto.
    destruct const; auto. destruct p; auto.
    eapply symbol_address_inject_neutral_le_nextblock_genv; eauto.
  - destruct a.
    simpl. apply Val.add_inject. destruct base; auto.
    apply Val.add_inject. destruct ofs; auto.
    destruct p; auto. destruct zeq; auto.
    destruct (rs i) eqn:?; simpl; auto.
    destruct const; auto. destruct p; auto.
    eapply symbol_address_inject_neutral_le_nextblock_genv; eauto.
Qed.


Ltac destr_all :=
  repeat match goal with
           |- context [match ?g with _ => _ end] =>
           (destruct g eqn:?; try discriminate)
         | |- context [if ?g then _ else _] =>
           (destruct g eqn:?; try discriminate)
         end.
Ltac solve_reg_inj :=
  repeat
    match goal with
    | |- forall r, Val.inject _ (nextinstr_nf _ _) (nextinstr_nf _ _) => apply set_reg_inject; auto
    | |- forall r, Val.inject _ (_ # _ <- _ _) (_ # _ <- _ _) => apply set_reg_inject; auto
    | |- Val.inject _ (Val.offset_ptr _ _) (Val.offset_ptr _ _) => apply Val.offset_ptr_inject; auto
    | |- Val.inject _ (undef_regs _ _ _) (undef_regs _ _ _) => apply undef_regs_inject; auto
    | |- _ => intros
    end.

End WITHCONFIG.



