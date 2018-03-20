Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
(* Require Memimpl. *)
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Import AsmFacts.

Section WITHMEMORYMODEL.
  
  Context `{memory_model: Mem.MemoryModel }.
  Existing Instance inject_perm_upto_writable.

  Program Definition frame_info_mono: frame_info :=
    {|
      frame_size := Mem.stack_limit;
      frame_perm := fun o => Public;
    |}.

  Existing Instance mem_accessors_default.

  Context `{external_calls_ops : !ExternalCallsOps mem }.
  Context `{!EnableBuiltins mem}.
  Existing Instance symbols_inject_instance.
  Context `{external_calls_props : !ExternalCallsProps mem
                                    (memory_model_ops := memory_model_ops)
                                    }.

  Variable prog: Asm.program.
  Let ge := Genv.globalenv prog.
  Definition bstack: block := Genv.genv_next ge.
  Section PRESERVATION.

  Definition current_offset (v: val) :=
    match v with
      Vptr stk ofs => Ptrofs.unsigned ofs
    | _ => Mem.stack_limit
    end.

  Definition offset_after_alloc (p: Z) fi :=
    (p - align (Z.max 0 (frame_size fi)) 8).

  Definition offset_after_free (p: Z) sz :=
    (p + align (Z.max 0 sz) 8).

  Variable binit_sp: block.
  Definition init_sp: val := Vptr binit_sp Ptrofs.zero.

  (* [init_sp] is required to be a pointer, i.e. Vptr bsp osp.
   * The whole-program setting is emulating by allocating an empty block
   * for the arguments to main and using this block for init_sp.
   *
   * Because now, RSP is updated with increments/decrements, it's unclear how
   * to cleanly recover a Vnullptr for example when needed to match with the original
   * program.
   *)

  Lemma type_init_sp:
    Val.has_type init_sp Tptr.
  Proof.
    unfold init_sp; apply Val.Vptr_has_type.
  Qed.

  Lemma init_sp_zero:
    forall b o,
      init_sp = Vptr b o -> o = Ptrofs.zero.
  Proof.
    inversion 1; auto.
  Qed.

  Definition exec_instr {F V} (ge: Genv.t F V) f i rs (m: mem) :=
    match i with
    | Pallocframe fi ofs_ra =>
      let curofs := current_offset (rs RSP) in
      let sp := Vptr bstack (Ptrofs.repr (offset_after_alloc curofs fi)) in
      (* match Mem.storev Mptr m (Val.offset_ptr sp ofs_link) rs#RSP with *)
      (* | None => Stuck *)
      (* | Some m2 => *)
        match Mem.storev Mptr m (Val.offset_ptr sp ofs_ra) rs#RA with
        | None => Stuck
        | Some m3 =>
          Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)) m3
        end
      (* end *)
    | Pfreeframe sz ofs_ra unrecord =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
      | None => Stuck
      | Some ra =>
        let curofs := current_offset (rs RSP) in
        let sp := Vptr bstack (Ptrofs.repr (offset_after_free curofs sz)) in
        Next (nextinstr (rs#RSP <- sp #RA <- ra)) m
      end
    | Pload_parent_pointer rd z =>
      let curofs := current_offset (rs RSP) in
      let sp := Vptr bstack (Ptrofs.repr (offset_after_free curofs z)) in
      Next (nextinstr (rs#rd <- sp)) m
    | Pcall_s id sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
    | Pcall_r r sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (rs r)) m
    | _ => Asm.exec_instr Vnullptr ge f i rs m
    end.

  Definition is_unchanged i :=
    match i with
      Pallocframe _ _
    | Pfreeframe _ _ _
    | Pload_parent_pointer _ _
    | Pcall_s _ _
    | Pcall_r _ _ => false
    | _ => true
    end.

  Lemma is_unchanged_exec:
    forall (ge: Genv.t Asm.fundef unit) f rs m i,
      is_unchanged i = true ->
      exec_instr ge f i rs m = Asm.exec_instr Vnullptr ge f i rs m.
  Proof.
    destruct i; simpl; intros; congruence.
  Qed.
  
  Inductive step (ge: Genv.t Asm.fundef unit) : state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
        exec_instr ge f i rs m = Next rs' m' ->
        step ge (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
        eval_builtin_args ge rs (rs RSP) m args vargs ->
        external_call ef ge vargs m t vres m' ->
        forall BUILTIN_ENABLED: builtin_enabled ef,
          rs' = nextinstr_nf
                  (set_res res vres
                           (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
          step ge (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
        rs PC = Vptr b Ptrofs.zero ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        extcall_arguments rs m (ef_sig ef) args ->
        forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
          (RA_TYPE: Val.has_type (rs RA) Tptr)
          (SP_NOT_VUNDEF: rs RSP <> Vundef)
          (RA_NOT_VUNDEF: rs RA <> Vundef), 
          external_call ef ge args m t res m' ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->
          step ge (State rs m) t (State rs' m').

 
  Definition no_inject_below j m thr:=
    forall b delta o k p,
      j b = Some (bstack, delta) ->
      Mem.perm m b o k p ->
      thr <= o + delta /\ in_stack (Mem.stack_adt m) b.

  Definition agree_sp m1 rs2:=
    forall ostack,
      rs2 # RSP = Vptr bstack ostack ->
      Ptrofs.unsigned ostack = Mem.stack_limit - StackADT.size_stack (Mem.stack_adt m1).

  Definition perm_bstack m2:=
    forall (ofs : Z) (k : perm_kind) (p : permission),
       Mem.perm m2 bstack ofs k p -> 0 <= ofs < Ptrofs.max_unsigned /\  perm_order Writable p.

  Definition perm_bstack_stack_limit m2:=
    forall (ofs : Z) (k : perm_kind),
      0 <= ofs < Mem.stack_limit ->
      Mem.perm m2 bstack ofs k Writable.

  Definition sp_aligned rs2:=
    forall ostack,
      rs2 # RSP = Vptr bstack ostack ->
      (8 | Ptrofs.unsigned ostack).

  Definition no_stack m2 :=
    exists fr fi,
      Mem.stack_adt m2 = (fr::nil)::nil /\
      (bstack,fi)::nil = frame_adt_blocks fr /\
      0 = frame_adt_size fr /\
      (forall o, frame_perm fi o = Public) /\
      frame_size fi = Mem.stack_limit.

  Inductive inject_stack: meminj -> stack_adt -> Prop :=
  | inject_stack_nil j :
      inject_stack j nil
  | inject_stack_cons j l f:
      inject_stack j l ->
      (forall fr,
          In fr f ->
          exists b fi,
            j b = Some (bstack, Mem.stack_limit - size_stack l - align (Z.max 0 (frame_size fi)) 8) /\
            frame_adt_blocks fr = (b,fi)::nil /\
            frame_adt_size fr = frame_size fi) ->
      inject_stack j (f::l).

  Inductive perm_stack: stack_adt -> mem -> Prop :=
  | ps_nil m:
      perm_stack nil m
  | ps_cons l m fr r
            (PSrec: perm_stack l m)
            (PERMEQ: forall b fi o k p, In (b,fi) (frame_adt_blocks fr) -> Mem.perm m b o k p <-> 0 <= o < frame_size fi)
            (ORDER: forall fr0, In fr0 (fr::r) -> exists b fi, frame_adt_blocks fr0 = (b,fi)::nil /\ forall b', in_stack l b' -> Plt b' b):
      perm_stack ((fr::r)::l) m.

  Definition inject_padding (j: meminj) (m: mem) : Prop :=
    forall b fi delta,
      in_stack' (Mem.stack_adt m) (b,fi) ->
      j b = Some (bstack, delta) ->
      forall b' o delta' k p,
        j b' = Some (bstack, delta') ->
        Mem.perm m b' o k p ->
        ~ ( delta + Z.max 0 (frame_size fi) <= o + delta' < delta + align (Z.max 0 (frame_size fi)) 8).

  Inductive match_states: meminj -> Z -> state -> state -> Prop :=
  | match_states_intro:
      forall j (rs: regset) (m: mem) (rs': regset) m'
        (MINJ: Mem.inject j (fun n => if lt_dec n (length (Mem.stack_adt m)) then Some O else None) m m')
        (RSPzero: forall b o, rs # RSP = Vptr b o -> o = Ptrofs.zero )
        (RINJ: forall r, Val.inject j (rs # r) (rs' # r))
        (VB: Mem.valid_block m' bstack)
        (AGSP: agree_sp m rs')
        (AGSP1: match Mem.stack_adt m with
                  nil => rs # RSP = init_sp
                | (fr::_)::r =>
                  match frame_adt_blocks fr with
                    (b,fi)::nil =>
                    rs # RSP = Vptr b Ptrofs.zero
                  | _ => False
                  end
                | nil::r => False
                end)
        (* (SZpos: Forall (fun f : frame_adt => 0 <= frame_adt_size f) (Mem.stack_adt m)) *)
        (* (OneLink: Forall (fun f : frame_adt => option_map (fun f => length (frame_link f)) (frame_adt_info f) = Some 1%nat) (Mem.stack_adt m)) *)
        (SPAL: sp_aligned rs')
        (PBS: perm_bstack m')
        (PBSL: perm_bstack_stack_limit m')
        (NS: no_stack m')
        ostack
        (RSPEQ: forall b o, rs' RSP = Vptr b o -> b = bstack /\ o = ostack)
        (NIB: no_inject_below j m (Ptrofs.unsigned ostack))
        (IS: inject_stack j (Mem.stack_adt m))
        (IP: inject_padding j m)
        (PS: perm_stack (Mem.stack_adt m) m)
        (* (LRSP: load_rsp (Mem.stack_adt m) m) *)
        (GLOBFUN_INJ: forall b f, Genv.find_funct_ptr ge b = Some f -> j b = Some (b,0))
        (GLOBDEF_INJ: forall b f, Genv.find_def ge b = Some f -> j b = Some (b,0))
        (GLOBSYMB_INJ: meminj_preserves_globals' ge j)
        (GlobLe: (Genv.genv_next ge <= Mem.nextblock m)%positive)
        (GlobLeT: (Genv.genv_next ge <= Mem.nextblock m')%positive)
        (SPinstack: forall b o, init_sp = Vptr b o -> in_stack (Mem.stack_adt m) b)
      ,
        match_states j (Ptrofs.unsigned ostack) (State rs m) (State rs' m').

  Lemma inject_stack_incr:
    forall j j' (INCR: inject_incr j j')
      l (IS: inject_stack j l),
      inject_stack j' l.
  Proof.
    induction 2; econstructor; eauto.
    intros fr IN.
    specialize (H fr IN). decompose [ex and] H; clear H. eapply INCR in H0. eauto.
  Qed.
  
  Definition is_ptr v :=
    match v with
      Vptr _ _ => True
    | _ => False
    end.

  Lemma is_ptr_dec v: {is_ptr v} + {~ is_ptr v}.
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma perm_stack_inv:
    forall l m (PS: perm_stack l m) m'
      (U: forall b o k p, in_stack l b -> Mem.perm m' b o k p <-> Mem.perm m b o k p),
      perm_stack l m'.
  Proof.
    induction 1; simpl; intros; econstructor; eauto.
    - eapply IHPS. intros. apply U. apply in_stack_tl. simpl. auto.
    - intros.
      edestruct ORDER as (bb & ffi & BLOCKS & ORDER'). left; reflexivity.
      rewrite BLOCKS in H. destruct H as [H|[]]. inv H.
      rewrite U. apply PERMEQ. rewrite BLOCKS; simpl; auto.
      rewrite in_stack_cons; left.
      rewrite  in_frames_cons; left. red. unfold get_frame_blocks. setoid_rewrite BLOCKS.
      left; reflexivity.
  Qed.

  Axiom exec_instr_inject:
    forall j g m1 m2 rs1 rs2 f i rs1' m1'
      (MINJ: Mem.inject j g m1 m2)
      (RINJ: forall r, Val.inject j (rs1 # r) (rs2 # r))
      (IU: is_unchanged i = true)
      (EXEC: Asm.exec_instr init_sp ge f i rs1 m1 = Next rs1' m1')
      init_sp'
      (init_sp_inject: Val.inject j init_sp init_sp'),
      exists rs2' m2',
        Asm.exec_instr init_sp' ge f i rs2 m2 = Next rs2' m2'
        /\ Mem.inject j g m1' m2'
        /\ (forall r, Val.inject j (rs1' # r) (rs2' # r))
        (* /\ (forall b b' delta, j b = None -> j' b = Some (b', delta) -> Ple (Genv.genv_next ge) b /\ b' <> bstack) *). 
  (* should be proved already somewhere *)

  Lemma free_inject:
    forall j g m1 b lo hi m2 m3 m1',
      Mem.inject j g m1 m1' ->
      Mem.free m1 b lo hi = Some m2 ->
      (forall o k p, Mem.perm m1 b o k p -> lo <= o < hi) ->
      (forall b0, is_stack_top (Mem.stack_adt m2) b0 -> b0 = b) ->
      Mem.unrecord_stack_block m2 = Some m3 ->
      g 1%nat = Some O ->
      length (Mem.stack_adt m1') = 1%nat ->
      no_stack m1' ->
      Mem.inject j (fun n => g (S n)) m3 m1'.
  Proof.
    intros j g m1 b lo hi m2 m3 m1' INJ FREE PERMRNG IST USB G1 LST NS.
    eapply Mem.unrecord_stack_block_inject_left_zero.
    eapply Mem.free_left_inject. eauto. eauto. eauto.
    intros. eapply stack_inject_range in H. 2: eapply Mem.inject_stack_adt; eauto.
    rewrite LST in H. omega.
    intros.
    apply IST in H. subst. intros PERM.
    eapply Mem.perm_free in PERM. 2: eauto. destruct PERM. apply H. split; eauto.
    auto.
  Qed.
  
  Lemma ZEQ: forall a b,
      proj_sumbool (zeq a b) = true -> a = b.
  Proof.
    intros; destruct zeq; auto. discriminate.
  Qed.

  Lemma ZLE: forall a b c d,
      zle a b || zle c d = true ->
      a <= b \/ c <= d.
  Proof.
    intros; destruct (zle a b), (zle c d); try congruence; try omega.
    simpl in H; congruence.
  Qed.
  
  Lemma perm_stack_eq:
    forall l m b fi
      (WF: wf_stack (Mem.perm m) inject_id l)
      (PS: perm_stack l m)
      fr r
      (INBLOCKS: In (b,fi) (frame_adt_blocks fr))
      (INSTK: In (fr::r) l)
      o k p,
      Mem.perm m b o k p <-> 0 <= o < frame_size fi.
  Proof.
    induction 2; simpl; intros; eauto. easy.
    destruct INSTK as [EQ | INSTK].
    - inv EQ. apply PERMEQ. auto.
    - eapply IHPS; eauto. inv WF; auto.
  Qed.
  
  Lemma in_stack_inj_below:
    forall j l
      (IS: inject_stack j l)
      b fi f
      (INFRAMES: in_frames' f (b,fi))
      (INSTK: In f l),
    exists l1 l2,
      l = l1 ++ l2 /\
      j b = Some (bstack, Mem.stack_limit - StackADT.size_stack l2 + size_frames f - align (frame_size fi) 8).
  Proof.
    induction 1; simpl; intros; eauto. easy.
    destruct INSTK as [EQ|INSTK].
    - rewrite in_frames'_rew in INFRAMES. destruct INFRAMES as (fr & IFR & IFR'). subst.
      specialize (H _ IFR').
      destruct H as (bb & ffi & JB & BLOCKS & SIZE). red in IFR.
      rewrite BLOCKS in IFR.
      simpl in IFR. destruct IFR as [IFR|[]]; inv IFR.
      rewrite JB. exists nil. simpl. eexists; split; eauto. simpl. f_equal. f_equal. rewrite <- SIZE.
      rewrite Z.max_r. 2: destruct fr; auto. omega.
    - specialize (IHIS _ _ _ INFRAMES INSTK).
      destruct IHIS as (l1 & l2 & EQl & JB).
      subst.
      rewrite JB.
      repeat eexists.
      rewrite app_comm_cons. eauto.
  Qed.
  
  Lemma size_stack_app:
    forall l1 l2,
      StackADT.size_stack (l1 ++ l2) = StackADT.size_stack l1 + StackADT.size_stack l2.
  Proof.
    induction l1; simpl; intros; eauto.
    rewrite IHl1. omega.
  Qed.

  Lemma val_inject_set:
    forall j rs1 rs2 r0 r1
      (RINJ: r0 <> r1 -> Val.inject j (rs1 r0) (rs2 r0))
      v v' (VINJ: Val.inject j v v'),
      Val.inject j ((rs1 # r1 <- v) r0) ((rs2 # r1 <- v') r0).
  Proof.
    intros.
    destruct (PregEq.eq r1 r0); subst; auto.
    rewrite ! Pregmap.gss; auto.
    rewrite ! Pregmap.gso by auto. auto.
  Qed.

  Lemma val_inject_undef_regs:
    forall l j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      r,
      Val.inject j (undef_regs l rs1 r) (undef_regs l rs2 r).
  Proof.
    induction l; simpl; intros; eauto.
    apply IHl.
    intros; apply val_inject_set; auto.
  Qed.

  Lemma val_inject_nextinstr:
    forall j rs1 rs2 r
      (RINJ: forall r0, r0 = r \/ r0 = PC -> Val.inject j (rs1 r0) (rs2 r0)),
      Val.inject j (nextinstr rs1 r) (nextinstr rs2 r).
  Proof.
    unfold nextinstr.
    intros.
    apply val_inject_set; auto. 
    apply Val.offset_ptr_inject; auto.
  Qed.

  Lemma find_var_info_none_ge:
    forall b,
      (Genv.genv_next ge <= b)%positive ->
      Genv.find_var_info ge b = None.
  Proof.
    unfold Genv.find_var_info. intros.
    destr.
    apply Genv.genv_defs_range in Heqo. xomega.
  Qed.

  Lemma load_record_stack_blocks:
    forall m fi m',
      Mem.record_stack_blocks m fi = Some m' ->
      forall chunk b ofs,
        Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
  Proof.
    intros.
    destruct (plt b (Mem.nextblock m)).
    eapply Mem.load_unchanged_on_1.
    eapply Mem.strong_unchanged_on_weak.
    eapply Mem.record_stack_block_unchanged_on; eauto.
    apply p.
    instantiate (1 := fun _ _ => True); simpl; auto.
    destruct (Mem.load chunk m b ofs) eqn:LOAD.
    apply Mem.load_valid_access in LOAD. destruct LOAD.
    exfalso; apply n.
    eapply Mem.perm_valid_block. apply H0.
    instantiate (1:= ofs). generalize (size_chunk_pos chunk); omega.
    clear LOAD.
    destruct (Mem.load chunk m' b ofs) eqn:LOAD; auto.
    apply Mem.load_valid_access in LOAD. destruct LOAD.
    exfalso; apply n.
    eapply Mem.perm_valid_block.
    specialize (H0 ofs). trim H0. generalize (size_chunk_pos chunk); omega.
    rewrite_perms_bw H0.
    apply H0.
  Qed.

(*  Lemma alloc_inject:
    forall j ostack m1 (rs1 rs1': regset) fi b m1' m5 ofs_ra m2 m4,
      (* (frame_link fi = fl::nil) -> *)
      match_states j (Ptrofs.unsigned ostack) (State rs1 m1) (State rs1' m1') ->
      (* Mem.push_frame m1 fi ((Mptr, Ptrofs.repr ofs_ra, rs1#RA)::nil) = Some (m5,b) -> *)
      Mem.alloc m1 0 (frame_size fi) = (m2, b) ->
      (* Mem.store Mptr m2 b (seg_ofs fl) rs1#RSP = Some m3 -> *)
      Mem.store Mptr m2 b ofs_ra rs1#RA = Some m4 ->
      Mem.record_stack_blocks m4 (make_singleton_frame_adt' b  fi (frame_size fi)) = Some m5 ->
      (* 0 <= seg_ofs fl <= Ptrofs.max_unsigned -> *)
      0 <= ofs_ra <= Ptrofs.max_unsigned ->
      0 <= frame_size fi ->
      let curofs := current_offset (rs1' # RSP) in
      let newostack := offset_after_alloc curofs fi in
      let rs2 := nextinstr ( rs1 #RAX <- (rs1#RSP)  #RSP <- (Vptr b Ptrofs.zero)) in
      let rs2' := nextinstr (rs1' #RAX <- (rs1'#RSP) #RSP <- (Vptr bstack (Ptrofs.repr newostack))) in
      exists j',
        (forall bb, j' bb = if peq bb b then Some (bstack, newostack) else j bb) 
        /\ inject_incr j j'
        (* /\ exists m3', *)
        (*     Mem.storev Mptr m1' (Val.offset_ptr (Vptr bstack (Ptrofs.repr newostack)) (Ptrofs.repr (seg_ofs fl))) rs1'#RSP = Some m3' *)
            /\
            exists m4',
              Mem.storev Mptr m1' (Val.offset_ptr (Vptr bstack (Ptrofs.repr newostack)) (Ptrofs.repr ofs_ra)) rs1'#RA = Some m4'
              /\ match_states j' newostack (State rs2 m5) (State rs2' m4').
  Proof.
    intros j ostack m1 rs1 rs1' fi b m1' m5 ofs_ra m2 m4
           MS ALLOC STORE RSB REPRretaddr sizepos
           curofs newostack rs2 rs2'.
    inv MS.
    assert (RSPDEC: (rs1' RSP = Vptr bstack ostack0 /\ curofs = Ptrofs.unsigned ostack0)
                    \/ (~ is_ptr (rs1' RSP) /\ curofs = Mem.stack_limit /\ Mem.stack_adt m1 = nil)).
    {
      destruct (is_ptr_dec (rs1' RSP)).
      left; destruct (rs1' RSP) eqn:?; simpl in *; try easy.
      specialize (RSPEQ _ _ eq_refl).
      intuition subst. auto. reflexivity.
      right. split; auto.
      split; auto.
      destruct (rs1' RSP) eqn:?; simpl in *; try easy.
      generalize (RINJ RSP).
      repeat destr_in AGSP1.
      rewrite H0. inversion 1. rewrite <- H4 in n. simpl in n; easy.
    }
    assert (REPRcur: align (Z.max 0 (frame_size fi)) 8 <= curofs <= Ptrofs.max_unsigned).
    {
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      generalize (Mem.size_stack_below m5).
      repeat rewrite_stack_blocks.
      revert EQ1; repeat rewrite_stack_blocks. intro. simpl.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.
      unfold curofs, current_offset. rewrite EQRSP. erewrite AGSP; eauto.
      generalize (size_stack_pos (Mem.stack_adt m1)); rewrite EQ1; simpl; intros.
      generalize (Mem.stack_limit_range). intros. split. 2: omega.
      
      generalize (size_stack_pos r). 
      rewrite Z.max_r.
      omega.
      rewrite EQ, NIL. simpl.
      generalize (Mem.stack_limit_range).
      omega.
    }
    assert (REPR: 0 <= newostack <= Ptrofs.max_unsigned).
    {
      unfold newostack.
      unfold offset_after_alloc.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      omega.
    }
    generalize (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ _ newostack MINJ ALLOC VB).
    intro A.
    trim A. now omega.
    trim A. intros; right; eapply PBS; now eauto.
    trim A.
    {
      intros; eapply Mem.perm_implies. eapply PBSL; eauto.
      split. omega.
      unfold newostack, offset_after_alloc.
      eapply Z.lt_le_trans with curofs.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      rewrite Z.max_r by omega. omega.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst. 
      rewrite H2. erewrite (AGSP _ EQRSP); eauto.
      generalize (size_stack_pos (Mem.stack_adt m1)); intros. omega. omega. 
      simpl in H0.
      auto.
    }
    trim A.
    {
      red.
      intros.
      unfold newostack, offset_after_alloc.
      eapply Zdivides_trans with 8.
      destruct chunk; try (exists 8; reflexivity);
        try (exists 4; reflexivity);
        try (exists 2; reflexivity);
        try (exists 1; reflexivity).
      apply Z.divide_sub_r.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst. 
      rewrite H0. apply SPAL; auto.
      rewrite EQ. apply Mem.stack_limit_aligned.
      apply align_divides. omega.
    }
    trim A.
    {
      intros b0 delta' ofs k p JB PERM RNG.
      generalize (NIB _ _ _ _ _ JB PERM).
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst. 
      rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ.
      generalize (align_le (frame_size fi) 8).
      unfold newostack, offset_after_alloc in RNG.
      rewrite Z.max_r in RNG by omega. simpl in RNG. omega.
      rewrite NIL in *. simpl. tauto. 
    }
    trim A.
    {
      revert NS. unfold no_stack. intros (fr & fi0 & EQS & BLOCKS & ZERO & PUBLIC & SIZE). rewrite EQS.
      simpl. intros f2 fi1 [?|[]]; subst. rewrite <- BLOCKS.
      intros [|[]]. inv H.
      intros; apply PUBLIC.
    }
    destruct A as (f' & MINJ' & INCR & EQ1 & EQ2).
    exists f'.
    split.
    {
      intros.
      destruct peq; subst; eauto.
    }
    split; auto.
    (* (* store parent *) *)
    (* exploit Mem.store_mapped_inject. apply MINJ'. simpl in *; eauto. eauto. *)
    (* eapply val_inject_incr; eauto. intros (m3' & STORE & MINJ2). *)
    (* simpl. *)
    (* assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr newostack) (Ptrofs.repr (seg_ofs fl))) = *)
    (*         seg_ofs fl + newostack) as EQ. *)
    (* 2: rewrite EQ, STORE. *)
    (* rewrite Ptrofs.add_commut. erewrite Mem.address_inject; eauto. rewrite Ptrofs.unsigned_repr. omega. omega. *)
    (* exploit Mem.store_valid_access_3. exact STORE_PARENT.  *)
    (* intro VA; eapply Mem.store_valid_access_1 in VA; eauto. destruct VA. *)
    (* eapply H. rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); omega. *)
    (* eexists; split; eauto. *)
    (* store return address *)
    exploit Mem.store_mapped_inject. apply MINJ'. simpl in *; eauto. eauto. 
    eapply val_inject_incr; eauto. intros (m4' & STORE' & MINJ3).
    assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr newostack) (Ptrofs.repr ofs_ra)) =
            ofs_ra + newostack) as EQ'.
    2: simpl. 
    rewrite Ptrofs.add_commut.
    erewrite Mem.address_inject; eauto.
    rewrite Ptrofs.unsigned_repr; omega.
    exploit Mem.store_valid_access_3. exact Heqo.
    intro VA; eapply Mem.store_valid_access_1 in VA; eauto. destruct VA.
    eapply H. 
    rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); omega.
    unfold Ptrofs.add.
    rewrite (Ptrofs.unsigned_repr _ REPR).
    rewrite (Ptrofs.unsigned_repr _ REPRretaddr) in *.
    rewrite Ptrofs.unsigned_repr. rewrite Z.add_comm. rewrite STORE'.
    eexists; split; eauto.
    (* record the stack block *)
    destruct NS as (frstack & fstack & EQstk & BLOCKS & ZERO & PUB & SZ).
    exploit Mem.record_stack_block_inject_left_zero. apply MINJ3. 6: eauto.
    repeat rewrite_stack_blocks. rewrite EQstk. constructor; reflexivity.
    {
      red. red. simpl. constructor; auto. simpl. rewrite EQ1.
      intros b2 delta A; inv A.
      rewrite <- BLOCKS. simpl. rewrite peq_true.
      eexists; split. eauto.
      constructor.
      intros; eapply stack_perm_le_public. intros; apply PUB.
      intros; rewrite SZ.
      unfold newostack, offset_after_alloc.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ3 NIL]]]; subst. 
      rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ.
      rewrite H0.
      * red in AGSP. apply AGSP in EQRSP.  rewrite EQRSP.
        cut (o - size_stack (Mem.stack_adt m1) - align (Z.max 0 (frame_size fi)) 8 < 0). omega.
        generalize (size_stack_pos (Mem.stack_adt m1)).
        cut (o - align (Z.max 0 (frame_size fi)) 8 < 0). omega.
        cut (o < align (Z.max 0 (frame_size fi)) 8). omega.
        eapply Z.lt_le_trans.
        2: apply align_le. 2: omega. rewrite Z.max_r. omega. omega.
      * rewrite EQ3.
        cut (o < align (Z.max 0 (frame_size fi)) 8). omega.
        eapply Z.lt_le_trans.
        2: apply align_le. 2: omega. rewrite Z.max_r. omega. omega.
    }
    {
      repeat rewrite_stack_blocks.
      auto.
    }
    { repeat rewrite_stack_blocks. rewrite EQstk. constructor; auto. 
    } 
    simpl; auto.
    intro H.
    (* proving the final match_states *)
    rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
    econstructor; eauto.
    - eapply Mem.mem_inject_ext. eauto. simpl; intros.
      repeat rewrite_stack_blocks. simpl. destr. subst. simpl. auto.
      destr. destr.  omega. destr. omega.
    - intros b0 o A. unfold rs2 in A.
      rewrite nextinstr_rsp in A.
      rewrite Pregmap.gss in A. inv A; auto.
    - intros r.
      unfold rs2, rs2'.
      destruct (PregEq.eq r RSP).
      + subst. rewrite ! nextinstr_rsp. rewrite ! Pregmap.gss.
        econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
      + apply val_inject_nextinstr. intros.
        assert (r0 <> RSP) by intuition congruence.
        rewrite ! (Pregmap.gso _ _ H2) by auto.
        eapply val_inject_set; eauto.
    - eapply Mem.store_valid_block_1. eauto.
      eauto.
    - red. unfold rs2'. rewrite nextinstr_rsp. rewrite Pregmap.gss. inversion 1. subst.
      repeat rewrite_stack_blocks.
      rewrite Ptrofs.unsigned_repr by auto.
      unfold newostack, offset_after_alloc in *.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst. 
      rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ.
      rewrite H2. rewrite (AGSP _ EQRSP).
      simpl. omega.
      rewrite EQRSP, NIL in *. simpl. omega.
    - rewrite_stack_blocks. 
      unfold rs2. rewrite nextinstr_rsp. apply Pregmap.gss.
    - repeat rewrite_stack_blocks. constructor; auto.
    - red. intros ostack1 A. unfold rs2' in A. rewrite nextinstr_rsp in A. rewrite Pregmap.gss in A.
      inversion A. subst.
      rewrite Ptrofs.unsigned_repr by omega.
      unfold newostack.
      apply Z.divide_sub_r.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst. 
      rewrite H0; apply SPAL; auto.
      rewrite EQRSP. apply Mem.stack_limit_aligned.
      apply align_divides. omega.
    - red. intros ofs k p PERM.
      repeat rewrite_perms_bw PERM. eauto.
    - red; intros.
      repeat rewrite_perms_fw. eauto.
    - red. repeat rewrite_stack_blocks. exists frstack, fstack; rewrite EQstk, <- BLOCKS, <- ZERO. eauto.
    - unfold rs2'. rewrite nextinstr_rsp, Pregmap.gss. inversion 1. eauto.
    - rewrite Ptrofs.unsigned_repr by omega.
      red. intros b0 delta o k p JB PERM.
      repeat rewrite_perms_bw PERM.
      destruct peq.
      * subst. rewrite EQ1 in JB. inv JB. split. omega.
        rewrite_stack_blocks. simpl. unfold in_frame; simpl; auto.
      * split. unfold newostack, offset_after_alloc.
        transitivity curofs.
        -- generalize (Z.le_max_l 0 (frame_size fi)); intro MAX.
           generalize (align_le (Z.max 0 (frame_size fi)) 8). omega.
        -- 
          destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst. 
          rewrite H0. 
          rewrite EQ2 in JB; auto. 
          exploit NIB; eauto. tauto.
          exploit NIB; eauto. rewrite <- EQ2. eauto. auto. 
          rewrite NIL. simpl; tauto.
        -- repeat rewrite_stack_blocks. simpl; auto.
           right.
           eapply NIB; eauto. rewrite <- EQ2; eauto.
    - repeat rewrite_stack_blocks.
      econstructor; eauto.
      + eapply inject_stack_incr; eauto.
      + rewrite EQ1. f_equal. f_equal.
        unfold newostack, offset_after_alloc.
        destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst.
        instantiate (1:=fi).
        rewrite e.
        rewrite AGSP. omega. auto. rewrite EQRSP, NIL. simpl; omega.
      + reflexivity.
      + reflexivity.
    - intros b0 fi0 delta GFI FB0 b' o delta' k p FB1 P1.
      unfold get_frame_info in GFI.
      revert GFI. repeat rewrite_stack_blocks. intro GFI.
      simpl in GFI.
      repeat rewrite_perms_bw P1. 
      destr_in GFI.
      + destr_in GFI. subst. inv GFI. rewrite FB0 in EQ1; inv EQ1.
        destr_in P1.
        * subst. rewrite FB0 in FB1; inv FB1.
          rewrite Z.max_r by omega.  omega.
        * rewrite EQ2 in FB1 by auto.
          eapply NIB in P1; eauto.
          destruct P1 as (LE & IN).
          unfold newostack, offset_after_alloc.
          destruct (RSPDEC) as [[EQRSP EQA]|[NOPTR [EQA NIL]]]; subst; rewrite EQA.
          omega. rewrite NIL in IN; easy.
      + unfold make_singleton_frame_adt', in_frame in n.
        simpl in n.
        rewrite EQ2 in FB0 by auto.
        intro RNG.
        assert (0 < frame_size fi0).
        destruct (zlt 0 (frame_size fi0)); auto.
        rewrite Z.max_l in RNG by omega. change (align 0 8) with 0 in RNG. omega.
        rewrite Z.max_r in RNG by omega.
        destruct (RSPDEC) as [[EQRSP EQA]|[NOPTR [EQA NIL]]]; subst; rewrite EQA, ?NIL in *; try easy.
        generalize (perm_stack_eq _ _ _ _ PS GFI). intro PF0. 
        destr_in P1.
        * subst. rewrite EQ1 in FB1; inv FB1.
          cut (newostack + (frame_size fi)  <= delta). omega.
          unfold newostack. rewrite EQA.
          rewrite AGSP; auto.
          eapply in_stack_inj_below in GFI; eauto.
          destruct GFI as (l1 & l2 & EQADT & JB0). rewrite FB0 in JB0. inv JB0.
          rewrite Z.max_r in * by omega.
          unfold offset_after_alloc.
          rewrite Z.max_r by omega.
          cut (StackADT.size_stack (Mem.stack_adt m1) 
               >= StackADT.size_stack l2).
          generalize (align_le (frame_size fi) 8). omega.
          rewrite EQADT.
          rewrite size_stack_app.
          generalize (size_stack_pos l1); omega.
        * eapply IP.  apply GFI. eauto.
          rewrite <- EQ2. apply FB1. auto. eauto.
          rewrite Z.max_r by omega. omega.
    - repeat rewrite_stack_blocks. 
      econstructor; eauto.
      + eapply perm_stack_inv. eauto. apply Mem.in_frames_valid.
        split; intros.
        * repeat rewrite_perms_bw H2.
          destr_in H2.
          subst.
          eapply Mem.in_frames_valid in H0.
          eapply Mem.fresh_block_alloc in H0. easy.
          eauto.
        * repeat rewrite_perms_fw. auto.
      + split; intros.
        * repeat rewrite_perms_bw H0.
          rewrite pred_dec_true in H0; eauto.
        * do 2 rewrite_perms_fw. eapply Mem.perm_implies. eapply Mem.perm_alloc_2. eauto. eauto.
          constructor.
      + inv PS. simpl. easy.
        intros b' [A|A].
        * eapply Plt_Ple_trans. apply Mem.in_frames_valid. rewrite <- H0. left; auto. 
          erewrite Mem.alloc_result. 2: eauto. xomega.
        * eapply H4 in A; eauto. eapply Plt_trans. eauto.
          eapply Plt_Ple_trans. apply Mem.in_frames_valid. rewrite <- H0. left.
          red. rewrite H5. left; auto. 
          erewrite Mem.alloc_result. 2: eauto. xomega.
      + reflexivity.
    - destruct GLOBSYMB_INJ; split.
      + intros. eapply INCR. eauto.
      + intros. destruct (peq b1 b).
        subst; rewrite EQ1 in H3. inv H3.
        simpl.
        unfold Genv.block_is_volatile.
        unfold Genv.find_var_info.
        replace (Genv.find_def ge bstack) with (None (A:=globdef Asm.fundef unit)).
        replace (Genv.find_def ge b) with (None (A:=globdef Asm.fundef unit)).
        auto.
        unfold Genv.find_def.
        destruct (Maps.PTree.get b (Genv.genv_defs ge)) eqn:EQdef; auto.
        apply Genv.genv_defs_range in EQdef.
        exploit Mem.fresh_block_alloc. eauto. red. xomega. easy.
        unfold Genv.find_def.
        destruct (Maps.PTree.get bstack (Genv.genv_defs ge)) eqn:EQdef; auto.
        apply Genv.genv_defs_range in EQdef.
        unfold bstack in EQdef. xomega.
        rewrite EQ2 in H3.
        eauto.
        auto.
    - erewrite Mem.record_stack_block_nextblock. 2: eauto.
      erewrite Mem.nextblock_store. 2 : eauto.
      erewrite Mem.nextblock_alloc. 2: eauto. xomega.
    - erewrite Mem.nextblock_store. 2 : eauto. xomega.
    - repeat rewrite_stack_blocks. intros. right. eauto.       
    - rewrite Z.add_comm, <- EQ'. apply Ptrofs.unsigned_range_2.
  Qed.
 *)

  Lemma size_frames_divides f:
    (8 | size_frames f).
  Proof.
    unfold size_frames. induction f; simpl; eauto.
    exists 0; omega.
    rewrite Zmax_spec.
    destr.
    apply align_divides. omega.
  Qed.

  Lemma size_stack_divides l:
    (8 | StackADT.size_stack l).
  Proof.
    induction l; simpl; intros; eauto.
    exists 0; omega.
    apply Z.divide_add_r. auto. apply size_frames_divides; auto.
  Qed.

  (* Lemma inject_stack_all_below: *)
  (*   forall l m, *)
  (*     perm_stack l m -> *)
  (*     forall b b' d, *)
  (*       in_frames ((hd d l)) b -> *)
  (*       in_stack (tl l) b' -> *)
  (*       Plt b' b. *)
  (* Proof. *)
  (*   induction 1; simpl; intros. easy. *)
  (*   rewrite in_frames_cons in H3. *)
  (*   destruct H3. unfold in_frame, get_frame_blocks in H3; rewrite H2 in H3. *)
  (*   simpl in H3. destruct H3 as [|[]]. *)
  (*   subst. eauto. *)
    
  (*   simpl in *; subst. eauto. *)
  (* Qed. *)

  (* Lemma inject_stack_only_once: *)
  (*   forall l m a b, *)
  (*     perm_stack (a::l) m -> *)
  (*     in_frames a b -> *)
  (*     get_assoc_stack l b = None. *)
  (* Proof. *)
  (*   inversion 1; subst. *)
  (*   rewrite in_frames_cons. *)
  (*   unfold in_frame, get_frame_blocks. rewrite H6. simpl. intros [[|[]]|]; subst. *)
  (*   rewrite not_in_stack_get_assoc; auto. *)
  (*   intro INF. *)
  (*   apply H4 in INF. xomega. *)
    
  (* Qed. *)

  (* Lemma inject_stack_norepeat: *)
  (*   forall l m a b, *)
  (*     perm_stack (a::l) m -> *)
  (*     in_frame (a) b -> *)
  (*     ~ in_frames l b. *)
  (* Proof. *)
  (*   inversion 1; subst. *)
  (*   unfold in_frame. rewrite H6. simpl. intros [?|[]]. *)
  (*   subst. intro INF; apply H4 in INF.  xomega.  *)
  (* Qed. *)

  Lemma inject_stack_init_sp:
    forall j l,
      inject_stack j l ->
      forall b,
        in_stack l b ->
        exists o,
          j b = Some (bstack, o).
  Proof.
    induction 1; simpl; intros b INS. easy.
    rewrite in_stack_cons in INS. destruct INS as [INF|INS].
    - edestruct in_frames_in_frame_ex as (fr & INTF & IFR). eauto.
      destruct (H0 _ INTF) as (bb & fi & JB & BLOCKS & SIZE).
      rewrite JB.
      red in H3. ; rewrite H1 in H3; simpl in H3; destruct H3 as [|[]]; subst. eauto.
    eauto.
  Qed.

  Lemma init_sp_inj:
    forall j l,
      inject_stack j l ->
      in_stack l binit_sp ->
      exists o,
        Val.inject j init_sp (Vptr bstack o).
  Proof.
    intros. edestruct inject_stack_init_sp; eauto.
    unfold init_sp. exists (Ptrofs.repr x).
    econstructor; eauto. rewrite Ptrofs.add_zero_l. auto.
  Qed.


  Ltac use_ains :=
    repeat match goal with
           | AINS: asm_instr_no_stack ?i,
                   UNC: is_unchanged ?i = true,
                        EI: Asm.exec_instr ?isp _ _ ?i _ ?m1 = Next _ ?m2 |-
             context [Mem.stack_adt ?m2] =>
             let AINS_stack := fresh "AINS_stack" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (AINS_stack & _); rewrite ! AINS_stack;
             clear AINS_stack
           | AINS: asm_instr_no_stack ?i,
                   UNC: is_unchanged ?i = true,
                        EI: Asm.exec_instr ?isp _ _ ?i _ ?m1 = Next _ ?m2,
                            H: context [Mem.stack_adt ?m2] |- _ =>
             let AINS_stack := fresh "AINS_stack" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (AINS_stack & _); rewrite ! AINS_stack in H;
             clear AINS_stack

           | AINS: asm_instr_no_stack ?i,
                   UNC: is_unchanged ?i = true,
                        EI: Asm.exec_instr _ _ _ ?i _ ?m1 = Next _ ?m2 |-
             context [Mem.perm ?m2 _ _ _ _] =>
             let AINS_perm := fresh "AINS_perm" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (_ & AINS_perm); rewrite ! AINS_perm;
             clear AINS_perm
           | AINS: asm_instr_no_stack ?i,
                   UNC: is_unchanged ?i = true,
                        EI: Asm.exec_instr _ _ _ ?i _ ?m1 = Next _ ?m2,
                            H : context [Mem.perm ?m2 _ _ _ _] |- _ =>
             let AINS_perm := fresh "AINS_perm" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (_ & AINS_perm); rewrite ! AINS_perm in H;
             clear AINS_perm
           | AINR: asm_instr_no_rsp ?i,
                   UNC: is_unchanged ?i = true,
                        EI: Asm.exec_instr ?isp _ _ ?i ?rs1 _ = Next ?rs2 _ |-
             context [?rs2 (IR RSP)] =>
             rewrite (AINR UNC _ _ _ _ _ _ _ _ _ EI)
           | AINR: asm_instr_no_rsp ?i,
                   UNC: is_unchanged ?i = true,
                        EI: Asm.exec_instr ?isp _ _ ?i ?rs1 _ = Next ?rs2 _,
                            H: context [?rs2 (IR RSP)] |- _ =>
             rewrite (AINR UNC _ _ _ _ _ _ _ _ _ EI) in H
                                                          
           end.

  Lemma exec_instr_inject':
    forall j ostack m1 m2 rs1 rs2 f i rs1' m1'
      (MS: match_states j ostack (State rs1 m1) (State rs2 m2))
      (AINR: asm_instr_no_rsp i)
      (AINS: asm_instr_no_stack i)
      (EI: Asm.exec_instr init_sp ge f i rs1 m1 = Next rs1' m1'),
      exists j' ostack' rs2' m2',
        exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ match_states j' ostack' (State rs1' m1') (State rs2' m2')
        /\ inject_incr j j'.

    intros. 
    destruct (is_unchanged i) eqn:ISUNCH.
    - edestruct init_sp_inj as (oinit & INJinit); eauto.
        inv MS; eauto.
        inv MS; eapply SPinstack; eauto. reflexivity.
      edestruct exec_instr_inject as (rs2' & m2' & EXEC' & MINJ' & RINJ'); eauto.
        inv MS; eauto.
        inv MS; eauto.
      exists j, ostack, rs2', m2'; split; [|split]; eauto.
      destruct i; simpl in *; eauto; try congruence.
      inv MS; econstructor; eauto; try now ((intros; use_ains; eauto) || (red; intros; use_ains; eauto)).
      + eapply asmgen_nextblock_forward in EXEC'.
        red in VB |- *. xomega.
      + use_ains.
        eapply perm_stack_inv. eauto. apply Mem.in_frames_valid.
        intros; use_ains. tauto.
      + etransitivity. apply GlobLe.
        eapply asmgen_nextblock_forward; eauto.
      + etransitivity. apply GlobLeT.
        eapply asmgen_nextblock_forward; eauto.

    - destruct i; simpl in *; try congruence.
      + (* allocframe *)
        destruct (check_alloc_frame frame) eqn:CAF; try congruence.
        unfold check_alloc_frame in CAF.
        clear ISUNCH.
        destruct zle; try congruence.
        repeat destr_in EI.
        inversion MS; subst.
        edestruct alloc_inject as (j' & JSPEC & INCR & m4' & STORE2 & MS') ; eauto.
        instantiate (3 := Ptrofs.unsigned ofs_ra).
        rewrite Ptrofs.repr_unsigned. eauto.
        apply Ptrofs.unsigned_range_2.
        simpl in *.
        rewrite Ptrofs.repr_unsigned in STORE2. rewrite STORE2.
        set (newostack := offset_after_alloc (current_offset (rs2 RSP)) frame).
        fold newostack in STORE2, JSPEC, MS'.
        exists j',  newostack; eexists; eexists; split; eauto.
      + repeat (destr_in EI; [idtac]). inv EI. clear ISUNCH.
        rename Heqv0 into RS1RSP.
        rename Heqo into LOADRA.
        rename Heqb0 into CHECKFRAME.
        rename Heqo0 into FREE.
        rename Heqo1 into UNRECORD.
        inv MS.
        specialize (RSPzero _ _ RS1RSP). subst.
        exploit Mem.loadv_inject. eauto. apply LOADRA.
        apply Val.offset_ptr_inject. rewrite <- RS1RSP; auto.
        intros (ra' & LOADRA' & INJra).
        rewrite LOADRA'.
        unfold check_top_frame in CHECKFRAME.
        repeat destr_in CHECKFRAME.
        repeat destr_in AGSP1.
        repeat rewrite andb_true_iff in H0.
        destruct H0 as (A & B).
        destruct Forall_dec; simpl in A; try congruence. clear A.
        inv f2. destruct H2 as (A & C). subst. simpl in *.
        apply ZEQ in B. 
        set (newostack := Ptrofs.unsigned ostack0 + align (Z.max 0 (frame_size f1)) 8).
        exploit free_inject; eauto.
        {
          inversion PS as [|? ? ? ? ? PS' PERMeq ]; subst.
          rewrite Heql0 in H0. inv H0.
          intros o k p PERM. rewrite <- PERMeq; eauto.
        }
        {
          erewrite Mem.free_stack_blocks; eauto. rewrite Heql.
          unfold is_stack_top. simpl. rewrite Heql0. intros ? [?|[]]. auto.
        }
        {
          simpl. destr.
          exfalso; apply n.
          destruct l; simpl. 2: omega.
          exfalso.
          unfold proj_sumbool in Heqb1. destr_in Heqb1.
          revert i. repeat rewrite_stack_blocks. rewrite Heql. simpl. easy.
        }
        {
          destruct NS as (f0' & fr & EQ & ?). simpl. rewrite EQ. reflexivity.
        }
        intros INJ. 
        exists j, newostack; eexists; eexists; split; [|split]; eauto.
        generalize (RINJ RSP). rewrite RS1RSP.
        inversion 1 as [ff|ff|ff|ff|? ? ? ? ? INJB ? x EQRSP|ff]; subst.
        symmetry in EQRSP.
        rewrite Ptrofs.add_zero_l in *.
        exploit RSPEQ. eauto. intros (AA & BB). subst.
        specialize (AGSP _ EQRSP).
        specialize (SPAL _ EQRSP).
        generalize (Mem.unrecord_stack_adt _ _ UNRECORD).
        erewrite Mem.free_stack_blocks. 2: eauto. rewrite Heql. intros (bb0 & EQ).
        inv EQ.
        assert (0 <= Mem.stack_limit - StackADT.size_stack (Mem.stack_adt m1') <= Ptrofs.max_unsigned) as RNGnewofs. 
        {
          generalize (Mem.size_stack_below m1').
          generalize (size_stack_pos (Mem.stack_adt m1')).
          generalize (Mem.stack_limit_range).
          omega.
        }
        assert (0 <= newostack <= Ptrofs.max_unsigned) as RNGnew.
        {
          unfold newostack.
          rewrite AGSP. rewrite Heql. simpl. rewrite B. omega.
        }
        rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
        econstructor; eauto.
        * eapply Mem.mem_inject_ext. eauto.
          simpl. intros. repeat destr; omega.
        * intros b o NI. rewrite nextinstr_rsp in NI. rewrite Pregmap.gso in NI by congruence.
          rewrite Pregmap.gss in NI. subst. 
          repeat destr_in NI. auto.
        * intros; apply val_inject_nextinstr.
          intros; apply val_inject_set; auto.
          intros; apply val_inject_set; auto.
          unfold parent_pointer; rewrite Heql.
          inv IS. inv H6.
          {
            (* impossible: init_sp is in the stack *)
            destruct in_frames_dec; simpl in Heqb1; try congruence.
            rewrite <- H8 in i. simpl in i. easy.
          }
          {
            rewrite H11. econstructor. eauto. rewrite Ptrofs.add_zero_l. f_equal.
            unfold current_offset. rewrite AGSP.
            unfold offset_after_free. rewrite Heql. simpl. rewrite <- H4. simpl.
            rewrite H13. rewrite B. omega.
          }
        (* * red. rewrite nextinstr_rsp. rewrite ; edestruct Mem.unrecord_stack_block_mem_unchanged. simpl ; apply USB. *)
        (*   rewrite H0; eauto. *)
        * red. rewrite nextinstr_rsp.
          rewrite ! Pregmap.gso by congruence.
          rewrite Pregmap.gss. intros; subst.
          inv H0. rewrite AGSP. rewrite Heql. simpl.
          rewrite Ptrofs.unsigned_repr. unfold offset_after_free. rewrite B; omega.
          unfold offset_after_free. rewrite B; omega. 
        * unfold parent_pointer. rewrite Heql.
          inv PS. 
          rewrite nextinstr_rsp. rewrite Pregmap.gso by congruence.
          inv H4; auto.
          rewrite H10. auto.
        * inv SZpos.  auto.
        * red. rewrite nextinstr_rsp. 
          rewrite ! Pregmap.gso by congruence.
          rewrite Pregmap.gss. inversion 1. subst. clear H0.
          (* inv LRSP. rewrite <- H4 in *. destr_in Heqb0; inv INJ3. *)
          (* rewrite <- H4 in *. inv INJ3. *)
          unfold offset_after_free.
          rewrite Ptrofs.unsigned_repr. rewrite AGSP. rewrite Heql. simpl.
          eapply Z.divide_trans with (Mem.stack_limit - size_stack (Mem.stack_adt m1')).
          apply Z.divide_sub_r.
          apply Mem.stack_limit_aligned.
          apply size_stack_divides. rewrite <- B. exists 1; omega.
          rewrite AGSP, Heql. simpl. rewrite B. omega. 
        * 
        (* * red. *)
        (*   intros ofs k p PERM. *)
        (*   eapply Mem.unrecord_stack_block_perm in PERM. 2: eauto. eauto. *)
        (* * red. *)
        (*   intros ofs k RNG. *)
        (*   eapply Mem.unrecord_stack_block_perm'. 2: eauto. eauto.                  *)
        (* * red. *)
        (*   edestruct Mem.unrecord_stack_adt. apply USB. red in NS. rewrite H0 in NS. *)
        (*   inv NS; auto. *)
          (* *  *)
          rewrite nextinstr_rsp.
          rewrite ! Pregmap.gso by congruence.
          rewrite Pregmap.gss. 
          inversion 1. subst. clear H0. split; auto.
        * red. intros b' delta0 o k p JB0 PERM.
          eapply Mem.unrecord_stack_block_perm in PERM. 2: eauto.
          erewrite Mem.perm_free in PERM. 2: eauto.
          destruct PERM as (NOTSAME & PERM).
          generalize (NIB b' delta0 o k p JB0 PERM).
          destruct (peq b' b0).
          -- subst.
             inv PS. rewrite Heql0 in H8.  inv H8.
             rename H5 into PERM_in_range.
             apply PERM_in_range in PERM. intuition.
          -- clear NOTSAME.
             rewrite Heql. simpl. 
             intros (LE & OR). destruct OR; try congruence.
             red in H0; simpl in H0. rewrite Heql0 in H0. destruct H0 as [?|[]]; subst.
             simpl in n. congruence.
             split; auto.
             rewrite Ptrofs.unsigned_repr by omega.
             unfold newostack.
             destruct (zle (Ptrofs.unsigned (Ptrofs.repr delta) + align (Z.max 0 (frame_size f1)) 8) (o + delta0)); auto.
             exfalso.
             apply Z.gt_lt in g.
             assert (max_perm: forall m b o k p, Mem.perm m b o k p -> Mem.perm m b o Max Nonempty).
             {
               intros.
               eapply Mem.perm_implies.
               eapply Mem.perm_max. eauto. constructor.
             }
             generalize (Mem.free_range_perm _ _ _ _ _ FREE). intro FP.
             assert (0 < frame_size f1).
             destruct (zlt 0 (frame_size f1)); auto.
             apply Z.ge_le in g0.
             rewrite Z.max_l in g by omega.
             change (align 0 8) with 0 in g. omega.
             generalize (fun pf => Mem.address_inject _ _ _ _ _ Ptrofs.zero _ _ Freeable MINJ (FP _ pf) INJB).
             rewrite Ptrofs.unsigned_zero. rewrite Ptrofs.add_zero_l.  simpl.
             intro UR. trim UR. omega.
             destruct (zlt (o + delta0) (delta + frame_size f1)).
             ++ generalize (fun o2 RNG => Mem.mi_no_overlap _ _ _ _ MINJ b' _ _ _ _ _ o o2 n JB0 INJB (max_perm _ _ _ _ _ PERM) (max_perm _ _ _ _ _ (FP _ RNG))).
                assert (exists o2, 0 <= o2 < frame_size f1 /\ o + delta0 = o2 + delta) as EX.
                {
                  exists (o + delta0 - delta).
                  omega.
                }
                destruct EX as (o2 & RNG & EQ').
                intro CONTRA; edestruct CONTRA; eauto.
             ++ assert (delta + frame_size f1 <= o + delta0 < delta + align (frame_size f1) 8).
                rewrite Z.max_r in g by omega. omega.
                assert (exists o2, frame_size f1 <= o2 < align (frame_size f1) 8 /\ o + delta0 = o2 + delta) as EX.
                {
                  exists (o + delta0 - delta).
                  omega.
                }
                destruct EX as (o2 & RNG & EQ').
                eapply IP. 4: apply PERM.  3: eauto. 2: apply INJB.
                unfold get_frame_info; rewrite Heql.
                simpl. rewrite pred_dec_true; auto.
                rewrite Heql0. simpl. rewrite pred_dec_true. eauto. auto.
                red; rewrite Heql0. left; auto.
                rewrite Z.max_r. omega. omega.
        * 
          inv IS. auto.
        * red; intros b fi delta' GFI JB b2 o delta2 k p JB2 PERM.
          destruct (peq b2 b0).
          -- subst.
             eapply Mem.unrecord_stack_block_perm in PERM. 2: eauto.
             eapply Mem.perm_free_2 in PERM.
             easy. eauto.
             eapply perm_stack_eq. eauto.
             simpl. rewrite Heql0. simpl. rewrite pred_dec_true.
             rewrite pred_dec_true. eauto. reflexivity.
             red; rewrite Heql0. left; auto.
             eapply Mem.perm_free_3. eauto. eauto.
          -- eapply Mem.unrecord_stack_block_perm in PERM. 2: eauto.
             eapply Mem.perm_free_3 in PERM. 2: eauto.
             eapply IP; eauto.
             unfold get_frame_info. rewrite Heql.
             simpl.
             destr.
             rewrite Heql0. red in i. rewrite Heql0 in i.
             destruct i as [|[]]. simpl in H0. subst.
             unfold get_frame_info in GFI.
             erewrite inject_stack_only_once in GFI.
             congruence.
             eauto. red; rewrite Heql0. left; auto. 
        * inv PS. eapply perm_stack_inv; eauto.
          -- intros; eapply Mem.in_frames_valid.
             rewrite Heql; simpl; auto.
          -- intros.
             cut (b0 <> b1).
             ++ intro DIFF.
                split; intros P.
                ** eapply Mem.unrecord_stack_block_perm in P. 2: eauto.
                   eapply Mem.perm_free_3; eauto.
                ** eapply Mem.unrecord_stack_block_perm'. eauto.
                   eapply Mem.perm_free_1; eauto.
             ++ intro; subst.
                eapply inject_stack_norepeat in H0; eauto.
                econstructor; eauto. red; rewrite Heql0. left; auto.
        (* * inversion LRSP. constructor. *)
        (*   rewrite <- H4 in *. *)
        (*   eapply load_rsp_inv'. eauto. *)
        (*   eapply Mem.unchanged_on_trans. *)
        (*   eapply Mem.unchanged_on_implies. *)
        (*   eapply Mem.free_unchanged_on. eauto. *)
        (*   instantiate (1:= fun b0 o => b0 <> b). simpl. congruence. *)
        (*   simpl. *)
        (*   intros.  *)
        (*   intro; subst. *)
        (*   red in H8. destr_in H8. simpl in Heqo3. rewrite pred_dec_false in Heqo3.  *)
        (*   exploit inject_stack_norepeat. apply LRSP. red; simpl. eauto. *)
        (*   simpl. *)
        (*   destruct (in_frames_dec l b); auto. *)
        (*   erewrite not_in_frames_get_assoc in Heqo3; eauto; congruence. auto. *)
        (*   intros [?|[]]; subst. xomega. *)
        (*   eapply Mem.strong_unchanged_on_weak. *)
        (*   eapply Mem.unrecord_stack_block_unchanged_on. *)
        (*   eauto. *)
        * etransitivity. apply GlobLe.
          erewrite <- Mem.nextblock_free. 2: eauto.
          erewrite <- Mem.unrecord_stack_block_nextblock.
          2: eauto. xomega.
        * inversion 1; subst. subst b. 
          destruct in_frames_dec; eauto.
          simpl in *; congruence.
      + unfold parent_pointer, check_top_frame in EI.
        destruct (Mem.stack_adt m1) eqn:S1; try congruence.
        repeat destr_in EI.
        repeat destr_in Heqo.
        repeat destr_in Heqb0.
        apply andb_true_iff in H0; destruct H0 as (A & B).
        apply ZEQ in B. subst.
        destruct Forall_dec; simpl in A; try congruence.
        exists j, ostack; eexists; eexists; split. eauto.
        split; auto.
        inversion MS; subst; constructor; eauto.
        * rewrite nextinstr_rsp.
          destruct (preg_eq RSP rd).
          rewrite e. rewrite Pregmap.gss. inversion 1; auto.
          rewrite Pregmap.gso. eauto. auto.
        * intros; apply val_inject_nextinstr.
          intros; apply val_inject_set; auto. rewrite S1 in *.
          inv IS. inv H2.
          {
            repeat destr_in AGSP1. inv H5.
            rewrite Heql1 in H9. inv H9.
            econstructor. eauto. rewrite Ptrofs.add_zero_l. f_equal.
            unfold current_offset.
            generalize (RINJ RSP). rewrite H1. intro INJSP. inv INJSP.
            rewrite Ptrofs.add_zero_l.
            rewrite AGSP.
            unfold offset_after_free. rewrite S1. simpl.
            rewrite H10.
            omega. rewrite Ptrofs.add_zero_l in H5; auto.
            rewrite <- H5. f_equal.
            symmetry in H5; apply RSPEQ in H5. apply H5.
          }
        * red. rewrite nextinstr_rsp.
          rewrite Pregmap.gso; eauto.
        * rewrite nextinstr_rsp.
          rewrite Pregmap.gso; eauto.
        * red; rewrite nextinstr_rsp.
          rewrite Pregmap.gso; eauto.
        * rewrite nextinstr_rsp.
          rewrite Pregmap.gso; eauto.
  Qed.

  Definition asm_prog_no_rsp (ge: Genv.t Asm.fundef unit):=
    forall b f,
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      asm_code_no_rsp (fn_code f).

  Hypothesis prog_no_rsp: asm_prog_no_rsp ge.


  Context `{ecprops: !ExternalCallsProps mem}.



  Lemma inj_incr_sep_same:
    forall j j' m1 m2 b1 b2 delta,
      inject_incr j j' ->
      inject_separated j j' m1 m2 ->
      j' b1 = Some (b2, delta) ->
      Mem.valid_block m2 b2 ->
      j b1 = Some (b2, delta).
  Proof.
    intros.
    destruct (j b1) eqn:JB.
    destruct p. eapply H in JB; eauto.
    congruence.
    exploit H0; eauto. intuition congruence.
  Qed.

  Lemma set_res_no_rsp:
    forall res vres rs,
      no_rsp_builtin_preg res ->
      set_res res vres rs RSP = rs RSP.
  Proof.
    induction res; simpl.
    - intros. eapply Pregmap.gso. auto.
    - auto.
    - intros vres rs (NR1 & NR2).
      rewrite IHres2; auto.
  Qed.

  Lemma val_inject_set_res:
    forall r rs1 rs2 v1 v2 j,
      Val.inject j v1 v2 ->
      (forall r0, Val.inject j (rs1 r0) (rs2 r0)) ->
      forall r0, Val.inject j (set_res r v1 rs1 r0) (set_res r v2 rs2 r0).
  Proof.
    induction r; simpl; intros; auto.
    apply val_inject_set; auto.
    eapply IHr2; eauto.
    apply Val.loword_inject. auto.
    intros; eapply IHr1; eauto.
    apply Val.hiword_inject. auto.
  Qed.

  Definition init_data_diff (id: init_data) (i: ident) :=
    match id with
      Init_addrof ii _ => ii <> i
    | _ => True
    end.

  Lemma store_init_data_eq:
    forall F V m (ge: _ F V) id gv b o i,
      init_data_diff i id ->
      Genv.store_init_data (Genv.add_global ge (id,gv)) m b o i =
      Genv.store_init_data ge m b o i.
  Proof.
    destruct i; simpl; intros; auto.
    unfold Genv.find_symbol; simpl. 
    rewrite Maps.PTree.gso; auto.
  Qed.

  Lemma store_init_data_list_eq:
    forall F V id i, 
      Forall (fun x => init_data_diff x id) i ->
      forall m (ge: _ F V) gv b o,
        Genv.store_init_data_list (Genv.add_global ge (id,gv)) m b o i =
        Genv.store_init_data_list ge m b o i.
  Proof.
    induction 1; simpl; intros; auto.
    rewrite store_init_data_eq; auto.
    destr. 
  Qed.

  Lemma alloc_global_eq:
    forall F V (l: (ident * option (globdef F V))) m (ge: _ F V) id gv,
      (forall v, snd l = Some (Gvar v) -> Forall (fun x => init_data_diff x id) (gvar_init v)) ->
      Genv.alloc_global (Genv.add_global ge (id,gv)) m l =
      Genv.alloc_global ge m l .
  Proof.
    destruct l; simpl; intros.
    repeat (destr; [idtac]).
    rewrite store_init_data_list_eq. auto.
    apply H; auto.
  Qed.

  Lemma alloc_globals_eq:
    forall F V (l: list (ident * option (globdef F V))) m (ge: _ F V) id gv,
      (forall x v, In x l -> snd x = Some (Gvar v) -> Forall (fun x => init_data_diff x id) (gvar_init v)) ->
      Genv.alloc_globals (Genv.add_global ge (id,gv)) m l =
      Genv.alloc_globals ge m l .
  Proof.
    induction l; simpl; intros; eauto.
    rewrite alloc_global_eq. destr.
    apply IHl. intros; eauto.
    eauto.
  Qed.

  Lemma find_symbol_add_globals_other:
    forall F V l (ge: _ F V) s,
      ~ In s (map fst l) ->
      Genv.find_symbol (Genv.add_globals ge l) s =
      Genv.find_symbol ge s.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite IHl.
    unfold Genv.find_symbol; simpl.
    apply Maps.PTree.gso. intuition. intuition.
  Qed.


  Lemma find_symbol_add_global_other:
    forall F V l (ge: _ F V) s,
      s <> fst l ->
      Genv.find_symbol (Genv.add_global ge l) s =
      Genv.find_symbol ge s.
  Proof.
    destruct l; simpl; intros; eauto.
    unfold Genv.find_symbol; simpl.
    apply Maps.PTree.gso. intuition. 
  Qed.

  Lemma find_symbol_none_add_global:
    forall F V (ge: Genv.t F V) a i,
      Genv.find_symbol (Genv.add_global ge a) i = None ->
      i <> fst a /\ Genv.find_symbol ge i = None.
  Proof.
    unfold Genv.find_symbol; simpl.
    intros F V ge0 a i.
    rewrite Maps.PTree.gsspec.
    destr.
  Qed.

  Lemma find_symbol_none_add_globals:
    forall F V a (ge: Genv.t F V) i,
      Genv.find_symbol (Genv.add_globals ge a) i = None ->
      ~ In i (map fst a) /\ Genv.find_symbol ge i = None.
  Proof.
    induction a; simpl; intros; eauto.
    apply IHa in H.
    destruct H as (H1 & H).
    apply find_symbol_none_add_global in H; auto.
    intuition.
  Qed.

  Lemma find_symbol_none_not_in_defs:
    forall F V (p: program F V) i,
      Genv.find_symbol (Genv.globalenv p) i = None ->
      ~ In i (map fst (prog_defs p)).
  Proof.
    unfold Genv.globalenv.
    intros F V p.
    generalize (Genv.empty_genv F V (prog_public p)).
    generalize (prog_defs p).
    induction l; simpl; intros; eauto.
    apply find_symbol_none_add_globals in H.
    destruct H as (A & B).
    apply find_symbol_none_add_global in B.
    destruct B as (B & C).
    intuition.    
  Qed.

 


  Lemma extcall_arg_inject:
    forall j g rs1 m1 arg1 loc rs2 m2,
      extcall_arg rs1 m1 loc arg1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j g m1 m2 ->
      exists arg2,
        extcall_arg rs2 m2 loc arg2 /\
        Val.inject j arg1 arg2.
  Proof.
    destruct 1; simpl; intros.
    eexists; split; try econstructor; eauto.
    exploit Mem.loadv_inject; eauto.
    apply Val.offset_ptr_inject; eauto.
    intros (v2 & LOAD & INJ).
    eexists; split; try econstructor; eauto.
  Qed.

  Lemma extcall_arg_pair_inject:
    forall j g rs1 m1 arg1 ty rs2 m2,
      extcall_arg_pair rs1 m1 ty arg1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j g m1 m2 ->
      exists arg2,
        extcall_arg_pair rs2 m2 ty arg2 /\
        Val.inject j arg1 arg2.
  Proof.
    destruct 1; simpl; intros.
    eapply extcall_arg_inject in H; eauto.
    destruct H as (arg2 & EA & INJ);
      eexists; split; try econstructor; eauto.
    eapply extcall_arg_inject in H; eauto.
    destruct H as (arg2 & EA & INJ).
    eapply extcall_arg_inject in H0; eauto.
    destruct H0 as (arg3 & EA1 & INJ1).
    eexists; split; try econstructor; eauto.
    apply Val.longofwords_inject; eauto.
  Qed.

  Lemma extcall_arguments_inject:
    forall j g rs1 m1 args1 sg rs2 m2,
      extcall_arguments rs1 m1 sg args1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j g m1 m2 ->
      exists args2,
        extcall_arguments rs2 m2 sg args2 /\
        Val.inject_list j args1 args2.
  Proof.
    unfold extcall_arguments.
    intros j g rs1 m1 args1 sg rs2 m2.
    revert args1. generalize (loc_arguments sg).
    induction 1; simpl; intros; eauto.
    exists nil; split; try econstructor.
    eapply extcall_arg_pair_inject in H; eauto.
    decompose [ex and] H.
    edestruct IHlist_forall2 as (a2 & EA & INJ); eauto.
    eexists; split; econstructor; eauto.
  Qed.

  Lemma set_pair_no_rsp:
    forall p res rs,
      no_rsp_pair p ->
      set_pair p res rs RSP = rs RSP.
  Proof.
    destruct p; simpl; intros; rewrite ! Pregmap.gso; intuition. 
  Qed.

  Lemma val_inject_set_pair:
    forall j p res1 res2 rs1 rs2,
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Val.inject j res1 res2 ->
      forall r,
        Val.inject j (set_pair p res1 rs1 r) (set_pair p res2 rs2 r).
  Proof.
    destruct p; simpl; intros; eauto.
    apply val_inject_set; auto.
    repeat (intros; apply val_inject_set; auto).
    apply Val.hiword_inject; auto.
    apply Val.loword_inject; auto.
  Qed.

  Theorem step_simulation:
    forall S1 t S2,
      Asm.step init_sp ge S1 t S2 ->
      forall j ostack S1' (MS: match_states j ostack S1 S1'),
      exists j' ostack' S2',
        step ge S1' t S2' /\
        match_states j' ostack' S2 S2'.
  Proof.
    destruct 1; intros; inversion MS; subst.
    - 
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H7; inv H7. 
      assert (asm_instr_no_rsp i).
      {
        eapply prog_no_rsp. eauto.
        eapply Asmgenproof0.find_instr_in; eauto.
      }
      destruct (exec_instr_inject' _ _ _ _ _ _ _ _ _ _ MS H4 (asmgen_no_change_stack i) H2)
        as ( j' & ostack' & rs2' & m2' & EI' & MS' & INCR).
      do 3 eexists; split.
      eapply exec_step_internal; eauto.
      rewrite Ptrofs.add_zero. eauto.
      eauto.
    -
      edestruct (eval_builtin_args_inject) as (vargs' & Hargs & Hargsinj).
      6: eauto.
      eauto. eauto. eauto.
      eauto. 
      eapply GLOBSYMB_INJ.
      edestruct (external_call_mem_inject_gen ef ge ge)
        as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & INCR & SEP).
      apply meminj_preserves_globals'_symbols_inject.
      eauto.
      eauto.
      eauto.
      eauto. 
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H9; inv H9. 
      do 3 eexists; split.
      eapply exec_step_builtin.
      eauto.
      eauto. 
      rewrite Ptrofs.add_zero; eauto.
      eauto.
      eauto.
      auto.
      reflexivity.
      econstructor.
      + eapply Mem.mem_inject_ext. eauto.
        erewrite external_call_stack_blocks; eauto.
      + rewrite nextinstr_nf_rsp.
        intros b o.
        rewrite set_res_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        auto.
      + intros. apply val_inject_nextinstr_nf.
        apply val_inject_set_res; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
      + eapply external_call_valid_block; eauto.
      + red. rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other.
        erewrite <- external_call_stack_blocks. eauto. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + erewrite <- external_call_stack_blocks; eauto.
      + red. 
        rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red.
        intros.
        eapply Mem.perm_max in H6.
        eapply external_call_max_perm in H6.
        2: eauto.
        eauto. eauto.
      + red.
        intros.
        eapply ec_perm_unchanged. eapply external_call_spec. eauto.
        eauto.
        intros. eapply PBS in H7. destruct H7.  intro A; inv A; inv H9. 
        eauto.
      + red.
        erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
      + rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red. intros b delta o k p JB1 PERM.
        erewrite <- external_call_stack_blocks. 2: eauto.
        destruct (j b) eqn:A. destruct p0.
        exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
        eapply NIB; eauto.
        eapply Mem.perm_max in PERM.
        eapply external_call_max_perm in PERM.
        2: eauto.
        eauto.
        eapply Mem.valid_block_inject_1; eauto.
        exploit SEP. eauto. eauto. intuition congruence.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply inject_stack_incr; eauto.
      + 
        red.
        unfold get_frame_info.
        erewrite <- external_call_stack_blocks. 2: eauto.
        intros.
        exploit inj_incr_sep_same. eauto. eauto. apply H7. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply H9. auto.
        intros.
        eapply IP; eauto.
        eapply Mem.perm_max in H10.
        eapply external_call_max_perm; eauto.
        eapply Mem.valid_block_inject_1 in H11; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply perm_stack_inv. eauto.
        apply Mem.in_frames_valid.
        eapply ec_perm_frames; eauto.
        apply external_call_spec.
      + intros.
        eapply INCR; eauto.
      + intros.
        eapply INCR; eauto.
      + destruct GLOBSYMB_INJ.
        split. intros.
        eapply INCR; eauto.
        intros.
        destruct (j b1) eqn:JB1.
        destruct p.
        exploit INCR; eauto. rewrite H9; intro X; inv X.
        eauto.
        exploit SEP; eauto. intros (NV1 & NV2).
        simpl; unfold Genv.block_is_volatile.
        rewrite ! find_var_info_none_ge.
        auto.
        unfold Mem.valid_block in NV1. xomega.
        unfold Mem.valid_block in NV2. xomega.
      + etransitivity. apply GlobLe. eapply external_call_nextblock; eauto.
      + etransitivity. apply GlobLeT. eapply external_call_nextblock; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto. eauto.
    -
      edestruct (extcall_arguments_inject) as (vargs' & Hargs & Hargsinj).
      eauto.
      eauto. eauto. 
      edestruct (external_call_mem_inject_gen ef ge ge)
        as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & INCR & SEP).
      apply meminj_preserves_globals'_symbols_inject. eauto.
      eauto.
      eauto.
      eauto. 
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H8; inv H8. 
      do 3 eexists; split.
      eapply exec_step_external.
      eauto.
      eauto.
      eauto.
      generalize (RINJ RSP). destruct (rs RSP); simpl in *; inversion 1; subst; try congruence.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      generalize (RINJ RSP). destruct (rs RSP); simpl in *; inversion 1; subst; try congruence.
      generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence.
      eauto.
      reflexivity.
      econstructor.
      + eapply Mem.mem_inject_ext; eauto.
        erewrite external_call_stack_blocks; eauto.
      +
        repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + intros; apply val_inject_set.
        intros; apply val_inject_set.
        intros; apply val_inject_set_pair; auto.
        apply val_inject_undef_regs; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
        intros; eapply val_inject_incr; eauto.
        auto.
      + eapply external_call_valid_block; eauto.
      + red. repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        erewrite <- external_call_stack_blocks. eauto. eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + erewrite <- external_call_stack_blocks; eauto.
      + red.
        repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + red.
        intros.
        eapply Mem.perm_max in H5.
        eapply external_call_max_perm in H5.
        2: eauto.
        eauto. eauto.
      + red.
        intros.
        eapply ec_perm_unchanged. eapply external_call_spec. eauto.
        eauto.
        intros. eapply PBS in H6. destruct H6.  intro A; inv A; inv H8.
        eauto.
      + red.
        erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
      + repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto. 
      + red. intros b delta o k p JB1 PERM.
        erewrite <- external_call_stack_blocks. 2: eauto.
        destruct (j b) eqn:A. destruct p0.
        exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
        eapply NIB; eauto.
        eapply Mem.perm_max in PERM.
        eapply external_call_max_perm in PERM.
        2: eauto.
        eauto.
        eapply Mem.valid_block_inject_1; eauto.
        exploit SEP. eauto. eauto. intuition congruence.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply inject_stack_incr; eauto.
      + 
        red.
        unfold get_frame_info.
        erewrite <- external_call_stack_blocks. 2: eauto.
        intros.
        exploit inj_incr_sep_same. eauto. eauto. apply H6. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply H8. auto.
        intros.
        eapply IP; eauto.
        eapply Mem.perm_max in H9.
        eapply external_call_max_perm; eauto.
        eapply Mem.valid_block_inject_1 in H10; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply perm_stack_inv. eauto.
        apply Mem.in_frames_valid.
        eapply ec_perm_frames; eauto. apply external_call_spec.
      + intros.
        eapply INCR; eauto.
      + intros.
        eapply INCR; eauto.
      + destruct GLOBSYMB_INJ.
        split. intros.
        eapply INCR; eauto.
        intros.
        destruct (j b1) eqn:JB1.
        destruct p.
        exploit INCR; eauto. rewrite H8; intro X; inv X.
        eauto.
        exploit SEP; eauto. intros (NV1 & NV2).
        simpl; unfold Genv.block_is_volatile.
        rewrite ! find_var_info_none_ge.
        auto.
        unfold Mem.valid_block in NV1. xomega.
        unfold Mem.valid_block in NV2.
        xomega. 
      + etransitivity. apply GlobLe. eapply external_call_nextblock; eauto.
      + etransitivity. apply GlobLeT. eapply external_call_nextblock; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
  Qed.

End PRESERVATION.


  Inductive mono_initial_state {F V} (prog: program F V) (rs: regset) m: state -> Prop :=
  |mis_intro:
     forall m1 bstack m2 m3
       (MALLOC: Mem.alloc m 0 (Mem.stack_limit) = (m1,bstack))
       (MDROP: Mem.drop_perm m1 bstack 0 (Mem.stack_limit) Writable = Some m2)
       (MRSB: Mem.record_stack_blocks m2 (make_singleton_frame_adt' bstack frame_info_mono 0) m3),
       let ge := Genv.globalenv prog in
       let rs0 :=
           rs # PC <- (Genv.symbol_address ge prog.(prog_main) Ptrofs.zero)
              #RA <- Vnullptr
              #RSP <- (Vptr bstack (Ptrofs.repr Mem.stack_limit)) in
         mono_initial_state prog rs m (State rs0 m3).

  Lemma repr_stack_limit:
    Ptrofs.unsigned (Ptrofs.repr (Mem.stack_limit)) = Mem.stack_limit.
  Proof.
    apply Ptrofs.unsigned_repr.
    generalize (Mem.stack_limit_range); omega.
  Qed.
  
  Lemma match_initial_states s m0:
    Asm.initial_state prog s ->
    Genv.init_mem prog = Some m0 ->
    exists s' j ostack, match_states (Genv.genv_next ge) j ostack s s' /\
                   mono_initial_state prog (Pregmap.init Vundef) m0 s'.
  Proof.
    inversion 1. subst.
    rename H into INIT.
    rename H0 into INITMEM.
    rename H1 into ALLOC.
    rename H2 into RSB.
    rewrite INITMEM. intro A; inv A.
    exploit Genv.initmem_inject; eauto.
    intro FLATINJ.
    destruct (Mem.alloc m0 0 Mem.stack_limit) as (m1' & bstack0) eqn:ALLOC'.
    generalize (Mem.alloc_right_inject _ _ _ _ _ _ _ _ FLATINJ ALLOC'). intro ALLOCINJ1.
    destruct (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ bstack0 Mem.stack_limit ALLOCINJ1 ALLOC)
      as (f' & STACKINJ & INCR & FNEW & FOLD).
    {
      eapply Mem.valid_new_block; eauto.
    }
    {
      apply Mem.stack_limit_range.
    }
    {
      intros.
      eapply Mem.perm_alloc_3 in H. 2: eauto.
      right. generalize Mem.stack_limit_range; omega.
    }
    {
      intros; omega.
    }
    {
      simpl. red.
      intros.
      generalize (size_chunk_pos chunk); omega.
    }
    {
      intros; omega.
    }
    {
      erewrite Mem.alloc_stack_blocks; eauto.
      erewrite Genv.init_mem_stack_adt; eauto. easy.
    }
    edestruct (Mem.range_perm_drop_2).
    red; intros; eapply Mem.perm_alloc_2; eauto.
    exploit Mem.drop_outside_inject. apply STACKINJ. eauto.
    {
      intros b' delta ofs k p FB1 PERM RNG.
      destruct (peq b' b).
      - subst. eapply Mem.perm_alloc_3 in PERM; eauto. omega.
      - rewrite FOLD in FB1 by auto. unfold Mem.flat_inj in FB1.
        destr_in FB1. inv FB1.
        exploit Mem.alloc_result; eauto. intro A. rewrite A in p0.  xomega.
    } 
    intro STACKINJdrop.
    assert (b = bstack0).
    {
      exploit Mem.alloc_result. apply ALLOC.
      exploit Mem.alloc_result. apply ALLOC'. congruence.
    }
    subst.
    assert (bstack = bstack0).
    {
      unfold bstack.
      unfold ge.
      exploit Mem.alloc_result; eauto.
      erewrite <- Genv.init_mem_genv_next; eauto.
    }
    subst.
    exploit Mem.record_stack_block_inject_flat.
    erewrite <- Mem.alloc_stack_blocks in STACKINJdrop; eauto.
    7: eauto.
    instantiate (1 := make_singleton_frame_adt' bstack frame_info_mono 0).
    {
      red; red.
      apply Forall_forall. simpl.
      intros (b & fi) [A|[]] b2 delta F. inv A. simpl in *.
      rewrite FNEW in F; inv F.
      rewrite peq_true. eexists; split; eauto.
      split. simpl; auto.
      simpl. intros; omega.
    }
    {
      erewrite Mem.drop_perm_stack_adt; eauto.
      erewrite Mem.alloc_stack_blocks; eauto.
      erewrite Genv.init_mem_stack_adt; eauto. 
    }
    {
      intros b [A|[]]. inv A. simpl.
      eapply Mem.drop_perm_valid_block_1; eauto.
      eapply Mem.valid_new_block; eauto.
    }
    {
      intros b fi [A|[]]; inv A.
      intros o k p PERM; simpl.
      eapply Mem.perm_drop_4 in PERM; eauto.
      eapply Mem.perm_alloc_3; eauto.
    }
    {
      unfold in_frame; simpl.
      intros b1 b2 delta Fb1.
      split; intros [A|[]]; inv A; subst; left; try congruence.
      destruct (peq b1 bstack); auto.
      rewrite FOLD in Fb1; auto.
      unfold Mem.flat_inj in Fb1.
      destr_in Fb1.
    }
    reflexivity.
    intros (m2' & MRSB & STACKINJ_FINAL & LEN).
    exists (State ((((Pregmap.init Vundef) # PC <- (Genv.symbol_address ge0 (prog_main prog) Ptrofs.zero)) # RA <- Vnullptr) #RSP <- (Vptr bstack (Ptrofs.repr Mem.stack_limit))) m2');
      eexists; exists (Ptrofs.unsigned (Ptrofs.repr Mem.stack_limit)) (* (Ptrofs.unsigned Ptrofs.zero) *); split.
    2: econstructor; eauto.
    econstructor; eauto.
    - eapply Mem.mem_inject_ext. eauto. 
      unfold flat_frameinj. 
      intros.
      erewrite (Mem.record_stack_blocks_stack_adt _ _ _ RSB).
      erewrite (Mem.alloc_stack_blocks _ _ _ _ _ ALLOC); eauto.
      erewrite Genv.init_mem_stack_adt; eauto.
      simpl. repeat destr. f_equal; omega.
    - unfold rs0.
      rewrite Pregmap.gss. inversion 1. auto.
    - unfold rs0.
      intros; apply val_inject_set; auto.
      intros; apply val_inject_set; auto.
      intros; apply val_inject_set; auto.
      + unfold Genv.symbol_address. destr; auto.
        destruct (peq b bstack); subst.
        eapply Genv.genv_symb_range in Heqo; eauto. unfold bstack in Heqo. replace ge with ge0 in Heqo. xomega.
        unfold ge, ge0; reflexivity.
        econstructor; eauto.
        rewrite FOLD; auto.
        unfold Mem.flat_inj; apply pred_dec_true.
        erewrite <- Genv.init_mem_genv_next. 2: eauto.
        eapply Genv.genv_symb_range; eauto. 
        reflexivity.
      + constructor.
      + econstructor; eauto. symmetry; apply Ptrofs.add_zero_l.
    - red.         
      erewrite Mem.record_stack_block_nextblock; eauto.
      erewrite Mem.nextblock_drop; eauto.
      erewrite Mem.nextblock_alloc; eauto.
      apply Mem.alloc_result in ALLOC; subst. rewrite ALLOC. xomega.
    - red.
      unfold rs0.
      rewrite Pregmap.gss. inversion 1.
      erewrite Mem.record_stack_blocks_stack_adt. 2: eauto.
      erewrite (Mem.alloc_stack_blocks). 2: eauto. 
      erewrite Genv.init_mem_stack_adt; eauto.
      simpl.
      change (align (Z.max 0 0) 8) with 0.
      rewrite repr_stack_limit. omega. 
    - erewrite Mem.record_stack_blocks_stack_adt. 2: eauto.
      unfold rs0. simpl. rewrite Pregmap.gss. auto. 
    - erewrite Mem.record_stack_blocks_stack_adt. 2: eauto.
      erewrite (Mem.alloc_stack_blocks). 2: eauto. 
      erewrite Genv.init_mem_stack_adt; eauto.
      constructor; simpl; auto. omega.
    - red. 
      unfold rs0.
      rewrite Pregmap.gss. inversion 1.
      rewrite repr_stack_limit. apply Mem.stack_limit_aligned.
    - red. intros o k p P.
      assert (RNG: 0 <= o < Mem.stack_limit).
      {
        eapply Mem.record_stack_block_perm in P. 2: eauto.
        eapply Mem.perm_drop_4 in P; eauto.
        eapply Mem.perm_alloc_3 in P. 2: eauto. auto.
      }
      eapply Mem.record_stack_block_perm in P. 2: eauto.
      exploit Mem.perm_drop_2; eauto. intros PO.
      split; auto. generalize Mem.stack_limit_range; omega.
    - red; intros.
      eapply Mem.record_stack_block_perm'. eauto.
      eapply Mem.perm_drop_1; eauto.
    - red.
      erewrite Mem.record_stack_blocks_stack_adt; eauto.
      erewrite Mem.drop_perm_stack_adt; eauto.
      erewrite Mem.alloc_stack_blocks; eauto.
      erewrite Genv.init_mem_stack_adt; eauto.
      eexists; eexists; split. eauto. split.  reflexivity.
      split. reflexivity.
      split.  reflexivity. reflexivity.
    - unfold rs0.
      rewrite Pregmap.gss. inversion 1; subst. auto.
    - red.
      intros b delta o k p INJ PERM.
      eapply Mem.record_stack_block_perm in PERM; eauto.
      eapply Mem.perm_alloc_inv in PERM; eauto.
      destr_in PERM. omega.
      erewrite Mem.record_stack_blocks_stack_adt; eauto.
      simpl.
      rewrite repr_stack_limit.
      rewrite FOLD in INJ; auto.
      unfold Mem.flat_inj in INJ. destr_in INJ.
    - erewrite Mem.record_stack_blocks_stack_adt; eauto.
      erewrite Mem.alloc_stack_blocks; eauto.
      erewrite Genv.init_mem_stack_adt; eauto.
      repeat econstructor; eauto.
      simpl.
      change (align (Z.max 0 0) 8) with 0.
      rewrite FNEW. f_equal. f_equal. omega.
    - red. 
      erewrite Mem.record_stack_blocks_stack_adt; eauto.
      erewrite Mem.alloc_stack_blocks; eauto.
      erewrite Genv.init_mem_stack_adt; eauto.
      simpl.
      intros b fi delta EQ FB b' o delta' k p FB' PERM.
      repeat destr_in EQ. simpl in *.
      rewrite Z.max_r by omega.
      change (align 0 8) with 0. omega.
    -
      erewrite Mem.record_stack_blocks_stack_adt; eauto.
      erewrite Mem.alloc_stack_blocks; eauto.
      erewrite Genv.init_mem_stack_adt; eauto. econstructor; eauto.
      constructor. 3: reflexivity. 2: easy.
      simpl. intros o k p ; split; try omega.
      intro P.
      eapply Mem.record_stack_block_perm in P; eauto.
      eapply Mem.perm_alloc_inv in P; eauto.
      rewrite pred_dec_true in P; auto.
    - intros.
      assert (Plt b (Genv.genv_next ge)).
      {
        unfold Genv.find_funct_ptr in H. repeat destr_in H.
        eapply Genv.genv_defs_range in Heqo; eauto.
      }
      destruct (peq b bstack); subst.
      unfold bstack in H0. xomega.
      rewrite FOLD; auto.
      unfold Mem.flat_inj; apply pred_dec_true.
      erewrite <- Genv.init_mem_genv_next. 2: eauto. auto.
    - intros.
      assert (Plt b (Genv.genv_next ge)).
      {
        eapply Genv.genv_defs_range in H; eauto.
      }
      destruct (peq b bstack); subst.
      unfold bstack in H0. xomega.
      rewrite FOLD; auto.
      unfold Mem.flat_inj; apply pred_dec_true.
      erewrite <- Genv.init_mem_genv_next. 2: eauto. auto.
    - split.
      simpl; intros.
      assert (Plt b (Genv.genv_next ge)).
      {
        eapply Genv.genv_symb_range in H; eauto.
      }
      destruct (peq b bstack); subst.
      unfold bstack in H0. xomega.
      rewrite FOLD; auto.
      unfold Mem.flat_inj; apply pred_dec_true.
      erewrite <- Genv.init_mem_genv_next. 2: eauto. auto.
      intros b1 b2 delta FB. destruct (peq b1 bstack); subst.
      rewrite FNEW in FB; inv FB; auto.
      rewrite FOLD in FB; auto.
      unfold Mem.flat_inj in FB; repeat destr_in FB; auto.
    - erewrite Mem.record_stack_block_nextblock. 2: eauto.
      erewrite Mem.nextblock_alloc. 2: eauto.
      erewrite <- Genv.init_mem_genv_next; eauto. unfold ge; xomega. 
    - erewrite Mem.record_stack_block_nextblock. 2: eauto.
      erewrite Mem.nextblock_drop; eauto. erewrite Mem.nextblock_alloc.
      erewrite <- Genv.init_mem_genv_next; eauto. unfold ge; xomega.
      eauto.
    - unfold init_sp. inversion 1; subst.
      erewrite Mem.record_stack_blocks_stack_adt; eauto.
      left. left. reflexivity.
  Qed.

  Lemma transf_final_states:
    forall isp j o st1 st2 r,
      match_states isp j o st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
  Proof.
    inversion 1; subst.
    inversion 1; subst.
    econstructor.
    generalize (RINJ PC). rewrite H3. unfold Vnullptr. destruct ptr64; inversion 1; auto.
    generalize (RINJ RAX). rewrite H5. unfold Vnullptr. destruct ptr64; inversion 1; auto.
  Qed.

  Definition mono_semantics (p: Asm.program) rs m :=
    Semantics step (mono_initial_state p rs m) final_state (Genv.globalenv p).
  
  Theorem transf_program_correct m:
    asm_prog_no_rsp ge ->
    Genv.init_mem prog = Some m ->
    forward_simulation (Asm.semantics (Vptr (Genv.genv_next ge) Ptrofs.zero) prog) (mono_semantics prog (Pregmap.init Vundef) m).
  Proof.
    intros APNR IM.
    eapply forward_simulation_step with (fun s1 s2 => exists j o, match_states (Genv.genv_next ge) j o s1 s2).
    - simpl. reflexivity. 
    - simpl. intros s1 IS; inversion IS. rewrite IM in H; inv H.
      exploit match_initial_states. eauto. eauto.
      intros (s' & j & ostack & MS & MIS); eexists; split; eauto.
    - simpl. intros s1 s2 r (j & o & MS) FS. eapply transf_final_states; eauto.
    - simpl. intros s1 t s1' STEP s2 (j & o & MS). 
      edestruct step_simulation as (isp' & j' & o' & STEP' & MS'); eauto.
  Qed.
  
End WITHMEMORYMODEL.

