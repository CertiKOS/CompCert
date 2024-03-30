Require Import Maps Coqlib Integers List.
Require Import AST Globalenvs Memory Values.
Import ListNotations.

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
