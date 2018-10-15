(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Feb 7, 2018 *)
(* ******************* *)

(** Correctness proof for the FlatAsm generation **)

Require Import Coqlib Integers Values Maps AST.
Require Import Memtype Memory.
Require Import Smallstep.
Require Import Asm RealAsm.
Require Import FlatAsm FlatAsmBuiltin FlatAsmgen FlatAsmProgram.
Require Import Segment.
Require Import Events.
Require Import StackADT.
Require Import Linking Errors.
Require Import Globalenvs FlatAsmGlobenv.
Require Import AsmFacts.
Require Import Num.

Open Scope Z_scope.

Ltac monadInvX1 H :=
  let monadInvX H :=  
      monadInvX1 H ||
                 match type of H with
                 | (?F _ _ _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 end
  in

  match type of H with
  | (OK _ = OK _) =>
      inversion H; clear H; try subst
  | (Error _ = OK _) =>
      discriminate
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInvX EQ1);
      try (monadInvX1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInvX EQ1);
      try (monadInvX1 EQ2)))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
      destruct X eqn:?; [try (monadInvX1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [discriminate | try (monadInvX1 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [try (monadInvX1 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  | (match ?X with Some _ => _ | None => _ end = _) =>
      let EQ := fresh "EQ" in (
      destruct X eqn:EQ; try (monadInvX1 H))
  | (match ?X with pair _ _ => _ end = OK _) =>
      let EQ := fresh "EQ" in (
      destruct X eqn:EQ; try (monadInvX1 H))
  end.

Ltac monadInvX H :=
  monadInvX1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  end.  


Lemma alignw_le : forall x, x <= align x alignw.
Proof.
  intros x. apply align_le. unfold alignw. omega.
Qed.


Lemma divides_align : forall y x,
    y > 0 -> (y | x) -> align x y = x.
Proof.
  intros y x GT DV.
  unfold align. red in DV. destruct DV as [z DV].
  subst. replace (z * y + y - 1) with (z * y + (y - 1)) by omega.
  erewrite Int.Zdiv_shift; eauto.
  erewrite Z_div_mult; eauto. rewrite Z_mod_mult.
  rewrite zeq_true. rewrite Z.add_0_r. auto.
Qed.

Lemma align_idempotent : forall v x,
    x > 0 -> align (align v x) x = align v x.
Proof.
  intros v x H. eapply divides_align; eauto.
  apply align_divides. auto.
Qed.

Lemma alignw_divides:
  forall z,
    (alignw | align z alignw).
Proof.
  intros. apply align_divides. unfold alignw; omega.
Qed.


(** Lemmas about FlatAsmgen that are useful for proving invariants *)

Lemma transl_fun_exists : forall gmap defs gdefs f id,
    transl_globdefs gmap defs = OK gdefs ->
    In (id, Some (Gfun (Internal f))) defs ->
    exists f', transl_fun gmap id f = OK f'
          /\ forall i, In i (fn_code f') -> In i (get_defs_code gdefs).
Proof.
  induction defs; simpl; intros.
  - contradiction.
  - destruct a. destruct H0.
    + inv H0. monadInv H. destruct x.
      destruct p. monadInv EQ.
      eexists; split; eauto.
      intros. simpl. rewrite in_app. auto.
    + monadInv H. destruct x.
      destruct p. 
      exploit IHdefs; eauto.
      intros (f' & TRANSLF & IN). eexists; split; eauto.
      intros. simpl. rewrite in_app. auto.
Qed.

Definition size_gvar (def: option (AST.globdef Asm.fundef unit)) : Z :=
  match def with
  | Some (Gvar gv) => init_data_list_size (gvar_init gv)
  | _ => 0
  end.

(* Definition size_extfun (def: option (AST.globdef Asm.fundef unit)) : Z := *)
(*   match def with *)
(*   | Some (Gfun (External ef)) => alignw *)
(*   | _ => 0 *)
(*   end. *)

Definition size_fun (def: option (AST.globdef Asm.fundef unit)) : Z :=
  match def with
  | Some (Gfun (Internal f)) => code_size (Asm.fn_code f)
  | _ => 0
  end.

Lemma align0: align 0 alignw = 0.
Proof.
  reflexivity.
Qed.

Lemma update_instrs_code_size:
  forall i c lmap csize  lmap' csize'
    (UI : update_instrs lmap csize i c = (lmap', csize')),
    csize' = csize + code_size c.
Proof.
  clear.
  unfold update_instrs.
  induction c; simpl; intros; eauto. inv UI. omega.
  apply IHc in UI. omega.    
Qed.

Lemma update_instrs_other:
  forall i i' l (n: i <> i') c lmap csize lmap' csize'
    (UI : update_instrs lmap csize i c = (lmap', csize')),
    lmap' i' l = lmap i' l.
Proof.
  clear.
  unfold update_instrs.
  induction c; simpl; intros; eauto.
  inv UI; auto.
  destruct (update_instr lmap csize i a) eqn:UI1.
  erewrite IHc. 2: apply UI. clear UI.
  unfold update_instr in UI1. repeat destr_in UI1.
  unfold update_label_map. rewrite peq_false by auto. auto.
Qed.

Lemma align_plus:
  forall a b z,
    (z | a) -> z <> 0 ->
    align (a + b) z = a + align b z.
Proof.
  unfold align.
  intros.
  destruct H. subst.
  replace (x * z + b + z - 1) with ((x * z) + (b + z - 1)) by omega.
  rewrite Z_div_plus_full_l; auto.
  rewrite Z.mul_add_distr_r. reflexivity.
Qed.

Section UPDATE_MAPS.

  Variable gmap: GID_MAP_TYPE.
  Variable lmap: LABEL_MAP_TYPE.
  Variables dsize csize: Z.

  Variable i: ident.
  Variable def: option (globdef Asm.fundef unit).

  Variable gmap': GID_MAP_TYPE.
  Variable lmap': LABEL_MAP_TYPE.
  Variables dsize' csize': Z.

  Hypothesis UPDATE: update_maps_def gmap lmap dsize csize i def = (gmap', lmap', dsize', csize').

  Lemma update_gmap:
    forall i',
      gmap' i' = if ident_eq i i'
                 then match def with
                      | None => gmap i
                      | Some (Gfun (External ef)) => gmap i
                      | Some (Gfun (Internal f)) => Some (code_label csize)
                      | Some (Gvar gvar) => Some (data_label dsize)
                      end
                 else gmap i'.
  Proof.
    unfold update_maps_def in UPDATE.
    intros. destr.
    unfold update_gid_map in UPDATE.
    repeat destr_in UPDATE; rewrite peq_true; auto.
    unfold update_gid_map in UPDATE.
    repeat destr_in UPDATE; try rewrite peq_false; auto.
  Qed.

  Lemma update_lmap:
    forall i' l,
      lmap' i' l = if ident_eq i i'
                   then match def with
                        | Some (Gfun (Internal f)) =>
                          fst (update_instrs lmap csize i (Asm.fn_code f)) i l
                        | _ => lmap i' l
                        end
                   else lmap i' l.
  Proof.
    unfold update_maps_def in UPDATE.
    intros. destr.
    repeat destr_in UPDATE; auto.
    repeat destr_in UPDATE; auto.
    eapply update_instrs_other; eauto.
  Qed.

  Lemma update_dsize:
    dsize' = dsize + align (size_gvar def) alignw.
  Proof.
    unfold update_maps_def in UPDATE.
    repeat destr_in UPDATE; simpl; rewrite ? align0; omega.
  Qed.

  Lemma update_dsize_mono:
    dsize <= dsize'.
  Proof.
    rewrite update_dsize.
    generalize (alignw_le (size_gvar def)).
    cut (0 <= size_gvar def). omega.
    unfold size_gvar. repeat destr; try omega.
    generalize (init_data_list_size_pos (gvar_init v)); omega.
  Qed.

  (* Lemma update_efsize: *)
  (*   efsize' = efsize + size_extfun def. *)
  (* Proof. *)
  (*   unfold update_maps_def in UPDATE. *)
  (*   repeat destr_in UPDATE; simpl; omega. *)
  (* Qed. *)


  (* Lemma update_efsize_mono: *)
  (*   efsize <= efsize'. *)
  (* Proof. *)
  (*   rewrite update_efsize. *)
  (*   unfold size_extfun. unfold alignw. repeat destr; try omega. *)
  (* Qed. *)

  Lemma update_csize_mono:
    csize <= csize'.
  Proof.
    unfold update_maps_def in UPDATE.
    repeat destr_in UPDATE; simpl; rewrite ? align0; try omega.
    eapply update_instrs_code_size in Heqp; eauto. subst.
    etransitivity. 2: apply alignw_le.
    generalize (code_size_non_neg (Asm.fn_code f0)); omega.
  Qed.

  Hypothesis csize_div: (alignw | csize).

  Lemma update_csize:
    csize' = csize + align (size_fun def) alignw.
  Proof.
    unfold update_maps_def in UPDATE.
    repeat destr_in UPDATE; simpl; rewrite ? align0; try omega.
    eapply update_instrs_code_size in Heqp; eauto. subst.
    rewrite align_plus; auto. unfold alignw. congruence.
  Qed.


  Hypothesis dsize_div: (alignw | dsize).

  Lemma update_dsize_div:
    (alignw | dsize').
  Proof.
    rewrite update_dsize.
    apply Z.divide_add_r. auto. apply align_divides. unfold alignw; omega.
  Qed.

  Lemma update_csize_div:
    (alignw | csize').
  Proof.
    rewrite update_csize.
    apply Z.divide_add_r. auto. apply align_divides. unfold alignw; omega.
  Qed.

  (* Lemma update_efsize_div: *)
  (*   (alignw | efsize'). *)
  (* Proof. *)
  (*   rewrite update_efsize. *)
  (*   apply Z.divide_add_r. auto. *)
  (*   unfold size_extfun. *)
  (*   repeat destr; first [ exists 0; omega | exists 1; omega ]. *)
  (* Qed. *)

End UPDATE_MAPS.

Definition sum {A: Type} (f: A -> Z) (l: list A)  :=
  fold_left (fun acc e => acc + f e) l 0.

Lemma fold_left_plus:
  forall {A} f (l: list A) d,
    fold_left (fun acc e => acc + f e) l d = d + sum f l.
Proof.
  unfold sum.
  induction l; simpl; intros. omega.
  rewrite IHl.
  rewrite (IHl (f a)). omega.
Qed.

Definition sizes_gvars (defs: list (ident * option (AST.globdef Asm.fundef unit))) : Z :=
  sum (fun d => align (size_gvar (snd d)) alignw) defs.

(* Definition sizes_extfuns (defs: list (ident * option (AST.globdef Asm.fundef unit))) : Z := *)
(*   sum (fun d => size_extfun (snd d)) defs. *)

Definition sizes_funs (defs: list (ident * option (AST.globdef Asm.fundef unit))) : Z :=
  sum (fun d => align (size_fun (snd d)) alignw) defs.

Lemma sum_pos:
  forall {A: Type} f (fpos: forall x, 0 <= f x) (l: list A), 0 <= sum f l.
Proof.
  unfold sum.
  induction l; simpl; intros; eauto. omega.
  rewrite fold_left_plus.
  fold (sum f l) in IHl. specialize (fpos a). omega.
Qed.

Lemma sizes_gvars_pos:
  forall d, 0 <= sizes_gvars d.
Proof.
  apply sum_pos.
  intros.
  etransitivity. 2: apply alignw_le.
  unfold size_gvar. repeat destr; try omega.
  generalize (init_data_list_size_pos (gvar_init v)); omega.
Qed.

(* Lemma sizes_extfuns_pos: *)
(*   forall d, 0 <= sizes_extfuns d. *)
(* Proof. *)
(*   apply sum_pos. *)
(*   intros. *)
(*   unfold size_extfun. repeat destr; try omega. *)
(*   unfold alignw; omega. *)
(* Qed. *)

Lemma sizes_funs_pos:
  forall d, 0 <= sizes_funs d.
Proof.
  apply sum_pos.
  intros.
  etransitivity. 2: apply alignw_le.
  unfold size_fun. repeat destr; try omega.
  generalize (code_size_non_neg (Asm.fn_code f0)); omega.
Qed.

Section UPDATE_MAPS2.

  Variable defs: list (ident * option (globdef Asm.fundef unit)).

  Variable gmap: GID_MAP_TYPE.
  Variable lmap: LABEL_MAP_TYPE.
  Variables dsize csize : Z.

  Variable gmap': GID_MAP_TYPE.
  Variable lmap': LABEL_MAP_TYPE.
  Variables dsize' csize' : Z.

  Hypothesis UPDATE: update_maps gmap lmap dsize csize defs = (gmap', lmap', dsize', csize').

  Lemma umind:
    forall (P : GID_MAP_TYPE -> LABEL_MAP_TYPE -> Z -> Z -> Prop)
      (Pstart: P gmap lmap dsize csize)
      (Pstep: forall g l s c g' l' s' c' i d,
          update_maps_def g l s c i d = (g', l', s', c') ->
          P g l s c ->
          In (i,d) defs ->
          P g' l' s' c'),
      P gmap' lmap' dsize' csize'.
  Proof.
    intros P Pstart.
    revert defs gmap lmap dsize csize Pstart gmap' lmap' dsize' csize' UPDATE.
    unfold update_maps.
    induction defs; simpl; intros; eauto.
    inv UPDATE. auto.
    destruct a as [i0 def0]. simpl in *.
    destruct (update_maps_def gmap lmap dsize csize i0 def0) as (((gmap1 & lmap1) & dsize1) & csize1) eqn:UP1.
    eapply IHl. 2: eauto. eapply Pstep; eauto. eauto.
  Qed.
  

  Lemma update_gmap_not_in:
    forall i,
      ~ In i (map fst defs) ->
      gmap' i = gmap i.
  Proof.
    intros.
    apply (umind (fun g l d c => g i = gmap i)); auto.
    intros.
    erewrite update_gmap. 2: eauto. rewrite pred_dec_false. auto.
    intro; subst. apply in_map with (f:=fst) in H2. simpl in H2. congruence.
  Qed.

  Lemma update_lmap_not_in:
    forall i l,
      ~ In i (map fst defs) ->
      lmap' i l = lmap i l.
  Proof.
    intros.
    eapply (umind (fun g ll d c => ll i l = lmap i l)); auto.
    intros.    
    erewrite update_lmap. 2: eauto. rewrite pred_dec_false; auto.
    intro; subst. apply in_map with (f:=fst) in H2. simpl in H2. congruence.
  Qed.

  Definition maps := (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z )%type.

  Lemma umind_rel_inv:
    forall (inv: maps -> Prop)
      (INVstart: inv (gmap,lmap,dsize,csize))
      (INV: forall g l s c g' l' s' c' i d,
          update_maps_def g l s c i d = (g', l', s', c') ->
          inv (g,l,s,c) -> inv (g',l',s',c'))
      {A: Type} (f: maps -> A) (t: _ -> A -> A)
      (Pstep: forall g l s c g' l' s' c' i d,
          update_maps_def g l s c i d = (g', l', s', c') ->
          In (i,d) defs ->
          inv (g,l,s,c) ->
          f (g',l',s',c') = t d (f (g,l,s,c))),
      fold_left (fun (acc : A) (id : ident * option (globdef Asm.fundef unit)) =>
                   t (snd id) acc) defs (f (gmap,lmap,dsize,csize))
      = f (gmap',lmap',dsize',csize').
  Proof.
    intros inv INVstart INV A f t.
    revert defs gmap lmap dsize csize gmap' lmap' dsize' csize' UPDATE INVstart.
    unfold update_maps.
    induction defs; simpl; intros; eauto.
    inv UPDATE. auto.
    destruct a as [i0 def0]. simpl in *.
    destruct (update_maps_def gmap lmap dsize csize i0 def0) as (((gmap1 & lmap1) & dsize1) & csize1) eqn:UP1.
    erewrite <- Pstep. 2: eauto. 2: eauto.
    eapply IHl; eauto.
    eauto.
  Qed.

  Lemma umind_rel:
    forall {A: Type} (f: maps -> A) (t: _ -> A -> A)
      (Pstep: forall g l s c g' l' s' c' i d,
          update_maps_def g l s c i d = (g', l', s', c') ->
          In (i,d) defs ->
          f (g',l',s',c') = t d (f (g,l,s,c))),
      fold_left (fun (acc : A) (id : ident * option (globdef Asm.fundef unit)) =>
                   t (snd id) acc) defs (f (gmap,lmap,dsize,csize))
      = f (gmap',lmap',dsize',csize').
  Proof.
    intros.
    eapply umind_rel_inv with (inv := fun _ => True); eauto.
  Qed.


  Lemma umind_inv:
    forall (inv: maps -> Prop)
      (INVstart: inv (gmap,lmap,dsize,csize))
      (INV: forall g l s c g' l' s' c' i d,
          update_maps_def g l s c i d = (g', l', s', c') ->
          inv (g,l,s,c) -> inv (g',l',s',c')),
      inv (gmap',lmap',dsize',csize').
  Proof.
    intros inv INVstart INV.
    revert defs gmap lmap dsize csize gmap' lmap' dsize' csize' UPDATE INVstart.
    unfold update_maps.
    induction defs; simpl; intros; eauto.
    inv UPDATE. auto.
    destruct a as [i0 def0]. simpl in *.
    destruct (update_maps_def gmap lmap dsize csize i0 def0) as (((gmap1 & lmap1) & dsize1) & csize1) eqn:UP1.
    eapply IHl; eauto.
  Qed.

  Lemma updates_gmap_in:
    forall i s,
      gmap' i = Some s ->
      In i (map fst defs) \/ gmap i = Some s.
  Proof.
    intros.
    destruct (in_dec peq i (map fst defs)); auto.
    rewrite update_gmap_not_in in H; auto.
  Qed.


  Lemma updates_dsize:
    dsize' = dsize + sizes_gvars defs.
  Proof.
    rewrite <- (umind_rel (fun '(g,l,d,c) => d) (fun def d => d + align (size_gvar def) alignw)).
    2: intros; eapply update_dsize; eauto.
    rewrite (fold_left_plus (fun e => align (size_gvar (snd e)) alignw) defs dsize).
    reflexivity.
  Qed.

  (* Lemma updates_efsize: *)
  (*   efsize' = efsize + sizes_extfuns defs. *)
  (* Proof. *)
  (*   rewrite <- (umind_rel (fun '(g,l,d,c,e) => e) (fun def e => e + size_extfun def)). *)
  (*   2: intros; eapply update_efsize; eauto. *)
  (*   rewrite (fold_left_plus (fun e => size_extfun (snd e)) defs efsize). *)
  (*   reflexivity. *)
  (* Qed. *)

  Hypothesis csize_div: (alignw | csize).

  Lemma updates_csize:
    csize' = csize + sizes_funs defs.
  Proof.
    erewrite <- (fun pf pf2 => umind_rel_inv (fun '(g,l,d,c) => (alignw | c)) pf pf2 (fun '(g,l,d,c) => c) (fun def c => c + align (size_fun def) alignw)).
    4: intros; eapply update_csize; eauto.
    rewrite (fold_left_plus (fun e => align (size_fun (snd e)) alignw) defs csize).
    reflexivity. auto.
    intros; eapply update_csize_div; eauto.
  Qed.

  (* Hypothesis efsize_div: (alignw | efsize). *)
  Hypothesis dsize_div: (alignw | dsize).

  Lemma updates_dsize_div:
    (alignw | dsize').
  Proof.
    eapply (umind_inv (fun '(g,l,d,c) => (alignw | d))); eauto.
    intros; eapply update_dsize_div; eauto.
  Qed.

  Lemma updates_csize_div:
    (alignw | csize').
  Proof.
    eapply (umind_inv (fun '(g,l,d,c) => (alignw | c))); eauto.
    intros; eapply update_csize_div; eauto.
  Qed.

  (* Lemma updates_efsize_div: *)
  (*   (alignw | efsize'). *)
  (* Proof. *)
  (*   eapply (umind_inv (fun '(g,l,d,c,e) => (alignw | e))); eauto. *)
  (*   intros; eapply update_efsize_div; eauto. *)
  (* Qed. *)

  Lemma csize_mono:
    csize <= csize'.
  Proof.
    rewrite updates_csize.
    generalize (sizes_funs_pos defs); omega.
  Qed.


  Lemma dsize_mono:
    dsize <= dsize'.
  Proof.
    rewrite updates_dsize.
    generalize (sizes_gvars_pos defs); omega.
  Qed.

  (* Lemma efsize_mono: *)
  (*   efsize <= efsize'. *)
  (* Proof. *)
  (*   rewrite updates_efsize. *)
  (*   generalize (sizes_extfuns_pos defs); omega. *)
  (* Qed. *)


End UPDATE_MAPS2.

Lemma update_maps_app:
  forall a b gmap lmap dsize csize,
    update_maps gmap lmap dsize csize (a ++ b) =
    let '(gmap', lmap', dsize', csize') := update_maps gmap lmap dsize csize a in
    update_maps gmap' lmap' dsize' csize' b.
Proof.
  unfold update_maps. intros.
  repeat destr.
  rewrite fold_left_app. rewrite Heqp. reflexivity.
Qed.

Theorem update_map_gmap_range : forall p gmap lmap dsize csize,
    make_maps p = (gmap, lmap, dsize, csize) ->
    forall id slbl, gmap id = Some slbl -> In (fst slbl) (code_segid :: data_segid :: nil).
Proof.
  intros p gmap lmap dsize csize UPDATE.
  pattern gmap,  lmap , dsize , csize.
  eapply umind. apply UPDATE. unfold default_gid_map. congruence.
  intros.
  erewrite update_gmap in H2; eauto.
  unfold code_label, data_label in H2.
  repeat destr_in H2; eauto; simpl; auto.
Qed.

(** Lemmas for proving agree_sminj_instr *)

(*   The key is to prove that 'Genv.find_instr', given the label of an instruction, *)
(*   will find the instruction iteself. This relies critically on the following two properties: *)

(*   1. The labels attached to the generated code are distinct; *)
(*   2. The mapping from segment ids to segment blocks provided by the FlatAsm environment *)
(*      are injective when its range is restricted to "valid blocks", i.e., *)
(*      blocks that correspond to valid segments; *)

(*   These two properties are establish by lemmas in the following module which in turn lead to *)
(*   the key lemma. *)
(*  **)

(* The following sequence of lemmas is used to prove  *)

(*    'update_map_gmap_range' *)

(* *)

Lemma tprog_id_in_seg_lists : forall gmap lmap p dsize csize tp id,
  transl_prog_with_map gmap lmap p dsize csize = OK tp ->
  id = code_segid \/ id = data_segid ->
  In id (map segid (list_of_segments tp)).
Proof.
  intros gmap lmap p dsize csize tp id H H0.
  monadInv H. unfold list_of_segments in *. simpl in *.
  destruct H0. auto.
  destruct H. auto. 
Qed.

(* The mapping from global identifers to segment labels generated by *)
(*    'update_map' always maps to valid segment labels *)
(*    (i.e., labels that will be mapped into valid segment blocks) *)

Lemma update_maps_cons:
  forall defs i def g l d c,
    update_maps g l d c ((i,def)::defs) =
    let '(g1,l1,d1,c1) := update_maps_def g l d c i def in
    update_maps g1 l1 d1 c1 defs.
Proof.
  unfold update_maps. intros. simpl. repeat destr.
Qed.

Theorem update_map_gmap_range1 : forall p gmap lmap dsize csize tp,
    make_maps p = (gmap, lmap, dsize, csize) ->
    transl_prog_with_map gmap lmap p dsize csize = OK tp ->
    forall id slbl, gmap id = Some slbl -> In (fst slbl) (map segid (list_of_segments tp)).
Proof.
  intros p gmap lmap dsize csize tp UPDATE TRANS id b GMAP.
  eapply tprog_id_in_seg_lists; eauto.
  exploit update_map_gmap_range; eauto.
  simpl. intuition.
Qed.


(* The following sequence of lemmas is used to prove  *)

(*    'transl_funs_gen_valid_code_labels' *)

(* *)

Lemma transl_instr_inv : forall ofs fid sid i x,
  transl_instr ofs fid sid i = OK x ->
  exists sblk, x = (i, sblk, fid) /\ sblk = mkSegBlock sid (Ptrofs.repr ofs) (Ptrofs.repr (instr_size i)).
Proof.
  intros. destruct i; simpl in H; inv H; eauto.
Qed.

Lemma transl_instrs_gen_valid_code_labels : forall instrs (gmap: GID_MAP_TYPE) i (tp:FlatAsm.program) sid ofs1 ofs2 ofs' instrs',
  (forall id b, gmap id = Some b -> In (fst b) (map segid (list_of_segments tp))) ->
  gmap i = Some (sid, ofs1) ->
  transl_instrs i sid ofs2 instrs = OK (ofs', instrs') ->
  code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) instrs'.
Proof.
  induction instrs; intros.
  - monadInv H1. red. intros. contradiction.
  - monadInv H1. 
    exploit transl_instr_inv; eauto. 
    intros (sblk & EQI & EQS). subst.
    assert (code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) x1).
      eapply IHinstrs; eauto.
    apply code_labels_are_valid_cons; auto.
    exploit (@gen_segblocks_in_valid instruction); eauto.
Qed.

Lemma transl_fun_gen_valid_code_labels : forall gmap i f f' (tp:FlatAsm.program),
  (forall id b, gmap id = Some b -> In (fst b) (map segid (list_of_segments tp))) ->
  transl_fun gmap i f = OK f' ->
  code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) (fn_code f').
Proof.
  intros gmap i f f' tp IN TRANSLF.
  monadInvX TRANSLF. destruct zle; try inv EQ2. simpl.
  eapply transl_instrs_gen_valid_code_labels; eauto.
Qed.

(* If the mapping from global identifers to segment labels always maps to valid labels, *)
(*    then the code generated by 'transl_funs' using the mapping must also have valid labels *)
Lemma transl_globdefs_gen_valid_code_labels : forall defs gmap tdefs (tp:FlatAsm.program),
  (forall id b, gmap id = Some b -> In (fst b) (map segid (list_of_segments tp))) ->
  transl_globdefs gmap defs = OK tdefs ->
  code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) (get_defs_code tdefs).
Proof.
  induction defs; intros.
  - monadInv H0. red. intros. inv H0.
  - destruct a. monadInv H0. destruct x. destruct p. destruct o. destruct g.
    destruct f. monadInv EQ. 
    apply code_labels_are_valid_app.
    eapply transl_fun_gen_valid_code_labels; eauto.
    eapply IHdefs; eauto.
    monadInvX EQ. simpl. eapply IHdefs; eauto.
    monadInvX EQ. simpl. eapply IHdefs; eauto.
    monadInvX EQ. simpl. eapply IHdefs; eauto.
Qed.



(**************************)
   
Section WITHTRANSF.

Variable prog: Asm.program.
Variable tprog: FlatAsm.program.
Hypothesis TRANSF: transf_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

(* This lemma makes use of  *)
   
(*      'update_map_gmap_range'  *)

(*    and  *)
 
(*      'transl_funs_gen_valid_code_labels'  *)

(*     to prove that the generated instructions have *)
(*     valid segment labels attached to them *)
   
Lemma target_code_labels_are_valid :
  code_labels_are_valid
    init_block (length (list_of_segments tprog))
    (gen_segblocks tprog)
    (get_program_code tprog).
Proof.
  unfold transf_program in TRANSF.
  repeat destr_in TRANSF.
  subst tge.
  unfold transl_prog_with_map in H0. monadInv H0. simpl.
  eapply transl_globdefs_gen_valid_code_labels; eauto.
  eapply update_map_gmap_range1; eauto.
  unfold transl_prog_with_map. rewrite EQ. simpl. auto.
Qed.

(* The key lemma *)
Lemma find_instr_self : forall i,
    code_labels_are_distinct (get_program_code tprog) ->
    In i (get_program_code tprog) ->
    Genv.find_instr tge
                    (Vptr (gen_segblocks tprog (segblock_id (snd (fst i)))) (segblock_start (snd (fst i)))) = Some i.
Proof.
  intros i DLBL IN. subst tge.
  unfold Genv.find_instr. unfold globalenv.
  erewrite <- add_globals_pres_genv_instrs; eauto. simpl.
  set (sbmap := (gen_segblocks tprog)).
  unfold gen_instrs_map.
  set (code := get_program_code tprog) in *.
  eapply acc_instrs_map_self; eauto.
  apply gen_segblocks_injective.
  set (tge := globalenv tprog).
  subst sbmap code.
  (* apply code_labels_are_valid_eq_map with (Genv.genv_segblocks tge). *)
  (* apply genv_gen_segblocks. *)
  apply target_code_labels_are_valid.
Qed.

Lemma transl_instr_segblock : forall ofs' id i i' sid,
      transl_instr (Ptrofs.unsigned ofs') id sid i = OK i' ->
      segblock_to_label (snd (fst i')) = (sid, ofs').
Proof.
  intros. 
  exploit transl_instr_inv; eauto.
  intros (sblk & EQI & EQS). subst.
  unfold segblock_to_label. simpl.
  rewrite Ptrofs.repr_unsigned. auto.
Qed.

Lemma find_instr_ofs_non_negative : forall code ofs i,
    find_instr ofs code = Some i -> ofs >= 0.
Proof.
  induction code; simpl; intros.
  - inv H.
  - destruct zeq. omega.
    apply IHcode in H. generalize (instr_size_positive a). omega.
Qed.

Lemma transl_instrs_ofs_bound: forall code code' id sid ofs fofs,
  transl_instrs id sid ofs code = OK (fofs, code') -> ofs <= fofs.
Proof.
  induction code; simpl; intros.
  - inv H. omega.
  - monadInv H. 
    exploit transl_instr_inv; eauto.
    intros (sblk & EQI & EQS). subst.
    apply IHcode in EQ1.
    generalize (instr_size_positive a). omega.
Qed.

Lemma find_instr_transl_instrs : forall code id sid i ofs ofs' fofs code',
    find_instr (Ptrofs.unsigned ofs) code = Some i ->
    transl_instrs id sid (Ptrofs.unsigned ofs') code = OK (fofs, code') ->
    fofs <= Ptrofs.max_unsigned ->
    exists i' ofs1, transl_instr ofs1 id sid i = OK i'
               /\ segblock_to_label (snd (fst i')) = (sid, Ptrofs.add ofs ofs')
               /\ In i' code'.
Proof.
  induction code; simpl; intros.
  - inv H.
  - monadInv H0. destruct zeq.
    + inv H. 
      exploit transl_instr_inv; eauto.
      intros (sblk & EQI & EQS). subst.
      eexists. exists (Ptrofs.unsigned ofs'). split.       
      unfold transl_instr. eauto. simpl.
      repeat rewrite Ptrofs.repr_unsigned.
      split. unfold segblock_to_label. simpl.
      rewrite Ptrofs.add_unsigned. rewrite e. simpl. rewrite Ptrofs.repr_unsigned. auto.
      auto.
    + exploit (IHcode id sid i
                      (Ptrofs.repr (Ptrofs.unsigned ofs - instr_size a))
                      (Ptrofs.repr (Ptrofs.unsigned ofs' + instr_size a))); eauto.
      rewrite Ptrofs.unsigned_repr. auto.
      generalize (find_instr_ofs_non_negative code (Ptrofs.unsigned ofs - instr_size a) i H).
      generalize (instr_size_positive a).
      generalize (Ptrofs.unsigned_range_2 ofs). intros. omega.
      rewrite Ptrofs.unsigned_repr. eauto.
      generalize (transl_instrs_ofs_bound code x1 id sid
                                          (Ptrofs.unsigned ofs' + instr_size a) fofs EQ1).
      generalize (Ptrofs.unsigned_range_2 ofs').
      generalize (instr_size_positive a). omega.
      intros (i' & ofs1 & TRANSI & SBEQ & IN).
      eexists; eexists; split. eauto. split.
      rewrite SBEQ. f_equal.
      rewrite Ptrofs.add_unsigned. repeat rewrite Ptrofs.unsigned_repr.
      replace (Ptrofs.unsigned ofs - instr_size a + (Ptrofs.unsigned ofs' + instr_size a)) with
              (Ptrofs.unsigned ofs + Ptrofs.unsigned ofs') by omega.
      rewrite <- Ptrofs.add_unsigned. auto.
      generalize (transl_instrs_ofs_bound code x1 id sid
                                          (Ptrofs.unsigned ofs' + instr_size a) fofs EQ1).
      generalize (Ptrofs.unsigned_range_2 ofs').
      generalize (instr_size_positive a). omega.
      generalize (find_instr_ofs_non_negative code (Ptrofs.unsigned ofs - instr_size a) i H).
      generalize (instr_size_positive a).
      generalize (Ptrofs.unsigned_range_2 ofs). intros. omega.
      apply in_cons. auto.
Qed.

Lemma find_instr_transl_fun : forall id f f' ofs i gmap s,
    find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    transl_fun gmap id f = OK f' ->
    gmap id = Some s ->
    exists i' ofs1, transl_instr ofs1 id (fst s) i = OK i'
               /\ segblock_to_label (snd (fst i')) = (fst s, Ptrofs.add ofs (snd s))
               /\ In i' (fn_code f').
Proof.
  intros id f f' ofs i gmap s FINSTR TRANSFUN GMAP.
  unfold transl_fun in TRANSFUN. rewrite GMAP in TRANSFUN.
  monadInvX TRANSFUN. destruct zle; inversion EQ1; clear EQ1.
  exploit find_instr_transl_instrs; eauto.
Qed.

(* End WITHTRANSF. *)

(* End AGREE_SMINJ_INSTR. *)



(** Lemmas for proving agree_sminj_glob **)
(* Module AGREE_SMINJ_GLOB. *)

(* Section WITHTRANSF. *)

(* Variable prog: Asm.program. *)
(* Variable tprog: FlatAsm.program. *)
(* Hypothesis TRANSF: transf_program prog = OK tprog. *)

(* Let ge := Genv.globalenv prog. *)
(* Let tge := globalenv tprog. *)

Lemma lnr_transf: list_norepet (map fst (AST.prog_defs prog)).
Proof.
  unfold transf_program in TRANSF.
  repeat destr_in TRANSF.
  destruct w; auto.
Qed.

Lemma update_map_gmap_domain : forall gmap lmap dsize csize id slbl,
    make_maps prog = (gmap, lmap, dsize, csize) ->
    gmap id = Some slbl ->
    In id (prog_defs_names prog).
Proof.
  intros gmap lmap dsize csize id slbl UPDATE GMAP.
  unfold make_maps in UPDATE.
  destruct (updates_gmap_in _ _ _ _ _ _ _ _ _ UPDATE _ _ GMAP) as [IN | EQ]. 2: inv EQ. auto.
Qed.

(* End WITHTRANSF. *)


Lemma defs_nodup_labels : forall defs f id,
    defs_no_duplicated_labels defs ->
    In (id, Some (Gfun (Internal f))) defs ->
    list_norepet (labels (Asm.fn_code f)).
Proof.
  intros.
  red in H. rewrite Forall_forall in H.
  exploit H. apply in_map. eauto. simpl. auto.
Qed.

Ltac solve_label_pos_inv :=
  match goal with
  | [ |- _ <> Asm.Plabel _ /\ label_pos _ _ _ = Some _] =>
    split; solve_label_pos_inv
  | [ |- _ <> Asm.Plabel _ ] =>
    unfold not; inversion 1
  | [ |- label_pos _ _ _ = Some _ ] => auto
  | _ => idtac
  end.

Lemma label_pos_inv : forall l ofs a instrs z,
    label_pos l ofs (a :: instrs) = Some z ->
    (a = Asm.Plabel l /\ z = ofs + instr_size a)
    \/ (a <> Asm.Plabel l /\ label_pos l (ofs + instr_size a) instrs = Some z).
Proof.
  intros l ofs a instrs z H.
  simpl in H. unfold Asm.is_label in H; simpl in H.
  destruct a; try now (right; solve_label_pos_inv).
  destruct peq.
  - subst. left. inv H. auto.
  - right. simpl. split. unfold not. inversion 1. congruence.
    auto.
Qed.

Lemma update_instrs_map_pres_lmap_2 : forall instrs l id lmap lmap' csize csize',
    ~ In (Asm.Plabel l) instrs ->
    update_instrs lmap csize id instrs = (lmap',csize') ->
    lmap' id l = lmap id l.
Proof.
  unfold update_instrs.
  induction instrs; simpl; intros; auto.
  - inv H0; auto.
  - assert (Asm.Plabel l <> a /\ ~ In (Asm.Plabel l) instrs) as H1
        by (apply not_in_cons; auto). destruct H1.
    erewrite IHinstrs. 2: auto. 2: eauto.
    destr.
    unfold update_label_map. rewrite peq_true. rewrite peq_false. auto.
    unfold is_label in Heqo. destr_in Heqo.
Qed.

Lemma update_instrs_cons:
  forall lmap csize id ins insns,
    update_instrs lmap csize id (ins::insns) =
    let (lmap',csize') := update_instr lmap csize id ins in
    update_instrs lmap' csize' id insns.
Proof.
  Opaque update_instr.
  unfold update_instrs. simpl. intros.
  destr.
  Transparent update_instr.
Qed.

Lemma update_instrs_other_label:
  forall l id ins lmap csize lmap' csize',
    ~ In l (labels ins) ->
    update_instrs lmap csize id ins = (lmap',csize') ->
    lmap' id l = lmap id l.
Proof.
  induction ins; simpl; intros; eauto. inv H0. auto.
  rewrite update_instrs_cons in H0. destr_in H0.
  unfold update_instr in Heqp.
  repeat destr_in Heqp.
  eapply IHins in H0.
  - rewrite H0. unfold update_label_map. rewrite peq_true, peq_false; auto. simpl in H; auto.
  - simpl in H; auto.
  - eapply IHins in H0; eauto.
Qed.

Lemma update_instrs_map_lmap_inversion : forall instrs csize l z ofs id csize' lmap lmap' l'
    (MAXSIZE: csize' <= Ptrofs.max_unsigned)
    (MINSIZE: csize  >= 0)
    (LNR: list_norepet (labels instrs))
    (LPOS: label_pos l ofs instrs = Some z)
    (UI: update_instrs lmap csize id instrs = (lmap', csize'))
    (LM: lmap' id l = Some l'),
    l' = (code_segid , Ptrofs.repr (csize + z - ofs)) /\ 0 <= (csize + z - ofs) <= Ptrofs.max_unsigned.
Proof.
  induction instrs; simpl; intros; auto.
  - inv LPOS.
  - apply label_pos_inv in LPOS. destruct LPOS as [[LAB EQ] | [NLAB LPOS]].
    + subst. simpl in *. subst. simpl in *.
      rewrite update_instrs_cons in UI. destr_in UI.
      erewrite update_instrs_other_label in LM. 3: eauto. 2: inv LNR; auto.
      unfold update_instr in Heqp. repeat destr_in Heqp.
      unfold is_label in Heqo; repeat destr_in Heqo. 
      unfold update_label_map in LM.
      rewrite ! peq_true in LM. inv LM. unfold code_label.
      split.
      f_equal. f_equal. omega.
      rewrite (update_instrs_code_size _ _ _ _ _ _ UI) in MAXSIZE.
      generalize (instr_size_positive (Asm.Plabel l1)).
      generalize (code_size_non_neg instrs). omega.
      unfold is_label in Heqo;  simpl in Heqo; repeat destr_in Heqo.
    + rewrite update_instrs_cons in UI. destr_in UI.
      specialize (IHinstrs z0 l z (ofs + instr_size a) id csize' l0 lmap' l').
      inv Heqp.
      exploit IHinstrs; eauto.
      generalize (instr_size_positive a); omega.
      destr_in LNR; auto. inv LNR; auto.
      intros (A & B).
      rewrite A. split. f_equal. f_equal. omega. omega.
Qed.

Lemma label_pos_min_size : forall instrs l ofs ofs',
    label_pos l ofs instrs = Some ofs' -> ofs <= ofs'.
Proof.
  induction instrs; intros.
  - simpl in *. inv H.
  - simpl in *.
    generalize (instr_size_positive a). intros H0. 
    repeat destr_in H. omega.
    eapply IHinstrs in H2. omega.
Qed.

Lemma size_fun_pos:
  forall o,
    0 <= size_fun o.
Proof.
  intros.
  unfold size_fun. repeat destr; try omega.
  generalize (code_size_non_neg (Asm.fn_code f0)); omega.
Qed.

Lemma update_funs_map_lpos_inversion: forall defs id l f z gmap lmap csize dsize csize' dsize' gmap' lmap' l'
    (DDISTINCT : list_norepet (map fst defs))
    (LDISTINCT : list_norepet (labels (Asm.fn_code f)))
    (MAXSIZE   : csize' <= Ptrofs.max_unsigned)
    (MINSIZE   : csize >= 0)
    (AL: (alignw | csize)),
    In (id, Some (Gfun (Internal f))) defs ->
    label_pos l 0 (Asm.fn_code f) = Some z ->
    update_maps gmap lmap dsize csize defs = (gmap', lmap', dsize', csize') ->
    lmap' id l = Some l' ->
    (exists slbl : seglabel, gmap' id = Some slbl
                        /\ fst slbl = fst l'
                        /\ Ptrofs.add (snd slbl) (Ptrofs.repr z) = snd l').
Proof.
  induction defs; intros.
  - contradiction.
  - inv DDISTINCT. inv H.
    + simpl in *.
      rewrite update_maps_cons in H1. repeat destr_in H1.
      simpl in Heqp. repeat destr_in Heqp.
      erewrite update_gmap_not_in. 2: eauto. 2: auto.
      unfold update_gid_map. rewrite peq_true.
      eexists. split. eauto. unfold code_label. simpl.
      erewrite update_lmap_not_in in H2. 3: eauto. 2: auto. 2: auto.
      generalize (csize_mono _ _ _ _ _ _ _ _ _ H3 (alignw_divides _ )).
      intros.
      exploit update_instrs_map_lmap_inversion. 4: eauto. 4: eauto. 4: eauto.
      generalize (alignw_le z2). omega. omega. auto.
      intros (A & B). subst. simpl. split. auto.
      rewrite Ptrofs.add_unsigned.
      f_equal. rewrite Ptrofs.unsigned_repr. rewrite Ptrofs.unsigned_repr.
      omega.
      assert (0 <= z). eapply (label_pos_min_size (Asm.fn_code f) l 0); eauto.
      omega.
      apply update_instrs_code_size in Heqp0.
      generalize (alignw_le z2).
      subst.
      generalize (code_size_non_neg (Asm.fn_code f)). omega. eauto.
    + destruct a.
      rewrite update_maps_cons in H1. repeat destr_in H1.
      assert (i <> id).
      {
        simpl in *.
        apply in_map with (f:=fst) in H3; simpl in *. congruence.
      }
      eapply IHdefs; auto. eauto. 4: auto. 4: eauto. 4: eauto. auto. 3: auto.
      erewrite update_csize with (csize':=z0). 2: eauto.
      generalize (alignw_le (size_fun o)) (size_fun_pos o); omega.
      auto.
      eapply update_csize_div; eauto.
Qed.

(* Section WITHTRANSF. *)

(* Variable prog: Asm.program. *)
(* Variable tprog: FlatAsm.program. *)
(* Hypothesis TRANSF: transf_program prog = OK tprog. *)

(* Let ge := Genv.globalenv prog. *)
(* Let tge := globalenv tprog. *)

Lemma update_map_lmap_inversion : forall id f gmap lmap dsize csize l z l',
    (dsize + csize) <= Ptrofs.max_unsigned ->
    list_norepet (map fst (AST.prog_defs prog)) ->
    list_norepet (labels (Asm.fn_code f)) ->
    In (id, Some (Gfun (Internal f))) (AST.prog_defs prog) ->
    make_maps prog = (gmap, lmap, dsize, csize) ->
    label_pos l 0 (Asm.fn_code f) = Some z ->
    lmap id l = Some l' ->
    exists slbl, gmap id = Some slbl /\
            fst slbl = fst l' /\
            Ptrofs.add (snd slbl) (Ptrofs.repr z) = snd l'.
Proof.
  intros id f gmap lmap dsize csize l z l' SZBOUND DDISTINCT LDISTINCT IN UPDATE LPOS LMAP.
  unfold make_maps in UPDATE.
  eapply update_funs_map_lpos_inversion. 8: eauto. all: eauto.
  generalize (dsize_mono _ _ _ _ _ _ _ _ _ UPDATE).
  omega. omega.
  apply Z.divide_0_r.
Qed.

End WITHTRANSF.

(* End AGREE_SMINJ_LBL. *)



Section WITHMEMORYMODEL.
  
Context `{memory_model: Mem.MemoryModel }.
Existing Instance inject_perm_all.


Definition match_prog (p: Asm.program) (tp: FlatAsm.program) :=
  transf_program p = OK tp.

Section PRESERVATION.

Variable prog: Asm.program.
Variable tprog: FlatAsm.program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

Definition regset_inject (j:meminj) (rs rs' : regset) : Prop :=
  forall r, Val.inject j (rs r) (rs' r).

(** Properties about the memory injection from Asm to the flat memory *)    
Record match_inj (mj: meminj) : Type :=
  mk_match_inj {

      agree_inj_instr :  forall b b' f ofs ofs' i,
        Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) -> 
        Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
        mj b = Some (b', ofs') -> 
        exists id i' sid ofs1, 
          Genv.find_instr tge (Vptr b' (Ptrofs.add ofs (Ptrofs.repr ofs'))) = Some i' /\
          Globalenvs.Genv.find_symbol ge id = Some b /\
          transl_instr ofs1 id sid i = OK i';

      (* agree_sminj_glob : forall id gloc, *)
      (*     gm id = Some gloc -> *)
      (*     exists ofs' b b',  *)
      (*       Globalenvs.Genv.find_symbol ge id = Some b /\ *)
      (*       Genv.symbol_address tge gloc Ptrofs.zero = Vptr b' ofs' /\ *)
      (*       mj b = Some (b', Ptrofs.unsigned ofs'); *)

      agree_inj_glob : forall id b,
          Globalenvs.Genv.find_symbol ge id = Some b ->
          exists b' ofs', Genv.find_symbol tge id = Some (b', ofs') /\
          mj b = Some (b', Ptrofs.unsigned ofs');

      agree_inj_lbl : forall id b f l z,
          Globalenvs.Genv.find_symbol ge id = Some b ->
          Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
          label_pos l 0 (Asm.fn_code f) = Some z ->
          Val.inject mj (Vptr b (Ptrofs.repr z)) (Genv.label_address tge id l);      
    }.

(* Definition gid_map_for_undef_syms (gm: GID_MAP_TYPE) := *)
(*   forall id, Globalenvs.Genv.find_symbol ge id = None -> gm id = None. *)


Definition valid_instr_offset_is_internal (mj:meminj) :=
  forall b b' f ofs i ofs',
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    mj b = Some (b', ofs') ->
    Genv.genv_internal_codeblock tge b' = true.    


Definition extfun_entry_is_external (mj:meminj) :=
  forall b b' f ofs,
    Globalenvs.Genv.find_funct_ptr ge b = Some (External f) ->
    mj b = Some (b', ofs) ->
    Genv.genv_internal_codeblock tge b' = false.


Definition def_frame_inj m := (flat_frameinj (length (Mem.stack m))).

Lemma store_pres_def_frame_inj : forall chunk m1 b ofs v m1',
    Mem.store chunk m1 b ofs v = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  repeat erewrite Mem.push_new_stage_stack. simpl.
  exploit Mem.store_stack_blocks; eauto. intros. rewrite H0.
  auto.
Qed.

Lemma storev_pres_def_frame_inj : forall chunk m1 v1 v2 m1',
    Mem.storev chunk m1 v1 v2 = Some m1' ->
    def_frame_inj m1= def_frame_inj m1'.
Proof.
  intros until m1'. unfold Mem.storev.
  destruct v1; try congruence.
  intros STORE.
  eapply store_pres_def_frame_inj; eauto.
Qed.


Lemma store_mapped_inject' : 
  forall (f : meminj) (chunk : memory_chunk) 
    (m1 : mem) (b1 : block) (ofs : Z) (v1 : val) 
    (n1 m2 : mem) (b2 : block) (delta : Z) (v2 : val),
    Mem.inject f (def_frame_inj m1) m1 m2 ->
    Mem.store chunk m1 b1 ofs v1 = Some n1 ->
    f b1 = Some (b2, delta) ->
    Val.inject f v1 v2 ->
    exists n2 : mem,
      Mem.store chunk m2 b2 (ofs + delta) v2 = Some n2 /\
      Mem.inject f (def_frame_inj n1) n1 n2.
Proof.
  intros. exploit Mem.store_mapped_inject; eauto. 
  intros (n2 & STORE & MINJ).
  eexists. split. eauto.
  erewrite <- store_pres_def_frame_inj; eauto.
Qed.

Theorem storev_mapped_inject':
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  Mem.inject f (def_frame_inj m1) m1 m2 ->
  Mem.storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    Mem.storev chunk m2 a2 v2 = Some n2 /\ Mem.inject f (def_frame_inj n1) n1 n2.
Proof.
  intros. exploit Mem.storev_mapped_inject; eauto. 
  intros (n2 & STORE & MINJ).
  eexists. split. eauto.
  erewrite <- storev_pres_def_frame_inj; eauto.
Qed.

Definition match_find_funct (j:meminj) :=
  forall b f ofs b',
  Globalenvs.Genv.find_funct_ptr ge b = Some (External f) ->
  j b = Some (b', ofs) ->
  Genv.find_funct tge (Vptr b' (Ptrofs.repr ofs)) = Some (External f).

Definition glob_block_valid (m:mem) := 
  forall b g, Globalenvs.Genv.find_def ge b = Some g -> Mem.valid_block m b.

Inductive match_states: state -> state -> Prop :=
| match_states_intro: forall (j:meminj) (rs: regset) (m: mem) (rs': regset) (m':mem)
                        (* (gm: GID_MAP_TYPE) (lm: LABEL_MAP_TYPE) *)
                        (MINJ: Mem.inject j (def_frame_inj m) m m')
                        (MATCHSMINJ: match_inj j)
                        (* (GINJFLATMEM: globs_inj_into_flatmem j) *)
                        (INSTRINTERNAL: valid_instr_offset_is_internal j)
                        (EXTEXTERNAL: extfun_entry_is_external j)
                        (MATCHFINDFUNCT: match_find_funct j)
                        (RSINJ: regset_inject j rs rs')
                        (GBVALID: glob_block_valid m),
                        (* (GMUNDEF: gid_map_for_undef_syms gm), *)
    match_states (State rs m) (State rs' m').


Definition init_meminj : meminj :=
  let ge := Genv.globalenv prog in
  let tge := globalenv tprog in
  fun b =>
    (* (genv_next ge) is the stack block of the source program *)
    if eq_block b (Globalenvs.Genv.genv_next ge)
    then Some (Genv.genv_next tge, 0)
    else
      match (Genv.invert_symbol ge b) with
      | None => None
      | Some id =>
        match Genv.find_symbol tge id with
        | None => None
        | Some (b,ofs) => Some (b, Ptrofs.unsigned ofs)
        end

        (* match (gmap id) with *)
        (* | None => None *)
        (* | Some slbl => Some (Genv.symbol_block_offset tge slbl) *)
        (* end *)
      end.


Lemma in_transl_instrs:
  forall i si c o o' sz x1
    (RNG: 0 <= sz <= Ptrofs.max_unsigned)
    (POS: 0 <= o')
    (TI: transl_instrs i si o' c = OK (sz, x1))
    si'
    (IN: In (si', o) (map (fun i1 => (segblock_id (snd (fst i1)), segblock_start (snd (fst i1)))) x1)),
    si' = si /\ o' <= Ptrofs.unsigned o < o' + code_size c.
Proof.
  induction c; simpl; intros; eauto.
  - inv TI. simpl in IN. easy. 
  - monadInv TI. 
    exploit transl_instr_inv; eauto.
    intros (sblk & EQI & EQS). subst.
    simpl in IN.
    destruct IN as [IN|IN].
    + inv IN. simpl. split; auto.
      rewrite Ptrofs.unsigned_repr.
      generalize (instr_size_positive a) (code_size_non_neg c); omega.
      split. omega.
      generalize (transl_instrs_ofs_bound _ _ _ _ _ _ EQ1).
      generalize (instr_size_positive a); omega.
    + generalize (instr_size_positive a); intros.
      eapply IHc in IN. 4: eauto. destruct IN; split; auto. omega. auto. omega.
Qed.


Lemma transl_instrs_diff_labels:
  forall i si c
    (* (lnr : list_norepet (labels c)) *)
    (* (lmap_inj: forall i1 i2 l1 l2 sl1 sl2, (i1,l1) <> (i2,l2) -> lmap i1 l1 = Some sl1 -> lmap i2 l2 = Some sl2 -> *)
    (*                                   sl1 <> sl2) *)
    sz ofs c'
    (RNG: 0 <= sz <= Ptrofs.max_unsigned)
    (POS: 0 <= ofs)
    (TI : transl_instrs i si ofs c = OK (sz, c')),
    list_norepet (map (fun i1 => segblock_to_label (snd (fst i1))) c').
Proof.
  induction c; simpl; intros; eauto.
  - inv TI. simpl. constructor.
  - monadInv TI.
    exploit transl_instr_inv; eauto.
    intros (sblk & EQI & EQS). subst.
    (* trim IHc. *)
    (* { *)
    (*   destr_in lnr. inv lnr; auto. *)
    (* } *)
    (* trim IHc. eauto. *)
    simpl.
    constructor; eauto.
    clear IHc. 
    intro IN.
    simpl in IN.
    unfold segblock_to_label in IN. simpl in IN.
    eapply in_transl_instrs in IN. 4: eauto. 2: auto.
    rewrite Ptrofs.unsigned_repr in IN. 
    generalize (instr_size_positive a). omega. split. auto.
    generalize (transl_instrs_ofs_bound _ _ _ _ _ _ EQ1).
    generalize (instr_size_positive a); omega.
    generalize (instr_size_positive a); omega.
    eapply IHc. 3: eauto. auto.
    generalize (instr_size_positive a); omega.
Qed.

Lemma transl_globdef_distinct_code_labels:
  forall gmap i o p 
    (* (GNDL: globdef_no_duplicated_labels o = true) *)
    (TG : transl_globdef gmap i o = OK p),
    list_norepet (map (fun i0  => segblock_to_label (snd (fst i0))) (get_def_code p)).
Proof.
  intros.
  unfold transl_globdef in TG.
  repeat destr_in TG.
  - monadInv H0.
    unfold transl_fun in EQ. repeat destr_in EQ.
    monadInv H0. repeat destr_in EQ0.
    simpl. eapply transl_instrs_diff_labels; eauto. split; auto.
    generalize (transl_instrs_ofs_bound _ _ _ _ _ _ EQ). generalize (Ptrofs.unsigned_range i0); omega.
    apply Ptrofs.unsigned_range.
  - constructor.
  - constructor.
  - constructor.
Qed.

(* Lemma transl_globdef_gmap: *)
(*   forall gmap i o d ins c, *)
(*     transl_globdef gmap i o = OK d -> *)
(*     get_def_code d = (ins::c) -> *)
(*     exists s, gmap i = Some s. *)
(* Proof. *)
(*   intros. destruct o. destruct g. destruct f. *)
(*   - monadInv H. monadInvX EQ. eexists; eauto. *)
(*   - monadInv H. *)
(*   - simpl in H. monadInvX H. *)
(*   - monadInv H. *)
(* Qed. *)

(* Lemma transl_globdefs_gmap: *)
(*   forall gmap l gdefs ins c, *)
(*     transl_globdefs gmap l = OK (gdefs, c) -> *)
(*     Forall (fun '(i,d) => d = None \/ exists s, gmap i = Some s) l. *)
(* Proof. *)
(*   induction l; simpl; intros. *)
(*   constructor. *)
(*   destr_in H. monadInv H. subst. constructor; eauto. *)
(*   eapply transl_globdef_gmap. eauto. *)
(* Qed. *)


Lemma in_transl_globdef:
  forall gmap i o p0 
    (EQ : transl_globdef gmap i o = OK p0)
    x
    (IN: In x (map (fun i0  => segblock_to_label (snd (fst i0))) (get_def_code p0))),
    exists s,
      gmap i = Some s /\
      fst x = fst s /\ Ptrofs.unsigned (snd s) <= Ptrofs.unsigned (snd x) < Ptrofs.unsigned (snd s) + odef_size o.
Proof.
  intros.
  unfold transl_globdef in EQ.
  repeat destr_in EQ.
  - monadInv H0. simpl in IN. unfold transl_fun in EQ.
    repeat destr_in EQ. eexists; split. eauto. monadInv H0. simpl.
    repeat destr_in EQ0. simpl in *.
    destruct x. simpl in *.
    exploit in_transl_instrs. 3: apply EQ.
    generalize (transl_instrs_ofs_bound _ _ _ _ _ _ EQ). generalize (Ptrofs.unsigned_range i0); omega.
    apply Ptrofs.unsigned_range.
    subst. simpl. eauto.
    auto.
  - easy.
  - easy.
  - easy.
Qed.

Lemma in_transl_globdefs:
  forall gmap l gdefs 
    (EQ : transl_globdefs gmap l = OK gdefs)
    x
    (IN: In x (map (fun i0 => segblock_to_label (snd (fst i0))) (get_defs_code gdefs))),
          exists i def s,
            In (i, def) l /\
            gmap i = Some s /\
            fst x = fst s /\ Ptrofs.unsigned (snd s) <= Ptrofs.unsigned (snd x) < Ptrofs.unsigned (snd s) + odef_size def.
Proof.
  induction l; simpl; intros; eauto. inv EQ. easy.
  repeat destr_in EQ.
  monadInv H0.
  - specialize (IHl _ EQ1).
    simpl in IN. rewrite map_app, in_app in IN.
    destruct IN as [IN|IN].
    exploit in_transl_globdef; eauto.
    intros (s & G & FST & RNG).
    exists i, o, s; repeat apply conj; auto; omega.
    exploit IHl; eauto.
    intros (i0 & def & s & INl & G & FST & RNG).
    exists i0, def, s; repeat apply conj; auto; omega.
Qed.

Definition gmap_inj (gmap: GID_MAP_TYPE) (l: list (ident * option _)): Prop :=
  forall i1 i2 d1 d2 s1 s2 o1 o2,
    In (i1, d1) l ->
    In (i2, d2) l ->
    i1 <> i2 ->
    gmap i1 = Some (s1, o1) ->
    gmap i2 = Some (s2, o2) ->
    s1 <> s2 \/ Ptrofs.unsigned o1 + odef_size d1 <= Ptrofs.unsigned o2 \/ Ptrofs.unsigned o2 + odef_size d2 <= Ptrofs.unsigned o1.

Lemma gmap_inj_inv:
  forall gmap a b,
    gmap_inj gmap (a::b) ->
    gmap_inj gmap b.
Proof.
  unfold gmap_inj; intros; eauto.
  eapply H; simpl; eauto.
Qed.

Ltac ereplace t :=
  match type of t with
  | ?ty => let x := fresh in evar (x : ty); replace t with x; unfold x
  end.

Lemma transl_globdef_distinct_code_labels'
     : forall (gmap : GID_MAP_TYPE) (i : ident) (o : option (globdef Asm.fundef unit)) (p : ident * option gdef * segblock),
       transl_globdef gmap i o = OK p -> 
       list_norepet (map (fun '(_,blk,_) => segblock_to_label blk) (get_def_code p)).
Proof.
  intros.
  exploit transl_globdef_distinct_code_labels; eauto.
  intros. rewrite map_ext with 
              (g := (fun i0 => segblock_to_label (snd (fst i0)))). auto.
  intros. destruct a. destruct p0. auto.
Qed.

Lemma in_segblock_eq : forall a (c: list (instruction * segblock * ident)),
 In a (map (fun '(_, blk, _) => segblock_to_label blk) c) <->
 In a (map (fun i => segblock_to_label (snd (fst i))) c).
Proof.
  intros. rewrite map_ext with 
              (g := (fun i0 => segblock_to_label (snd (fst i0)))). auto.
  split; auto.
  intros. destruct a0. destruct p. auto.
Qed.

Lemma transl_globdefs_distinct_code_labels:
  forall gmap prog (GINJ: gmap_inj gmap (AST.prog_defs prog)) tgdefs,
    transl_globdefs gmap (AST.prog_defs prog) = OK tgdefs ->
    wf_prog prog ->
    code_labels_are_distinct (get_defs_code tgdefs).
Proof.
  intros gmap prog0 GINJ tgdefs TG WF. inv WF.
  revert TG GINJ wf_prog_not_empty wf_prog_norepet_defs wf_prog_norepet_labels.
  generalize (AST.prog_defs prog0). intro l.
  intros TG GINJ DNE NDD DNDL.
  red.
  revert l tgdefs TG GINJ DNE NDD DNDL.
  induction l; simpl; intros; eauto.
  - inv TG. simpl. constructor.
  - inv NDD. inv DNDL. inv DNE. destr_in TG. monadInv TG.
    repeat destr_in EQ2; eauto. simpl.
    rewrite map_app. rewrite list_norepet_app.
    repeat apply conj; eauto.
    + eapply transl_globdef_distinct_code_labels'; eauto.
    + eapply IHl; eauto using gmap_inj_inv.
    + red.
      intros (sx & ox) (sy & oy) INx INy.
      exploit in_transl_globdef. eauto.
      rewrite <- in_segblock_eq. eauto.
      simpl. intros (s & G & FST & RNG). subst.
      exploit in_transl_globdefs. eauto. 
      rewrite <- in_segblock_eq. eauto.
      simpl. intros (i0 & def & s' & INl & G' & FST' & RNG'). subst.
      destruct s, s'. simpl in *. intro A; inv A.
      exploit GINJ. left; reflexivity.
      right; eauto.
      intro; subst. apply H1.
      ereplace i0. apply in_map, INl. reflexivity.
      eauto. eauto. intros [A | A]. congruence. omega.
Qed.

Lemma update_maps_code_lt:
  forall defs g l d c g' l' d' c' i s
    (RNG: 0 <= c <= Ptrofs.max_unsigned)
    (RNG: 0 <= c' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c defs = (g', l', d', c'))
    (AL: (alignw | c))
    (LNR: list_norepet (map fst defs))
    f
    (IN: In (i, Some (Gfun (Internal f))) defs)
    (* o *)
    (* (POS: 0 <= o < code_size (Asm.fn_code f)) *)
    (BEFORE: g i = None)
    (AFTER: g' i = Some s),
    c <= Ptrofs.unsigned (snd s) /\ Ptrofs.unsigned (snd s) + code_size (Asm.fn_code f) <= c'.
Proof.
  induction defs; simpl; intros; eauto. easy.
  destruct IN.
  - subst.
    rewrite update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    erewrite update_gmap_not_in in AFTER. 2: eauto. 2: inv LNR; auto.
    erewrite update_gmap in AFTER. 2: eauto.
    rewrite peq_true in AFTER. inv AFTER.
    unfold code_label; simpl.
    rewrite Ptrofs.unsigned_repr; auto.
    exploit update_csize_div. eauto. eauto. intro.
    eapply update_csize in Heqp.
    eapply csize_mono in H0. subst. simpl in H0.
    generalize (alignw_le (code_size (Asm.fn_code f))). omega.
    inv LNR; auto. auto.
  - destruct a. rewrite update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    exploit update_csize_div; eauto.  intro.
    inv LNR.
    assert (c <= z). {
      exploit update_csize; eauto. intro; subst.
      generalize (alignw_le (size_fun o)) (size_fun_pos o).
      intros. omega.
    }
    assert (z <= c') by (eapply csize_mono; eauto).
    exploit IHdefs. 3: eauto. omega. auto. auto. auto. eauto. eauto.
    erewrite update_gmap; eauto. rewrite peq_false; auto.
    intro; subst. apply H4.
    apply in_map with (f:= fst) in H. simpl in H; auto. eauto.
    omega.
Qed.

Lemma update_maps_code_lt':
  forall defs g l d c g' l' d' c' i s
    (RNG: 0 <= c <= Ptrofs.max_unsigned)
    (RNG: 0 <= c' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c defs = (g', l', d', c'))
    (AL: (alignw | c))
    (LNR: list_norepet (map fst defs))
    def
    (IN: In (i, def) defs)
    (BEFORE: g i = None)
    (GMAP: g' i = Some (code_segid, s)),
    c <= Ptrofs.unsigned s /\ Ptrofs.unsigned s + odef_size def <= c'.
Proof.
  intros.
  simpl in *.
  assert (exists f, def = Some (Gfun (Internal f))).
  {
    destruct (in_split _ _ IN) as (bef & aft & EQ). rewrite EQ in *.
    rewrite update_maps_app in UPDATE.
    repeat destr_in UPDATE. simpl in *.
    rewrite update_maps_cons in H0. repeat destr_in H0.
    erewrite update_gmap_not_in in GMAP. 2: eauto.
    erewrite update_gmap in GMAP. 2: eauto. rewrite peq_true in GMAP.
    repeat destr_in GMAP; unfold code_label, data_label; simpl; eauto.
    erewrite update_gmap_not_in in H0. 2: eauto. congruence.
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in DISJ. intro II; destruct (DISJ i i II (or_introl eq_refl) eq_refl).
    erewrite update_gmap_not_in in H0. 2: eauto. congruence.
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in DISJ. intro II; destruct (DISJ i i II (or_introl eq_refl) eq_refl).
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in LNR2; inv LNR2; auto.
  }
  destruct H; subst.
  simpl. exploit update_maps_code_lt. 3: eauto. 5: eauto. all: eauto.
Qed.

Lemma update_maps_data_lt:
  forall defs g l d c g' l' d' c' i s
    (RNG: 0 <= d <= Ptrofs.max_unsigned)
    (RNG: 0 <= d' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c defs = (g', l', d', c'))
    (LNR: list_norepet (map fst defs))
    gv
    (IN: In (i, Some (Gvar gv)) defs)
    (BEFORE: g i = None)
    (AFTER: g' i = Some s),
    d <= Ptrofs.unsigned (snd s) /\ Ptrofs.unsigned (snd s) + init_data_list_size (gvar_init gv) <= d'.
Proof.
  induction defs; simpl; intros; eauto. easy.
  destruct IN.
  - subst.
    rewrite update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    erewrite update_gmap_not_in in AFTER. 2: eauto. 2: inv LNR; auto.
    erewrite update_gmap in AFTER. 2: eauto.
    rewrite peq_true in AFTER. inv AFTER.
    unfold code_label; simpl.
    rewrite Ptrofs.unsigned_repr; auto.
    eapply update_dsize in Heqp.
    eapply dsize_mono in H0. subst. simpl in H0.
    generalize (alignw_le (init_data_list_size (gvar_init gv))).
    omega.
  - destruct a. rewrite update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    inv LNR.
    assert (d <= z0). {
      exploit update_dsize; eauto. intro; subst.
      generalize (alignw_le (size_gvar o)). cut (size_gvar o >= 0).
      intros. omega.
      unfold size_gvar. repeat destr; try omega. apply init_data_list_size_pos.
    }
    assert (z0 <= d') by (eapply dsize_mono; eauto).
    exploit IHdefs. 3: eauto. omega. auto. auto. eauto. eauto.
    erewrite update_gmap; eauto. rewrite peq_false; auto.
    intro; subst. apply H3.
    apply in_map with (f:= fst) in H. simpl in H; auto. eauto.
    omega.
Qed.

Lemma update_maps_data_lt':
  forall defs g l d c g' l' d' c' i s
    (RNG: 0 <= d <= Ptrofs.max_unsigned)
    (RNG: 0 <= d' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c defs = (g', l', d', c'))
    (LNR: list_norepet (map fst defs))
    def
    (IN: In (i, def) defs)
    (BEFORE: g i = None)
    (GMAP: g' i = Some (data_segid, s)),
    d <= Ptrofs.unsigned s /\ Ptrofs.unsigned s + odef_size def <= d'.
Proof.
  intros.
  simpl in *.
  assert (exists gv, def = Some (Gvar gv)).
  {
    destruct (in_split _ _ IN) as (bef & aft & EQ). rewrite EQ in *.
    rewrite update_maps_app in UPDATE.
    repeat destr_in UPDATE. simpl in *.
    rewrite update_maps_cons in H0. repeat destr_in H0.
    erewrite update_gmap_not_in in GMAP. 2: eauto.
    erewrite update_gmap in GMAP. 2: eauto. rewrite peq_true in GMAP.
    repeat destr_in GMAP; unfold code_label, data_label; simpl; eauto.
    erewrite update_gmap_not_in in H0. 2: eauto. congruence.
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in DISJ. intro II; destruct (DISJ i i II (or_introl eq_refl) eq_refl).
    erewrite update_gmap_not_in in H0. 2: eauto. congruence.
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in DISJ. intro II; destruct (DISJ i i II (or_introl eq_refl) eq_refl).
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in LNR2; inv LNR2; auto.
  }
  destruct H; subst.
  exploit update_maps_data_lt. 3: eauto. 5: eauto. all: eauto.
Qed.

(* Lemma update_maps_extfun_lt: *)
(*   forall defs g l d c e g' l' d' c' e' i s *)
(*     (RNG: 0 <= e <= Ptrofs.max_unsigned) *)
(*     (RNG: 0 <= e' <= Ptrofs.max_unsigned) *)
(*     (UPDATE: update_maps g l d c e defs = (g', l', d', c', e')) *)
(*     (LNR: list_norepet (map fst defs)) *)
(*     ef *)
(*     (IN: In (i, Some (Gfun (External ef))) defs) *)
(*     (BEFORE: g i = None) *)
(*     (AFTER: g' i = Some s), *)
(*     e <= Ptrofs.unsigned (snd s) /\ Ptrofs.unsigned (snd s) + alignw <= e'. *)
(* Proof. *)
(*   induction defs; simpl; intros; eauto. easy. *)
(*   destruct IN. *)
(*   - subst. *)
(*     rewrite AGREE_SMINJ_INSTR.update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst. *)
(*     erewrite update_gmap_not_in in AFTER. 2: eauto. 2: inv LNR; auto. *)
(*     erewrite update_gmap in AFTER. 2: eauto. *)
(*     rewrite peq_true in AFTER. inv AFTER. *)
(*     unfold extfun_label; simpl. *)
(*     rewrite Ptrofs.unsigned_repr; auto. *)
(*     eapply update_efsize in Heqp. *)
(*     eapply efsize_mono in UPDATE. subst. simpl in UPDATE. *)
(*     unfold alignw in *. *)
(*     omega. *)
(*   - destruct a. rewrite AGREE_SMINJ_INSTR.update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst. *)
(*     inv LNR. *)
(*     assert (e <= z). { *)
(*       exploit update_efsize; eauto. intro; subst. *)
(*       unfold size_extfun, alignw. repeat destr; omega. *)
(*     } *)
(*     assert (z <= e') by (eapply efsize_mono; eauto). *)
(*     exploit IHdefs. 3: eauto. omega. auto. auto. eauto. eauto.  *)
(*     erewrite update_gmap; eauto. rewrite peq_false; auto. *)
(*     intro; subst. apply H2. *)
(*     apply in_map with (f:= fst) in H. simpl in H; auto. eauto. *)
(*     omega. *)
(* Qed. *)

(* Lemma update_maps_extfun_lt': *)
(*   forall defs g l d c e g' l' d' c' e' i s *)
(*     (RNG: 0 <= e <= Ptrofs.max_unsigned) *)
(*     (RNG: 0 <= e' <= Ptrofs.max_unsigned) *)
(*     (UPDATE: update_maps g l d c e defs = (g', l', d', c', e')) *)
(*     (LNR: list_norepet (map fst defs)) *)
(*     def *)
(*     (IN: In (i,def) defs) *)
(*     (BEFORE: g i = None) *)
(*     (GMAP: g' i = Some (extfuns_segid, s)), *)
(*     e <= Ptrofs.unsigned s /\ Ptrofs.unsigned s + odef_size def <= e'. *)
(* Proof. *)
(*   intros. *)
(*   simpl in *. *)
(*   assert (exists ef, def = Some (Gfun (External ef))). *)
(*   { *)
(*     destruct (in_split _ _ IN) as (bef & aft & EQ). rewrite EQ in *. *)
(*     rewrite update_maps_app in UPDATE. *)
(*     repeat destr_in UPDATE. simpl in *. *)
(*     rewrite AGREE_SMINJ_INSTR.update_maps_cons in H0. repeat destr_in H0. *)
(*     erewrite update_gmap_not_in in GMAP. 2: eauto. *)
(*     erewrite update_gmap in GMAP. 2: eauto. rewrite peq_true in GMAP. *)
(*     repeat destr_in GMAP; unfold code_label, data_label, extfun_label; simpl; eauto. *)
(*     erewrite update_gmap_not_in in H0. 2: eauto. congruence. *)
(*     rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto. *)
(*     simpl in DISJ. intro II; destruct (DISJ i i II (or_introl eq_refl) eq_refl). *)
(*     rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto. *)
(*     simpl in LNR2; inv LNR2; auto. *)
(*   } *)
(*   destruct H; subst. *)
(*   exploit update_maps_extfun_lt. 3: eauto. all: eauto. simpl. auto. *)
(*   unfold alignw. omega. *)
(* Qed. *)

Lemma norepet_unique:
  forall {A B} (f: A -> B) (l: list A)
    (LNR: list_norepet (map f l)) a b
    (INA: In a l) (INB: In b l) (EQ: f a = f b),
    a = b.
Proof.
  induction l; simpl; intros; eauto. easy.
  inv LNR. trim IHl. auto.
  destruct INA, INB; subst; eauto.
  apply in_map with (f:=f) in H0. congruence.
  apply in_map with (f:=f) in H. congruence.
Qed.

Definition sdef_is_var_or_internal_fun {F V: Type} (def: option (AST.globdef (AST.fundef F) V)) :=
  match def with
  | Some (Gvar _) => True
  | Some (Gfun (Internal f)) => True
  | _ => False
  end.

Lemma vit_dec : forall F V (def: option (AST.globdef (AST.fundef F) V)),
    {sdef_is_var_or_internal_fun def} + {~ (sdef_is_var_or_internal_fun def)}.
Proof.
  intros. 
  destruct def; auto. 
  destruct g; auto.
  destruct f; auto.
  left. red. auto.
  left. red. auto.
Qed.

Lemma vit_false_inv: forall F V (def: option (AST.globdef (AST.fundef F) V)),
  ~ sdef_is_var_or_internal_fun def -> 
  def = None \/ exists f, def = Some (Gfun (External f)).
Proof.
  intros. destruct def; auto.
  destruct g; auto.
  destruct f; auto. exfalso. apply H. red. auto. 
  eauto.
  exfalso. apply H. red. auto.
Qed.

Lemma update_map_gmap_some :
  forall (prog : Asm.program) (gmap : GID_MAP_TYPE) (lmap : LABEL_MAP_TYPE) (dsize csize : Z) (id : ident)
    defs gdefs def
    (VIT: sdef_is_var_or_internal_fun def)
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize))
    (BOUND: dsize + csize <= Ptrofs.max_unsigned)
    (LNR: list_norepet (map fst (AST.prog_defs prog)))
    (DEFS: (defs ++ (id, def) :: gdefs) = AST.prog_defs prog),
    exists slbl, gmap id = Some slbl
           /\ (forall id' def' slbl', In (id', def') defs -> (gmap id' = Some slbl') ->
                                 fst slbl' = fst slbl -> Ptrofs.unsigned (snd slbl') + odef_size def' <= Ptrofs.unsigned (snd slbl))
           /\ (forall id' def' slbl', In (id', def') gdefs -> (gmap id' = Some slbl') ->
                           fst slbl' = fst slbl -> Ptrofs.unsigned (snd slbl) + odef_size def <= Ptrofs.unsigned (snd slbl')).
Proof.
  clear. unfold make_maps.
  intros.
  rewrite <- DEFS in *. clear prog DEFS.
  rewrite update_maps_app in UPDATE. do 3 destr_in UPDATE. subst.
  rewrite update_maps_cons in UPDATE.
  do 3 destr_in UPDATE. subst.
  rewrite map_app, list_norepet_app in LNR; destruct LNR as (LNR1 & LNR2 & DISJ); inv LNR2.
  assert (0 <= z0). eapply dsize_mono. eauto.
  assert (0 <= z). eapply csize_mono; eauto. apply Z.divide_0_r.
  assert (alignw | z). eapply updates_csize_div. eauto. apply Z.divide_0_r.
  assert (alignw | z1). eapply update_csize_div with(def:= def). unfold update_maps_def.
  eauto. auto.
  assert (z0 <= z2). eapply update_dsize_mono; eauto.
  assert (z <= z1). eapply update_csize_mono; eauto.
  assert (z2 <= dsize). eapply dsize_mono. eauto.
  assert (z1 <= csize). eapply csize_mono. eauto. auto.
  erewrite update_gmap_not_in; eauto.
  red in VIT. 
  destruct def; try contradiction. 
  destruct g1. 
  - (* internal function *)
    destruct f; try contradiction.
    simpl in Heqp0. repeat destr_in Heqp0.
    unfold update_gid_map. rewrite peq_true. eexists; split; eauto.
    split.
    + intros id' def' slbl' IN GM LBLEQ.
      erewrite update_gmap_not_in in GM; eauto.
      unfold update_gid_map in GM. rewrite peq_false in GM.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_code_lt'. 3: apply Heqp. 5: apply IN. 5: reflexivity. all: eauto.
      vm_compute. intuition congruence. omega. apply Z.divide_0_r.
      rewrite Ptrofs.unsigned_repr. omega. omega.
      intro; subst.
      exploit DISJ. apply in_map. eauto. left. reflexivity. reflexivity. auto.
      intro IN'. exploit DISJ. apply in_map, IN. right; apply IN'. auto. auto.
    + intros id' def' slbl' IN GM LBLEQ.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_code_lt'. 3: apply UPDATE. 5: apply IN. all: eauto. omega. omega.
      unfold update_gid_map.
      rewrite peq_false.
      erewrite update_gmap_not_in. 2: eauto. reflexivity. auto.
      intro IN'. exploit DISJ. apply IN'. right; apply in_map, IN. auto. auto.
      intro; subst. apply H1. replace id' with (fst (id', def')) by reflexivity.
      apply in_map; congruence.
      rewrite Ptrofs.unsigned_repr.
      exploit update_instrs_code_size; eauto. intros; subst.
      eapply Z.le_trans. 2: apply H10.
      eapply Z.le_trans. 2: apply alignw_le. omega. omega.
  - (* variable *)
    simpl in Heqp0. repeat destr_in Heqp0.
    unfold update_gid_map. rewrite peq_true. eexists; split; eauto.
    split.
    + intros id' def' slbl' IN GM LBLEQ.
      erewrite update_gmap_not_in in GM; eauto.
      unfold update_gid_map in GM. rewrite peq_false in GM.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_data_lt'. 3: apply Heqp. all: eauto.
      vm_compute. intuition congruence. omega.
      rewrite Ptrofs.unsigned_repr. omega. omega.
      intro; subst. exploit DISJ. apply in_map; eauto. left. reflexivity. reflexivity. auto.
      intro IN'. exploit DISJ. apply in_map, IN. right; apply IN'. auto. auto.
    + intros id' def' slbl' IN GM LBLEQ.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_data_lt'. 3: apply UPDATE. all: eauto. omega. omega.
      unfold update_gid_map.
      rewrite peq_false.
      erewrite update_gmap_not_in. 2: eauto. reflexivity. auto.
      intro IN'. exploit DISJ. apply IN'. right; apply in_map, IN. auto. auto.
      intro; subst. apply H1. replace id' with (fst (id', def')) by reflexivity.
      apply in_map; congruence.
      rewrite Ptrofs.unsigned_repr by omega.
      intros. eapply Z.le_trans. 2: apply H9.
      generalize (alignw_le (init_data_list_size (gvar_init v))); omega.
Qed.

Lemma make_maps_gmap_inj':
  forall prog0 g' l' d' c' 
    (lnr : list_norepet (map fst (AST.prog_defs prog0)))
    (mm : make_maps prog0 = (g', l', d', c'))
    (bound: d' + c' <= Ptrofs.max_unsigned)
    (* (ne: Forall def_not_empty (map snd (AST.prog_defs prog0))) *)
    l1 l2 l3 i1 i2 d1 d2 s1 s2 o1 o2
    (EQ: AST.prog_defs prog0 = l1 ++ (i1, d1) :: l2 ++ (i2, d2) :: l3)
    (G1 : g' i1 = Some (s1, o1))
    (G2 : g' i2 = Some (s2, o2)),
    s1 <> s2 \/ Ptrofs.unsigned o1 + odef_size d1 <= Ptrofs.unsigned o2 \/ Ptrofs.unsigned o2 + odef_size d2 <= Ptrofs.unsigned o1.
Proof.
  intros.
  destruct (peq s1 s2); auto. subst.
  right.
  destruct (vit_dec _ _ d1).
  - exploit update_map_gmap_some; eauto. 
    rewrite G1.
    intros (s' & G & O1 & O2). inv G. eapply O2 in G2; eauto. rewrite in_app. right; left; reflexivity.
  - unfold make_maps in mm.
    rewrite EQ in mm.
    rewrite update_maps_app in mm. repeat destr_in mm.
    rewrite update_maps_cons in H0. repeat destr_in H0.
    rewrite EQ in lnr.
    rewrite map_app, list_norepet_app in lnr.
    destruct lnr as (lnr1 & lnr2 & disj).
    assert (g' i1 = None).
    erewrite update_gmap_not_in. 2: eauto.
    erewrite update_gmap. 2: eauto. rewrite peq_true.
    erewrite update_gmap_not_in. 2: eauto. 
    exploit vit_false_inv; eauto. intros. destruct H; subst. auto.
    destruct H. subst. auto.
    intro IN. exploit disj. apply IN. left. reflexivity. reflexivity. auto.
    inv lnr2; auto. inv lnr2.  auto. congruence.
Qed.

Lemma app_cons_assoc:
  forall {A} (l1: list A) a l2 b l3,
    (l1 ++ a :: l2) ++ b :: l3 = l1 ++ a :: l2 ++ b :: l3.
Proof.
  induction l1; simpl; intros. reflexivity.
  rewrite IHl1. auto.
Qed.


Lemma update_maps_gmap_inj:
  forall prog g' l' d' c'
    (lnr: list_norepet (map fst (AST.prog_defs prog)))
    (mm: make_maps prog = (g', l', d', c'))
    (bound: d' + c' <= Ptrofs.max_unsigned),
    gmap_inj g' (AST.prog_defs prog).
Proof.
  red; intros.
  destruct (in_split _ _ H) as (l1 & l2 & EQ). rewrite EQ in H0.
  rewrite in_app in H0.
  destruct H0 as [IN2 | IN2].
  destruct (in_split _ _ IN2) as (l3 & l4 & EQ'). subst.
  exploit make_maps_gmap_inj'. 4: rewrite EQ, app_cons_assoc; reflexivity. all: eauto. intuition.
  destruct IN2 as [EQ2 | IN2]. inv EQ2. congruence.
  destruct (in_split _ _ IN2) as (l3 & l4 & EQ'). subst.
  exploit make_maps_gmap_inj'. 4: rewrite EQ; reflexivity. all: eauto.
Qed.


Lemma transl_prog_seg_code:
  forall gmap lmap dsize csize,
    transl_prog_with_map gmap lmap prog dsize csize = OK tprog ->
    segid (code_seg tprog) = code_segid.
Proof.
  unfold transl_prog_with_map.
  intros. monadInvX H. simpl. auto.
Qed.

Lemma transl_prog_seg_data:
  forall gmap lmap dsize csize,
    transl_prog_with_map gmap lmap prog dsize csize = OK tprog ->
    segid (data_seg tprog) = data_segid.
Proof.
  unfold transl_prog_with_map.
  intros. monadInvX H. simpl. auto.
Qed.

(* Lemma transl_prog_seg_ext: *)
(*   forall gmap lmap dsize csize efsize, *)
(*     transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog -> *)
(*     segid (extfuns_seg tprog) = extfuns_segid. *)
(* Proof. *)
(*   unfold transl_prog_with_map. *)
(*   intros. monadInvX H. simpl. auto. *)
(* Qed. *)

Lemma transl_fun_pres_stacksize : forall g i f f',
    transl_fun g i f = OK f' ->
    Asm.fn_stacksize f = fn_stacksize f'.
Proof.
  intros. monadInvX H. destr_in EQ2. inv EQ2. simpl. auto.
Qed.

Lemma transl_prog_gmap : forall g l p p' dz sz,
  transl_prog_with_map g l p dz sz = OK p' -> glob_map p' = g.
Proof.
  intros. monadInv H. simpl. auto.
Qed.

Lemma transl_prog_lmap : forall g l p p' dz sz,
  transl_prog_with_map g l p dz sz = OK p' -> lbl_map p' = l.
Proof.
  intros. monadInv H. simpl. auto.
Qed.


Lemma transl_globdef_pres_index : forall gmap i o o' s i',
  transl_globdef gmap i o = OK (i', o', s) -> i' = i.
Proof.
  intros. destruct o. destruct g. destruct f.
  - monadInv H. auto.
  - monadInv H. auto.
  - monadInvX H. auto.
  - monadInv H. auto.
Qed.

Lemma transl_globdefs_pres_index: forall defs gmap defs'
  (TL: transl_globdefs gmap defs = OK defs')
  (NPT: list_norepet (map fst (defs))),
  map fst defs = map (fun '(i,_,_) => i) defs'.
Proof.
  induction defs; intros; simpl.
  - monadInv TL. auto.
  - destruct a. monadInv TL. destruct x. destruct p.
    exploit transl_globdef_pres_index; eauto. intros. subst. simpl.
    exploit IHdefs; eauto.
    inv NPT. auto.
    intros. congruence.
Qed.

Lemma transl_globdefs_list_norepet: forall defs gmap defs'
  (TL: transl_globdefs gmap defs = OK defs')
  (NPT: list_norepet (map fst (defs))),
  list_norepet (map (fun '(i,_,_) => i) (defs')).
Proof.
  intros. exploit transl_globdefs_pres_index; eauto.
  intros. congruence.
Qed.

Lemma transl_prog_list_norepet : forall gmap lmap dsize csize
  (TL: transl_prog_with_map gmap lmap prog dsize csize = OK tprog)
  (NPT: list_norepet (map fst (AST.prog_defs prog))),
  list_norepet (map (fun '(i,_,_) => i) (prog_defs tprog)).
Proof.
  intros. monadInv TL. simpl.
  eapply transl_globdefs_list_norepet; eauto.
Qed.


Lemma transl_globdefs_pres_def : forall defs g defs' i def
  (TL: transl_globdefs g defs = OK defs')
  (IN: In (i,def) defs),
  exists def' sb, In (i, def', sb) defs' /\ transl_globdef g i def = OK (i, def', sb).
Proof.
  induction defs; intros; simpl; inv IN.
  - monadInv TL. destruct x. destruct p. 
    exploit transl_globdef_pres_index; eauto. intros. subst.
    repeat eexists; eauto. apply in_eq.
  - destruct a. monadInv TL. destruct x. 
    exploit IHdefs; eauto. 
    intros (def' & sb & IN & TL).
    repeat eexists. apply in_cons. eauto. eauto.
Qed.

Lemma transl_prog_pres_def : forall g l p dz cz p' i def
  (TL: transl_prog_with_map g l p dz cz = OK p')
  (IN: In (i,def) (AST.prog_defs p)),
  exists def' sb, In (i, def', sb) (prog_defs p') /\ transl_globdef g i def = OK (i, def', sb).
Proof.
  intros. monadInv TL. simpl.
  eapply transl_globdefs_pres_def; eauto.
Qed.

Lemma transl_globdefs_pres_def' : forall defs sdefs tdefs g i def gdefs
  (DEFSTAIL : defs ++ (i, def) :: gdefs = sdefs)
  (TL: transl_globdefs g sdefs = OK tdefs),
  exists defs' gdefs' def' sb, 
    tdefs = defs' ++ (i, def', sb) :: gdefs' 
    /\ transl_globdefs g defs = OK defs'
    /\ transl_globdef g i def = OK (i, def', sb)
    /\ transl_globdefs g gdefs = OK gdefs'.
Proof.
  induction defs; intros; simpl. 
  - simpl in *. subst. 
    monadInv TL. destruct x. destruct p. 
    exploit transl_globdef_pres_index; eauto. intros. subst.
    exists nil, x0. repeat eexists. auto. auto.
  - destruct a. subst. monadInv TL. destruct x. destruct p.
    exploit IHdefs; eauto. 
    intros (defs' & gdefs' & def' & sb & IN & TL1 & TL2 & TL3). subst.
    rewrite EQ. rewrite TL1, TL2, TL3. simpl. 
    exists ((i1, o0, s) :: defs'). repeat eexists. 
Qed.

Lemma transl_prog_pres_def' : forall defs gdefs g l p dz cz p' i def
  (DEFSTAIL : defs ++ (i, def) :: gdefs = (AST.prog_defs p))
  (TL: transl_prog_with_map g l p dz cz = OK p'),
  exists defs' gdefs' def' sb, 
    (prog_defs p') = defs' ++ (i, def', sb) :: gdefs' 
    /\ transl_globdefs g defs = OK defs'
    /\ transl_globdef g i def = OK (i, def', sb)
    /\ transl_globdefs g gdefs = OK gdefs'.
Proof.
  intros. monadInv TL. simpl.
  eapply transl_globdefs_pres_def'; eauto.
Qed.

Lemma transl_globdefs_pres_non_def : forall defs g defs' i
  (TL: transl_globdefs g defs = OK defs')
  (IN: ~ In i (map fst defs)),
  ~ exists def sb, In (i, def, sb) defs'.
Proof.
  induction defs; simpl; intros.
  - inv TL. intros H. destruct H. destruct H. inv H.
  - destruct a. monadInv TL. simpl in *.
    apply Decidable.not_or in IN. destruct IN.
    destruct x. destruct p.
    exploit transl_globdef_pres_index; eauto.
    intros. subst.
    assert (~ (exists (def : option gdef) (sb : segblock), In (i, def, sb) x0)).
    eapply IHdefs; eauto.
    intros EX. apply H1.
    destruct EX. destruct H2. destruct H2. inv H2. congruence.
    do 2 eexists. eauto.
Qed.

Lemma transl_prog_pres_non_def : forall g l p dz cz p' i
  (TL: transl_prog_with_map g l p dz cz = OK p')
  (IN: ~ In i (prog_defs_names p)),
  ~ exists def sb, In (i, def, sb) (prog_defs p').
Proof.
  intros. monadInv TL. simpl.
  eapply transl_globdefs_pres_non_def; eauto.
Qed.


Lemma update_maps_gmap_in : forall defs x def g l dz cz g' l' dz' cz'
                              (VIT: sdef_is_var_or_internal_fun def)
                              (NPT: list_norepet (map fst defs))
                              (IN: In (x, def) defs)
                              (UPD: update_maps g l dz cz defs = (g', l', dz', cz')),
    exists sid ofs, g' x = Some (sid, ofs).
Proof.
  induction defs; simpl; intros. contradiction. destruct IN.
  - subst. rewrite update_maps_cons in UPD.
    destruct (update_maps_def g l dz cz x def) eqn: UPDD.
    destruct p. destruct p. inv NPT.
    erewrite update_gmap_not_in; eauto.
    erewrite update_gmap; eauto. rewrite peq_true.
    destruct def. destruct g1. destruct f.
    + unfold code_label. eauto.
    + inv VIT.
    + unfold data_label. eauto.
    + inv VIT.
  - destruct a. simpl in *.
    rewrite update_maps_cons in UPD.
    destruct (update_maps_def g l dz cz i o) eqn: UPDD.
    destruct p. destruct p. 
    inv NPT. 
    exploit IHdefs; eauto.
Qed.

Lemma find_symbol_exists : forall (x : ident) def
    (IN: In (x, def) (AST.prog_defs prog)),
    exists b ofs, Genv.find_symbol (globalenv tprog) x = Some (b, ofs).
Proof.
  intros. generalize TRANSF. intros TRANSF'.
  unfold match_prog,transf_program in TRANSF'.
  repeat destr_in TRANSF'. destruct w.
  exploit transl_prog_pres_def; eauto.
  intros (def' & sb & IN' & TLD).
  destruct def. destruct g0. destruct f.
  - monadInv TLD. unfold globalenv.
    erewrite add_globals_pres_find_symbol; eauto. simpl.
    unfold gidmap_to_symbmap. 
    erewrite transl_prog_gmap; eauto.
    exploit update_maps_gmap_in; eauto. red. auto.
    intros (sid & ofs & GM). rewrite GM. 
    do 2 eexists. split; eauto.
    eapply unique_def_is_internal_fun; eauto.
    eapply transl_prog_list_norepet; eauto.
  - monadInv TLD. unfold globalenv.
    apply In_Nth in IN'. destruct IN' as (n & LT & NTH).
    exists (pos_advance_N (Pos.of_succ_nat num_segments) n), Ptrofs.zero.
    erewrite add_globals_find_symbol_ne; eauto.
    red. eauto.
    eapply transl_prog_list_norepet; eauto. 
  - monadInvX TLD. unfold globalenv.
    erewrite add_globals_pres_find_symbol; eauto. simpl.
    unfold gidmap_to_symbmap. 
    erewrite transl_prog_gmap; eauto.
    exploit update_maps_gmap_in; eauto. red. auto.
    intros (sid & ofs & GM). rewrite GM.
    do 2 eexists. split; eauto.
    eapply unique_def_is_var; eauto.
    eapply transl_prog_list_norepet; eauto.
  - monadInv TLD. unfold globalenv.
    apply In_Nth in IN'. destruct IN' as (n & LT & NTH).
    exists (pos_advance_N (Pos.of_succ_nat num_segments) n), Ptrofs.zero.
    erewrite add_globals_find_symbol_ne; eauto.
    red. eauto.
    eapply transl_prog_list_norepet; eauto.
Qed.

Lemma find_symbol_to_gmap : 
  forall (x : ident) def gmap lmap dz cz b ofs
    (IN: In (x, def) (AST.prog_defs prog))
    (FSYM: Genv.find_symbol (globalenv tprog) x = Some (b, ofs))
    (VI: sdef_is_var_or_internal_fun def)
    (MKMAP: make_maps prog = (gmap, lmap, dz, cz)),
  exists slbl, gmap x = Some slbl 
          /\ b = gen_segblocks tprog (fst slbl) 
          /\ ofs = snd slbl.
Proof.
  intros. generalize TRANSF. intros TRANSF'.
  unfold match_prog,transf_program in TRANSF'.
  repeat destr_in TRANSF'. destruct w. inv MKMAP.
  intros. unfold globalenv in FSYM.
  erewrite add_globals_pres_find_symbol in FSYM; eauto.
  - simpl in FSYM.
    unfold gidmap_to_symbmap in FSYM. 
    erewrite transl_prog_gmap in FSYM; eauto.
    destr_in FSYM; inv FSYM. destruct s. inv H1.
    eauto.
  - exploit transl_prog_pres_def; eauto.  
    intros (def' & sb & IN' & TL).
    destruct def. destruct g. destruct f.
    + monadInv TL.
      eapply unique_def_is_internal_fun; eauto.
      eapply transl_prog_list_norepet; eauto.
    + inv VI.
    + monadInvX TL.
      eapply unique_def_is_var; eauto.
      eapply transl_prog_list_norepet; eauto.
    + inv VI.
Qed.

Lemma gmap_to_find_symbol: 
  forall (x : ident) def gmap lmap dz cz slbl
    (IN: In (x, def) (AST.prog_defs prog))
    (VI: sdef_is_var_or_internal_fun def)
    (MKMAP: make_maps prog = (gmap, lmap, dz, cz))
    (GMAP: gmap x = Some slbl),
    Genv.find_symbol (globalenv tprog) x = Some (gen_segblocks tprog (fst slbl), snd slbl).
Proof.
  intros. generalize TRANSF. intros TRANSF'.
  unfold match_prog,transf_program in TRANSF'.
  repeat destr_in TRANSF'. destruct w. inv MKMAP.
  unfold globalenv.
  erewrite add_globals_pres_find_symbol; eauto.
  - simpl.
    unfold gidmap_to_symbmap.
    erewrite transl_prog_gmap; eauto.
    rewrite GMAP. destruct slbl. simpl. auto.
  - exploit transl_prog_pres_def; eauto.  
    intros (def' & sb & IN' & TL).
    destruct def. destruct g. destruct f.
    + monadInv TL.
      eapply unique_def_is_internal_fun; eauto.
      eapply transl_prog_list_norepet; eauto.
    + inv VI.
    + monadInvX TL.
      eapply unique_def_is_var; eauto.
      eapply transl_prog_list_norepet; eauto.
    + inv VI. 
Qed.  
  

Lemma update_instrs_in_lbl : forall code p l cz id l' cz'
                               (IN: In p (labels code))
                               (UPI: update_instrs l cz id code = (l', cz')),
    exists sid ofs, l' id p = Some (sid, ofs).
Proof.
  induction code; simpl; intros. contradiction. destruct (is_label a) eqn:ILBL.
  - destruct a; inv ILBL. unfold update_instrs in UPI. simpl in UPI.
    inv IN. 
    assert ({In p (labels code)} + {~In p (labels code)}).
    apply in_dec. apply peq. destruct H.
    + eapply IHcode; eauto.
    + exploit update_instrs_other_label; eauto. simpl. intros. rewrite H. 
      unfold update_label_map. rewrite peq_true. rewrite peq_true.
      unfold code_label. eauto.
    + eapply IHcode; eauto.
  - unfold update_instrs in UPI. simpl in UPI.
    eapply IHcode; eauto.
Qed.

Lemma update_maps_lmap_in : forall defs id f p g l dz cz g' l' dz' cz'
                              (NPT: list_norepet (map fst defs))
                              (IN: In (id, Some (Gfun (Internal f))) defs)
                              (INL: In p (labels (Asm.fn_code f)))
                              (UPD: update_maps g l dz cz defs = (g', l', dz', cz')),
    exists sid ofs, l' id p = Some (sid, ofs).
Proof.
  induction defs; simpl; intros. contradiction. destruct IN.
  - subst. rewrite update_maps_cons in UPD.
    destruct (update_maps_def g l dz cz id (Some (Gfun (Internal f)))) eqn: UPDD.
    destruct p0. destruct p0. inv NPT.
    erewrite update_lmap_not_in; eauto.
    erewrite update_lmap; eauto. rewrite peq_true.
    destruct (update_instrs l cz id (Asm.fn_code f)) as [l1 cz1] eqn:EQ. simpl.
    eapply update_instrs_in_lbl; eauto.
  - destruct a. simpl in *.
    rewrite update_maps_cons in UPD.
    destruct (update_maps_def g l dz cz i o) eqn: UPDD.
    destruct p0. destruct p0.
    inv NPT.
    exploit IHdefs; eauto.
Qed.

Lemma label_pos_in_fun : forall c l s z
  (LPOS: label_pos l s c = Some z),
  In l (labels c).
Proof.
  induction c; simpl; intros.
  - congruence.
  - destruct (Asm.is_label l a) eqn:EQ.
    + destruct a; inv EQ. destruct peq; inv H0. simpl. eauto.
    + exploit IHc; eauto. intros. destr_match; auto.
      apply in_cons. auto.
Qed.

Theorem init_meminj_match_sminj : 
    match_inj init_meminj.
Proof.
  generalize TRANSF. intros TRANSF'.
  unfold match_prog in TRANSF'.
  unfold transf_program in TRANSF'.
  repeat destr_in TRANSF'.
  generalize H0. intros TL.
  unfold make_maps in Heqp. 
  monadInv H0.
  revert H0.
  constructor.

  - (* agree_inj_instr *)
    intros b b' f ofs ofs' i FPTR FINST INITINJ.
    unfold init_meminj in INITINJ. 
    revert H0.
    destruct eq_block. inv INITINJ.
    unfold ge in FPTR. exploit Genv.genv_next_find_funct_ptr_absurd; eauto. contradiction.
    destr_match_in INITINJ; inv INITINJ.
    destr_match_in H0; inv H0.
    destruct p. inv H1. rewrite Ptrofs.repr_unsigned.
    unfold globalenv in EQ1; simpl in EQ1.
    rewrite add_globals_pres_find_symbol in EQ1. simpl in EQ1.
    apply Genv.invert_find_symbol in EQ0.
    exploit (Genv.find_symbol_funct_ptr_inversion prog); eauto.
    intros FINPROG.
    exploit transl_fun_exists; eauto. intros (f' & TRANSLFUN' & INR).
    unfold gidmap_to_symbmap in EQ1. destr_match_in EQ1; inv EQ1.
    destruct s. inv H0. 
    intros TPROG. rewrite <- TPROG in EQ2. simpl in EQ2.
    exploit find_instr_transl_fun; eauto.
    intros (i' & ofs1 & TRANSINSTR & SEGLBL & IN).
    exists i0, i', s, ofs1. split.
    unfold segblock_to_label in SEGLBL. simpl in SEGLBL. inversion SEGLBL.
    apply INR in IN.
    eapply find_instr_self; eauto.
    simpl. rewrite <- TPROG. simpl.
    eapply transl_globdefs_distinct_code_labels; eauto.
    eapply update_maps_gmap_inj; eauto.
    inv w; auto.
    rewrite <- TPROG; simpl. auto.
    split; auto.
    exploit Genv.find_symbol_funct_ptr_inversion; eauto.
    apply Genv.invert_find_symbol. eauto. eauto. intros IN.
    exploit transl_prog_pres_def; eauto. 
    intros (def' & sb & IN' & TLD). eauto.
    monadInv TLD. eauto.
    eapply unique_def_is_internal_fun; eauto.
    eapply transl_prog_list_norepet; eauto. inv w; auto.

  - (* agree_inj_glob *)
    intros id b FSYM.
    unfold ge in FSYM.
    exploit Genv.find_symbol_inversion; eauto. intros INSYM.
    unfold prog_defs_names in INSYM.
    rewrite in_map_iff in INSYM. destruct INSYM as (def & EQ1 & IN).
    destruct def. simpl in EQ1. subst i.
    exploit transl_prog_pres_def; eauto.
    intros (def' & sb & IN' & TLDEF).
    exploit find_symbol_exists; eauto.
    intros (b' & ofs' & FSYM').
    exists b', ofs'. split; auto.
    unfold init_meminj. destruct eq_block.
    subst b.  apply Genv.find_symbol_genv_next_absurd in FSYM. contradiction.
    apply Genv.find_invert_symbol in FSYM. rewrite FSYM. rewrite FSYM'. auto.

  - (* agree_inj_lbl *)
    intros id b f l1 z1 FINDSYM FINDPTR LPOS.
    unfold ge in FINDSYM.
    exploit Genv.find_symbol_funct_ptr_inversion; eauto. intros INDEFS.
    exploit transl_fun_exists; eauto.
    intros (f' & TRANSLF & INCODE).
    assert (exists l', l id l1 = Some l') as LMAP. 
    { 
      exploit label_pos_in_fun; eauto. intros.
      exploit update_maps_lmap_in; eauto. destruct w; auto.
      intros (sid & ofs & LEQ). eauto.
    }
    destruct LMAP as (l' & LMAP).
    exploit update_map_lmap_inversion; eauto.
    inv w; auto. inv w; auto.
    eapply defs_nodup_labels; eauto.
    intros (slbl & GMAP & LEQ & OFSEQ).
    unfold Genv.label_address. unfold tge.
    unfold globalenv. 
    erewrite add_globals_pres_lbl. simpl.
    erewrite transl_prog_lmap; eauto.
    unfold lblmap_to_symbmap. rewrite LMAP. destruct l'.
    apply Val.inject_ptr with (Ptrofs.unsigned (snd slbl)).
    unfold init_meminj. destruct eq_block.
    subst b. exfalso.
    eapply Genv.find_symbol_genv_next_absurd; eauto.
    erewrite Genv.find_invert_symbol; eauto.
    destruct slbl. simpl in LEQ. subst s0. simpl.
    unfold globalenv. 
    erewrite add_globals_pres_find_symbol; eauto. simpl.
    erewrite transl_prog_gmap; eauto. unfold gidmap_to_symbmap.
    rewrite GMAP. eauto.
    exploit transl_prog_pres_def; eauto. 
    intros (def' & sb & IN & TF). 
    destruct w. exploit transl_prog_list_norepet; eauto. intros.
    monadInv TF.
    eapply unique_def_is_internal_fun; eauto. 
    simpl in OFSEQ. subst i.
    rewrite Ptrofs.repr_unsigned. symmetry.
    rewrite Ptrofs.add_commut. auto.
Qed.

Lemma find_symbol_some_pres: forall id b,
  Globalenvs.Genv.find_symbol ge id = Some b ->
  exists b' ofs', Genv.find_symbol tge id = Some (b', ofs') 
             /\ init_meminj b = Some (b', Ptrofs.unsigned ofs').
Proof.
  intros. generalize init_meminj_match_sminj. intros MINJ.
  inv MINJ. eapply agree_inj_glob0; eauto.
Qed.

  
Lemma alloc_pres_def_frame_inj : forall m1 lo hi m1' b,
    Mem.alloc m1 lo hi = (m1', b) ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  apply Mem.alloc_stack_blocks in H. rewrite H. auto.
Qed.

(** Proving initial memory injection **)

Definition partial_genv defs : Globalenvs.Genv.t Asm.fundef unit :=
  let emptyge := (Globalenvs.Genv.empty_genv Asm.fundef unit prog.(AST.prog_public)) in
  Globalenvs.Genv.add_globals emptyge defs.

Definition globs_meminj : meminj :=
  let ge := Genv.globalenv prog in
  let tge := globalenv tprog in
  fun b =>
      match (Genv.invert_symbol ge b) with
      | None => None
      | Some id =>
        match Genv.find_symbol tge id with
        | None => None
        | Some (b, ofs) => Some (b, Ptrofs.unsigned ofs)
        end
      end.



Lemma invert_add_global_genv_next : forall (F V: Type) (ge:Globalenvs.Genv.t F V) id def,
    Genv.invert_symbol (Genv.add_global ge (id, def)) (Globalenvs.Genv.genv_next ge) = Some id.
Proof.
  intros. apply Genv.find_invert_symbol.
  apply Globalenvs.Genv.add_global_find_symbol_eq.
Qed.

Lemma partial_genv_invert_symbol : forall defs id def,
    Genv.invert_symbol (partial_genv (defs ++ (id, def) :: nil)) (Globalenvs.Genv.genv_next (partial_genv defs)) = Some id.
Proof.
  intros defs id def. unfold partial_genv.
  rewrite Genv.add_globals_app. simpl.
  apply invert_add_global_genv_next.
Qed.

Lemma partial_genv_find_symbol_eq : forall defs id def,
    Globalenvs.Genv.find_symbol (partial_genv (defs ++ (id, def) :: nil)) id = Some (Globalenvs.Genv.genv_next (partial_genv defs)).
Proof.
  intros defs id def. apply Genv.invert_find_symbol.
  apply partial_genv_invert_symbol.
Qed.

Lemma partial_genv_find_symbol_neq : forall defs id id' def,
    id <> id' ->
    Globalenvs.Genv.find_symbol (partial_genv (defs ++ (id, def) :: nil)) id' = Globalenvs.Genv.find_symbol (partial_genv defs) id'.
Proof.
  intros defs id id' def H. unfold partial_genv. rewrite Genv.add_globals_app.
  simpl. rewrite Genv.add_global_find_symbol_neq; auto.
Qed.


Lemma partial_genv_find_symbol_inversion : forall defs x b,
  Globalenvs.Genv.find_symbol (partial_genv defs) x = Some b ->
  In x (map fst defs).
Proof.
  unfold partial_genv. intros defs x b.
  eapply Genv.add_globals_preserves.
  - intros.
    destruct (peq x id). subst.
    rewrite Genv.add_global_find_symbol_eq in H1. inv H1. apply in_map with (f:= fst) in H0; auto.
    rewrite Genv.add_global_find_symbol_neq in H1 by auto. eauto.
  - setoid_rewrite PTree.gempty. congruence.
Qed.

Lemma invert_symbol_add_global_none : forall defs id def b,
    ~In id (map fst defs) ->
    Genv.invert_symbol (Genv.add_global (partial_genv defs) (id, def)) b = None ->
    Genv.invert_symbol (partial_genv defs) b = None.
Proof.
  intros defs id def b NOTIN INVSYM.
  destruct (Genv.invert_symbol (partial_genv defs) b) eqn:INVSYM'; auto.
  apply Genv.invert_find_symbol in INVSYM'.
  assert (id <> i) as FINDSYM.
  {
    exploit partial_genv_find_symbol_inversion; eauto.
    intros IN EQ. subst. congruence.
  }
  assert (Genv.invert_symbol (Genv.add_global (partial_genv defs) (id, def)) b = Some i).
  apply Genv.find_invert_symbol. 
  erewrite Genv.add_global_find_symbol_neq; eauto.
  congruence.
Qed.

Lemma update_map_gmap_none :
  forall (prog : Asm.program) (gmap : GID_MAP_TYPE) (lmap : LABEL_MAP_TYPE) (dsize csize : Z) (id : ident) def
    (DEFSNAMES: list_norepet (map fst (AST.prog_defs prog)))
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize))
    (NVI: ~sdef_is_var_or_internal_fun def)
    (IN: In (id, def) (AST.prog_defs prog)),
    gmap id = None.
Proof.
  intros. unfold make_maps in UPDATE.
  eapply umind with (P := fun g l s c => g id = None). eauto. reflexivity.
  intros.
  erewrite update_gmap. 2: eauto. destr. subst.
  exploit @norepet_unique. apply DEFSNAMES. apply IN. apply H1. reflexivity. intro A; inv A. 
  destruct d. destruct g0. destruct f.
  - exfalso. apply NVI. red. auto.
  - auto.
  - exfalso. apply NVI. red. auto.
  - auto.
Qed.




Definition fun_non_empty (def: AST.globdef Asm.fundef unit) : Prop :=
  match def with
  | Gfun (Internal f) =>
    (0 < length (Asm.fn_code f))%nat
  | _ => True
  end.

Definition defs_funs_non_empty (defs: list (ident * option (AST.globdef Asm.fundef unit))) : Prop :=
  Forall (fun '(id, def) =>
            match def with
            | None => True
            | Some def' => fun_non_empty def'
            end
         ) defs.

Lemma defs_funs_non_empty_cons_inv : forall a l,
  defs_funs_non_empty (a::l) -> defs_funs_non_empty l.
Proof.
  unfold defs_funs_non_empty. intros a l H.
  inv H. auto.
Qed.

Lemma drop_perm_pres_def_frame_inj : forall m1 lo hi m1' b p,
    Mem.drop_perm m1 b lo hi p = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  apply Mem.drop_perm_stack in H. rewrite H. auto.
Qed.

Lemma transl_fun_inversion : forall gmap id f f',
    transl_fun gmap id f = OK f' ->
    exists slbl, gmap id = Some slbl /\ fn_range f' = mkSegBlock (fst slbl) (snd slbl) (Ptrofs.repr (Asm.code_size (Asm.fn_code f))).
Proof.
  intros gmap id f f' H. monadInvX H.
  destruct zle; monadInv EQ2. simpl. eexists. split; eauto.
Qed.

Lemma partial_genv_invert_symbol_pres : forall defs id def b,
    ~ In id (map fst defs) ->
    b <> Globalenvs.Genv.genv_next (partial_genv defs) ->
    Genv.invert_symbol (partial_genv (defs ++ (id, def) :: nil)) b = Genv.invert_symbol (partial_genv defs) b.
Proof.
  intros defs id def b NOTIN H.
  unfold partial_genv. rewrite Genv.add_globals_app. simpl.
  match goal with
  | [ |- ?a = _ ] =>
    let eq := fresh "EQ" in
    destruct a eqn:eq
  end.
  - apply Genv.invert_find_symbol in EQ. symmetry. apply Genv.find_invert_symbol.
    destruct (ident_eq id i). subst i.
    rewrite Genv.add_global_find_symbol_eq in EQ. inv EQ.
    contradiction.
    erewrite Genv.add_global_find_symbol_neq in EQ; eauto.
  - symmetry. eapply invert_symbol_add_global_none in EQ; eauto.
Qed.


Lemma advance_next_succ : forall {F V: Type} (defs: list (ident * option (globdef F V))) p,
  Genv.advance_next defs (Pos.succ p) = Pos.succ (Genv.advance_next defs p).
Proof.
  induction defs; intros; simpl in *.
  - auto.
  - rewrite IHdefs. auto.
Qed.

Lemma partial_genv_next : forall defs,
    Globalenvs.Genv.genv_next (partial_genv defs) = Pos.of_succ_nat (length defs).
Proof.
  induction defs; intros; simpl. auto.
  unfold partial_genv in *. simpl.
  rewrite Genv.genv_next_add_globals in *. simpl in *.
  rewrite <- IHdefs.
  rewrite <- advance_next_succ. simpl. auto.
Qed.


Lemma partial_genv_next_succ : forall defs def,
    Globalenvs.Genv.genv_next (partial_genv (defs ++ def :: nil)) =
    Pos.succ (Globalenvs.Genv.genv_next (partial_genv defs)).
Proof.
  intros. unfold partial_genv.
  rewrite Genv.add_globals_app. simpl. auto.
Qed.

Lemma defs_names_distinct_not_in : forall(F V:Type) (defs:list (ident * option (AST.globdef F V))) id def gdefs,
    list_norepet (map fst (defs ++ (id, def) :: gdefs)) -> ~In id (map fst defs).
Proof.
  intros F V defs id def gdefs LNR.
  rewrite map_app, list_norepet_app in LNR.
  destruct LNR as (A & B & C).
  intro IN.
  exploit C. eauto. left; reflexivity. reflexivity. auto.
Qed.

Lemma defs_names_distinct_prefix_neq : forall (F V:Type) (defs1: list (ident * option (AST.globdef F V)))
                                         id def defs2 id' def',
    list_norepet (map fst (defs1 ++ (id, def) :: defs2)) ->
    In (id', def') defs1 -> id <> id'.
Proof.
  intros F V defs1 id def defs2 id' def' DISTINCT IN.
  assert (~ In id (map fst defs1)). eapply defs_names_distinct_not_in; eauto.
  unfold not. intros. subst.
  exploit (in_map fst defs1); eauto.
Qed.


Lemma find_symbol_add_globals_inversion :
  forall (F V:Type) (defs: list (ident * option (AST.globdef F V))) id r ge,
    Globalenvs.Genv.find_symbol (Globalenvs.Genv.add_globals ge defs) id = r ->
    (exists def, In (id, def) defs) \/ Globalenvs.Genv.find_symbol ge id = r.
Proof.
  induction defs; intros.
  - simpl in H. auto.
  - simpl in H. exploit IHdefs; eauto.
    intros [L | R].
    + destruct L as [def' IN].
      left. exists def'. apply in_cons. auto.
    + destruct a. destruct (ident_eq id i).
      subst. rewrite Genv.add_global_find_symbol_eq in R. left. eexists. simpl. left. eauto.
      erewrite Genv.add_global_find_symbol_neq in R; eauto.
Qed.

Lemma find_symbol_inversion_1 : forall defs (x : ident) (b : block),
    Globalenvs.Genv.find_symbol (partial_genv defs) x = Some b -> exists def, In (x, def) defs.
Proof.
  unfold partial_genv. intros.
  exploit find_symbol_add_globals_inversion; eauto.
  intros [L | R]. auto.
  exploit Genv.find_symbol_empty_genv_absurd; eauto. contradiction.
Qed.

Lemma find_symbol_inversion_2 : forall {F V} (prog:AST.program F V) (x : ident) (b : block),
    Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv prog) x = Some b -> 
    exists def, In (x, def) (AST.prog_defs prog).
Proof.
  intros. exploit Globalenvs.Genv.find_symbol_inversion; eauto.
  intros. unfold prog_defs_names in H0.
  rewrite in_map_iff in H0. destruct H0. destruct H0. 
  destruct x0. eauto. simpl in *. subst. eauto.
Qed.


Lemma store_zeros_mapped_inject:
  forall (f : meminj) (g : frameinj) (m1 : mem) (b1 : block) (ofs n : Z)
    (n1 m2 : mem) (b2 : block) (delta : Z),
    Mem.weak_inject f g m1 m2 ->
    store_zeros m1 b1 ofs n = Some n1 ->
    f b1 = Some (b2, delta) ->
    exists n2 : mem, store_zeros m2  b2 (ofs+delta) n = Some n2 /\ Mem.weak_inject f g n1 n2.
Proof.
  intros until n1. functional induction (store_zeros m1 b1 ofs n); intros.
  - inv H0. exists m2. split; auto. rewrite store_zeros_equation.
    rewrite e. auto.
  - exploit Mem.store_mapped_weak_inject; eauto. unfold Vzero. eauto.
    intros (n2 & STORE & WINJ).
    exploit IHo; eauto. intros (n3 & STOREZEROS & WINJ'). exists n3. split; eauto.
    rewrite store_zeros_equation. rewrite e.
    unfold Vzero. rewrite STORE. replace (p + delta + 1) with (p + 1 + delta) by omega. auto.
  - inv H0.
Qed.

Lemma store_zeros_pres_def_frame_inj : forall m1 b lo hi m1',
    store_zeros m1 b lo hi = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  intros m1 b lo hi m1' H.
  functional induction (store_zeros m1 b lo hi); intros.
  - inv H. auto.
  - exploit IHo; eauto. intros.
    exploit Mem.store_stack_blocks; eauto.
    intros. unfold def_frame_inj in *. rewrite H1 in *. auto.
  - inv H.
Qed.

Lemma globs_meminj_pres_find_symbol: 
  forall id b,
    Globalenvs.Genv.find_symbol ge id = Some b ->
    exists b' ofs', Genv.find_symbol tge id = Some (b', ofs') /\
               globs_meminj b = Some (b', Ptrofs.unsigned ofs').
Proof.
  intros id b FSYM.
  unfold ge in FSYM.
  exploit Genv.find_symbol_inversion; eauto. intros INSYM.
  unfold prog_defs_names in INSYM.
  rewrite in_map_iff in INSYM. destruct INSYM as (def & EQ1 & IN).
  destruct def. simpl in EQ1. subst i.
  generalize TRANSF. intros TRANSF'.
  red in TRANSF'. unfold transf_program in TRANSF'. repeat destr_in TRANSF'. 
  destruct w.
  exploit transl_prog_pres_def; eauto.
  intros (def' & sb & IN' & TLDEF).
  exploit find_symbol_exists; eauto.
  intros (b' & ofs' & FSYM').
  exists b', ofs'. split; auto.
  unfold globs_meminj. 
  apply Genv.find_invert_symbol in FSYM. rewrite FSYM. rewrite FSYM'. auto.
Qed.  

Lemma store_init_data_list_mapped_inject_aux : forall v g m1 m1' m2 b1 b2 delta ofs,
    Mem.weak_inject globs_meminj g m1 m1' ->
    globs_meminj b1 = Some (b2, delta) ->
    Genv.store_init_data_list ge m1 b1 ofs v = Some m2 ->
    exists m2', store_init_data_list tge m1' b2 (ofs+delta) v = Some m2'
           /\ Mem.weak_inject globs_meminj g m2 m2'.
Proof.
  induction v; intros.
  - simpl in H1. inv H1. exists m1'. split; auto.
  - simpl in H1. destr_match_in H1; inv H1.
    unfold Genv.store_init_data in EQ. destruct a.
    + exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl.
      rewrite STORE. replace (ofs + delta + 1) with (ofs + 1 + delta) by omega.
      auto.
    + exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl.
      rewrite STORE. replace (ofs + delta + 2) with (ofs + 2 + delta) by omega.
      auto.
    + exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl.
      rewrite STORE. replace (ofs + delta + 4) with (ofs + 4 + delta) by omega.
      auto.
    + exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl.
      rewrite STORE. replace (ofs + delta + 8) with (ofs + 8 + delta) by omega.
      auto.
    + exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl.
      rewrite STORE. replace (ofs + delta + 4) with (ofs + 4 + delta) by omega.
      auto.
    + exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl.
      rewrite STORE. replace (ofs + delta + 8) with (ofs + 8 + delta) by omega.
      auto.
    + simpl in H3. inv EQ.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl.
      replace (ofs + delta + (Z.max z 0)) with (ofs + (Z.max z 0) + delta) by omega.
      auto.
    + simpl in H3. destr_match_in EQ; inv EQ.
      exploit globs_meminj_pres_find_symbol; eauto.
      intros (b' & fos' & FSYM & INJ).
      exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). rewrite Ptrofs.repr_unsigned in STORE.
      exploit (fun f m1 m1' m2 => IHv f m1 m1' m2 b1); eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl.
      unfold Genv.symbol_address. rewrite FSYM. 
      rewrite STORE.
      replace (ofs + delta + (if Archi.ptr64 then 8 else 4)) with (ofs + (if Archi.ptr64 then 8 else 4) + delta) by omega.
      auto.
Qed.

Lemma store_init_data_list_mapped_inject : forall g m1 m1' m2 (v:globvar unit) b1 b2 delta ofs,
    Mem.weak_inject globs_meminj g m1 m1' ->
    globs_meminj b1 = Some (b2, delta) ->
    Genv.store_init_data_list ge m1 b1 ofs (gvar_init v) = Some m2 ->
    exists m2', store_init_data_list tge m1' b2 (ofs+delta) (gvar_init v) = Some m2'
           /\ Mem.weak_inject globs_meminj g m2 m2'.
Proof.
  intros g m1 m1' m2 v b1 b2 delta ofs WINJ F STOREL.
  simpl.
  eapply store_init_data_list_mapped_inject_aux; eauto.
Qed.

Lemma store_init_data_pres_def_frame_inj : forall m1 b1 ofs v m1',
    Genv.store_init_data ge m1 b1 ofs v = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  intros. unfold Genv.store_init_data in H.
  destruct v; try now (exploit Mem.store_stack_blocks; eauto; unfold def_frame_inj; congruence).
  inv H. auto.
  destr_match_in H; inv H.
  exploit Mem.store_stack_blocks; eauto; unfold def_frame_inj; congruence.
Qed.

Lemma store_init_data_list_pres_def_frame_inj : forall gv m1 b1 ofs  m1',
    Genv.store_init_data_list ge m1 b1 ofs gv = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  induction gv; intros.
  - inv H. auto.
  - inv H. destr_match_in H1; inv H1.
    exploit store_init_data_pres_def_frame_inj; eauto. intros.
    rewrite H. exploit IHgv; eauto.
Qed.


Lemma defs_names_distinct_not_in_tail : forall(F V:Type) (defs:list (ident * option (AST.globdef F V))) id def gdefs,
    list_norepet (map fst (defs ++ (id, def) :: gdefs)) -> ~In id (map fst gdefs).
Proof.
  intros F V defs id def gdefs LNR.
  rewrite map_app, list_norepet_app in LNR.
  destruct LNR as (A & B & C).
  intro IN. simpl in B. inv B. congruence.
Qed.

Lemma genv_find_symbol_next : forall defs id def gdefs,
    list_norepet (map fst (AST.prog_defs prog)) ->
    AST.prog_defs prog = (defs ++ (id, def) :: gdefs) ->
    Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv prog) id = Some (Globalenvs.Genv.genv_next (partial_genv defs)).
Proof.
  intros defs id def gdefs NORPT H. unfold Globalenvs.Genv.globalenv. rewrite H.
  rewrite Globalenvs.Genv.add_globals_app. simpl.
  match goal with
  | [ |- Globalenvs.Genv.find_symbol (Globalenvs.Genv.add_globals ?ge' ?defs') ?id' = _ ] =>
    exploit (find_symbol_add_globals_inversion Asm.fundef unit defs' id'
                                               (Globalenvs.Genv.find_symbol (Globalenvs.Genv.add_globals ge' defs') id')); eauto
  end.
  intros [L | R].
  - destruct L as [def' IN].
    rewrite H in NORPT.
    assert (~In id (map fst gdefs)). eapply defs_names_distinct_not_in_tail; eauto.
    assert (In (fst (id, def')) (map fst gdefs)). apply in_map. auto.
    simpl in H1. congruence.
  - rewrite <- R.
    erewrite Genv.add_global_find_symbol_eq; eauto.
Qed.


Lemma genv_invert_symbol_next : forall defs id def gdefs,
    list_norepet (map fst (AST.prog_defs prog)) ->
    AST.prog_defs prog = (defs ++ (id, def) :: gdefs) ->
    Genv.invert_symbol (Genv.globalenv prog) (Globalenvs.Genv.genv_next (partial_genv defs)) = Some id.
Proof.
  intros defs id def gdefs NORPT H.
  apply Genv.find_invert_symbol. eapply genv_find_symbol_next; eauto.
Qed.

Definition aligned (ofs:Z) := forall chunk, (align_chunk chunk | ofs).

Lemma chunk_divides_alignw: forall chunk,
  (align_chunk chunk | alignw).
Proof.
  intros. unfold alignw. destruct chunk; simpl; red.
  - exists 8; omega.
  - exists 8; omega.
  - exists 4; omega.
  - exists 4; omega.
  - exists 2; omega.
  - exists 1; omega.
  - exists 2; omega.
  - exists 2; omega.
  - exists 2; omega.
  - exists 2; omega.
Qed.

Lemma alignw_aligned : forall i,
  (alignw | i) -> aligned i.
Proof.
  unfold aligned. intros.
  apply Zdivides_trans with alignw; auto.
  apply chunk_divides_alignw.
Qed.


Lemma update_map_gmap_aligned :
  forall defs gmap lmap dsize csize
    gmap1 lmap1 dsize1 csize1 slbl i
    (UPDATE: (gmap,lmap,dsize, csize) = update_maps gmap1 lmap1 dsize1 csize1 defs)
    (CSZALN: (alignw | csize1))
    (CSZBOUND: csize <= Ptrofs.max_unsigned)
    (CSZPOS: 0 <= csize1)
    (DSZALN: (alignw | dsize1))
    (DSZBOUND: dsize <= Ptrofs.max_unsigned)
    (DSZPOS: 0 <= dsize1)
    (GMAPALN: forall i' slbl', gmap1 i' = Some slbl' -> aligned (Ptrofs.unsigned (snd slbl')))
    (GMAP: gmap i = Some slbl),
    aligned (Ptrofs.unsigned (snd slbl)).
Proof.
  induction defs; intros.
  assert (csize1 <= csize). eapply csize_mono; eauto.
  - inv UPDATE. eauto.
  - destruct a. destruct o. destruct g. destruct f.
    + cbn in UPDATE.
      destruct (update_instrs lmap1 csize1 i0 (Asm.fn_code f)) as [lmap' csize'] eqn:UPDATEINSTRS.
      eapply IHdefs; eauto.
      apply align_divides. unfold alignw. omega.
      apply Zle_trans with csize'; try apply alignw_le.
      exploit update_instrs_code_size; eauto. intros.
      generalize (code_size_non_neg (Asm.fn_code f)). intros.
      omega.
      intros i' slbl' GMAP'.
      unfold update_gid_map in GMAP'. destruct peq.
      subst. inv GMAP'. unfold code_label. simpl.
      rewrite Ptrofs.unsigned_repr. apply alignw_aligned. auto.
      assert (align csize' alignw <= csize).
      { eapply csize_mono; eauto. apply align_divides. unfold alignw. omega. }
      generalize (alignw_le csize'). intros.
      exploit update_instrs_code_size; eauto. intros.
      generalize (code_size_non_neg (Asm.fn_code f)). intros.
      omega.
      eauto.
    + cbn in UPDATE.
      eapply IHdefs; eauto.
    + cbn in UPDATE.
      eapply IHdefs; eauto.
      apply Z.divide_add_r; auto.
      apply align_divides.
      unfold alignw. omega.
      generalize (alignw_le (init_data_list_size (gvar_init v))). intros.
      generalize (init_data_list_size_pos (gvar_init v)). intros. omega.
      intros i' slbl' GMAP'.
      unfold update_gid_map in GMAP'. destruct peq.
      subst. inv GMAP'. unfold data_label. simpl.
      rewrite Ptrofs.unsigned_repr. apply alignw_aligned. auto.
      assert (dsize1 + align (init_data_list_size (gvar_init v)) alignw <= dsize).
      { eapply dsize_mono; eauto. }
      assert (0 <= align (init_data_list_size (gvar_init v)) alignw).
      {
        apply Zle_trans with (init_data_list_size (gvar_init v)).
        generalize (init_data_list_size_pos (gvar_init v)). omega.
        apply alignw_le.
      }
      omega.
      eauto.
    + cbn in UPDATE.
      eapply IHdefs; eauto.
Qed.

Lemma make_maps_sizes_pos :
  forall prog gmap lmap dsize csize,
    make_maps prog = (gmap, lmap, dsize, csize) ->
    dsize >= 0 /\ csize >= 0.
Proof.
  intros prog0 gmap lmap dsize csize H.
  unfold make_maps in H.
  assert (0 <= csize).
  { eapply csize_mono; eauto. unfold alignw. red. exists 0. omega. }
  assert (0 <= dsize).
  { eapply dsize_mono; eauto. }
  omega.
Qed.

Lemma prog_odef_size_pos : forall defs id odef gdefs,
    defs ++ (id, odef) :: gdefs = AST.prog_defs prog ->
    def_not_empty odef.
Proof.
  intros defs id odef gdefs DEFSTAIL.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF. repeat destr_in TRANSF.
  inv w. rewrite <- DEFSTAIL in wf_prog_not_empty. red in wf_prog_not_empty.
  rewrite Forall_forall in wf_prog_not_empty.
  specialize (wf_prog_not_empty odef).
  cut (def_not_empty odef); auto.
  apply wf_prog_not_empty. rewrite map_app. simpl. rewrite in_app. right. apply in_eq.
Qed.

Lemma make_maps_ofs_ordering :
  forall prog defs1 defs2 i1 i2 def1 def2 slbl1 slbl2
    gmap lmap dsize csize
    (SZMAX: dsize + csize  <= Ptrofs.max_unsigned)
    (NORPT: list_norepet (map fst (AST.prog_defs prog)))
    (DEFS: AST.prog_defs prog = defs1 ++ defs2)
    (UPDATE: (gmap, lmap, dsize, csize) = make_maps prog)
    (IN1: In (i1, def1) defs1)
    (IN2: In (i2, def2) defs2)
    (GMAP1: gmap i1 = Some slbl1)
    (GMAP2: gmap i2 = Some slbl2)
    (SAMESEG: fst slbl1 = fst slbl2),
    odef_size def1 + Ptrofs.unsigned (snd slbl1) <= Ptrofs.unsigned (snd slbl2).
Proof.
  intros. destruct (vit_dec _ _ def2).
  - apply in_split in IN2. destruct IN2 as (defs3 & defs4 & DEFS2).
    subst.
    exploit (update_map_gmap_some prog0 gmap lmap dsize csize i2
                                  (defs1 ++ defs3) defs4 def2); eauto.
    rewrite <- app_assoc. auto.
    intros (slbl & GMAP2' & BND1 & BND2).
    rewrite GMAP2' in GMAP2. inv GMAP2.
    rewrite Zplus_comm. eapply BND1; eauto.
    rewrite in_app. auto.
  - exploit update_map_gmap_none; eauto. rewrite DEFS.
    erewrite in_app. right. eauto. intros. congruence.
Qed.

Lemma code_size_upper_bound':
  forall defs gmap lmap dsize csize id f
    gmap1 lmap1 dsize1 csize1 
    (CZPOS: 0 <= csize1)
    (UPDATE: update_maps gmap1 lmap1 dsize1 csize1 defs = (gmap, lmap, dsize, csize))
    (IN: In (id, Some (Gfun (Internal f))) defs),
    code_size (Asm.fn_code f) <= csize.
Proof.
  induction defs. intros. inv IN.
  intros. inv IN.
  - unfold update_maps in UPDATE. simpl in UPDATE.
    destruct (update_instrs lmap1 csize1 id (Asm.fn_code f)) eqn:UPDATEINSTRS.
    assert (align z alignw <= csize).
    { eapply csize_mono; eauto. apply alignw_divides. }
    generalize (alignw_le z). intros.
    exploit update_instrs_code_size; eauto. intros. subst.
    omega.
  - unfold update_maps in UPDATE. simpl in UPDATE. destruct a.
    destruct (update_maps_def gmap1 lmap1 dsize1 csize1 i o) eqn:EQ.
    destruct p. destruct p. 
    eapply (IHdefs _ _ _ _ _ _ g l z0 z); eauto.
    assert (csize1 <= z).
    { eapply update_csize_mono; eauto. }
    omega.
Qed.

Lemma code_size_upper_bound:
  forall defs prog gmap lmap dsize csize id f gdefs
    (MAKEMAPS: make_maps prog = (gmap, lmap, dsize, csize))
    (PROG: defs ++ (id, Some (Gfun (Internal f))) :: gdefs = AST.prog_defs prog),
    code_size (Asm.fn_code f) <= csize.
Proof.
  intros. unfold make_maps in MAKEMAPS.
  eapply code_size_upper_bound'; eauto. omega.
  rewrite <- PROG. rewrite in_app. right. apply in_eq.
Qed.

Lemma transf_prog_code_size_pos: forall prog tprog id f
    (TRANSF: transf_program prog = OK tprog)
    (IN: In (id, Some (Gfun (Internal f))) (AST.prog_defs prog)),
    0 < Asm.code_size (Asm.fn_code f).
Proof.
  intros. unfold transf_program in TRANSF0.
  repeat destr_in TRANSF0. destruct w.
  red in wf_prog_not_empty.
  erewrite Forall_forall in wf_prog_not_empty; eauto.
  generalize (in_map snd (AST.prog_defs prog0) (id, Some (Gfun (Internal f))) IN).
  simpl. intros IN'.
  exploit wf_prog_not_empty; eauto.
Qed.


Lemma globs_meminj_domain_valid : forall gmap lmap dsize csize m2 b p
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize))
    (ALLOCG: Genv.alloc_globals ge Mem.empty (AST.prog_defs prog) = Some m2)
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize = OK tprog)
    (INJ: globs_meminj b = Some p),
    Mem.valid_block m2 b.
Proof.
  intros. unfold globs_meminj in INJ.
  destr_match_in INJ; inv INJ. destr_match_in H0; inv H0.
  assert (Genv.init_mem prog = Some m2) as INITM by auto.
  apply Genv.invert_find_symbol in EQ.
  eapply Genv.find_symbol_not_fresh; eauto.
Qed.

Lemma Nth_len : forall {A:Type} l1 (x:A) l2, Nth (length l1) (l1 ++ x :: l2) x.
Proof.
  induction l1. simpl. intros. 
  - constructor.
  - intros. simpl. constructor. apply IHl1.
Qed.

Lemma transl_prog_pres_nvi : 
  forall def i
    (NVI: ~sdef_is_var_or_internal_fun def)
    (IN: In (i, def) (AST.prog_defs prog)),
  exists n def' sb, def_is_none_or_external_fun (i, def', sb) /\ Nth n (prog_defs tprog) (i, def', sb).
Proof.
  intros. 
  intros. generalize TRANSF. intros TRANSF'.
  unfold match_prog,transf_program in TRANSF'.
  repeat destr_in TRANSF'. destruct w. 
  exploit transl_prog_pres_def; eauto.
  intros (def' & sb & IN' & TL).
  apply in_split in IN'. destruct IN' as (defs1' & gdefs1' & IN').
  exists (length defs1'), def', sb. split.
  - destruct def. destruct g0. destruct f.
    + monadInv TL. exfalso. apply NVI. red. auto.
    + monadInv TL. red. eauto.
    + monadInvX TL. exfalso. apply NVI. red. auto.
    + monadInv TL. red. eauto.
  - rewrite IN'.
    apply Nth_len.
Qed.

Lemma find_symbol_nvi_lower_bound : 
  forall def i b ofs
    (NVI: ~sdef_is_var_or_internal_fun def)
    (IN: In (i, def) (AST.prog_defs prog))
    (FSYM: Genv.find_symbol (globalenv tprog) i = Some (b, ofs)),
    Ple (pos_advance_N init_block (length (list_of_segments tprog))) b.
Proof.
  intros. generalize TRANSF. intros TRANSF'.
  unfold match_prog,transf_program in TRANSF'.
  repeat destr_in TRANSF'. destruct w. 
  intros. unfold globalenv in FSYM.
  exploit transl_prog_pres_def; eauto.  
  intros (def' & sb & IN' & TL).
  exploit transl_prog_pres_nvi; eauto.
  intros (n & def'' & sb' & NE & NTH).
  erewrite add_globals_find_symbol_ne in FSYM; eauto.
  simpl in FSYM. inv FSYM.
  simpl. apply pos_advance_N_ple.
  eapply transl_prog_list_norepet; eauto.
Qed.
  
Lemma transl_globdefs_pres_len  : forall g defs defs'
    (TL: transl_globdefs g defs = OK defs'),
    length defs = length defs'.
Proof.
  induction defs; intros; simpl.
  - monadInv TL. auto.
  - destruct a. monadInv TL. erewrite IHdefs; eauto. simpl. auto.
Qed.

Lemma transl_prog_pres_len  : forall g l p p' dz cz
    (TL: transl_prog_with_map g l p dz cz = OK p'),
    length (prog_defs p') = length (AST.prog_defs p).
Proof.
  intros. monadInv TL. simpl.
  erewrite transl_globdefs_pres_len; eauto.
Qed.


Lemma transl_prog_pres_nvi' :
  forall defs def gdefs i
    (DEFSTAIL : defs ++ (i, def) :: gdefs = AST.prog_defs prog)
    (NVI: ~sdef_is_var_or_internal_fun def),
  exists def' sb, def_is_none_or_external_fun (i, def', sb) /\ Nth (length defs) (prog_defs tprog) (i, def', sb).
Proof.
  intros. generalize TRANSF. intros TRANSF'.
  unfold match_prog,transf_program in TRANSF'.
  repeat destr_in TRANSF'. destruct w.
  exploit transl_prog_pres_def'; eauto.
  intros (defs' & gdefs' & def' & sb & IN' & TL1 & TL2 & TL3).
  exists def', sb. split. 
  - destruct def. destruct g0. destruct f.
    + monadInv TL2. exfalso. apply NVI. red. auto.
    + monadInv TL2. red. eauto.
    + monadInvX TL2. exfalso. apply NVI. red. auto.
    + monadInv TL2. red. eauto.
  - rewrite IN'.
    erewrite transl_globdefs_pres_len; eauto.
    apply Nth_len.
Qed.

Lemma find_symbol_nvi_eq:
  forall defs i def gdefs
    (DEFSTAIL : defs ++ (i, def) :: gdefs = AST.prog_defs prog)
    (NVIT: ~sdef_is_var_or_internal_fun def)
    (NPT: list_norepet (map (fun '(i, _) => i) (AST.prog_defs prog))),
            Genv.find_symbol (globalenv tprog) i = Some (pos_advance_N (Pos.of_succ_nat num_segments) (length defs), Ptrofs.zero).
Proof.
  intros. generalize TRANSF. intros TRANSF'.
  unfold match_prog,transf_program in TRANSF'.
  repeat destr_in TRANSF'. destruct w. 
  unfold globalenv.
  exploit transl_prog_pres_nvi'; eauto.
  intros (def' & sb & NE & NTH).
  erewrite add_globals_find_symbol_ne; eauto.
  eapply transl_prog_list_norepet; eauto.
Qed.  

Lemma pos_advance_N_succ_base : forall n,
    pos_advance_N 1 n = Pos.of_succ_nat n.
Proof.
  induction n; intros; simpl.
  - auto.
  - rewrite <- IHn. 
    rewrite <- psucc_advance_Nsucc_eq. simpl. auto.
Qed.

Lemma pos_advance_N_succ_commut: 
  forall n1 n2,
    pos_advance_N (Pos.of_succ_nat n1) n2 = pos_advance_N (Pos.of_succ_nat n2) n1.
Proof.
  induction n1; intros; simpl. 
  - apply pos_advance_N_succ_base.
  - repeat rewrite <- SuccNat2Pos.inj_succ. 
    erewrite <- IHn1. simpl. auto.
Qed.

Lemma pos_advance_N_plt : forall p n,
  (0 < n)%nat -> Plt p (pos_advance_N p n).
Proof.
  induction n; intros.
  - simpl. omega.
  - simpl.
    eapply Plt_le_trans. apply Pos.lt_succ_diag_r.
    apply pos_advance_N_ple.
Qed.

Lemma pos_advande_N_plt_mono: forall n1 n2 b,
  (n1 < n2)%nat -> Plt (pos_advance_N b n1) (pos_advance_N b n2).
Proof.
  induction n1; intros; simpl.
  - apply pos_advance_N_plt. auto.
  - destruct n2. omega.
    assert (n1 < n2)%nat by omega. 
    generalize (IHn1 n2 b H0). intros.
    simpl.
    repeat rewrite psucc_advance_Nsucc_eq. 
    rewrite <- Pos.succ_lt_mono. auto.
Qed.

Lemma pos_advance_N_plt_add: 
  forall b n1 n2, Plt (pos_advance_N b n1) (pos_advance_N b (n1+(Datatypes.S n2))).
Proof.
  intros. apply pos_advande_N_plt_mono.
  omega.
Qed.

Lemma pos_advande_N_ple_mono: forall n1 n2 b,
  (n1 <= n2)%nat -> Ple (pos_advance_N b n1) (pos_advance_N b n2).
Proof.
  induction n1; intros; simpl.
  - apply pos_advance_N_ple. 
  - destruct n2. omega.
    assert (n1 <= n2)%nat by omega.
    generalize (IHn1 n2 b H0). intros.
    simpl.
    repeat rewrite psucc_advance_Nsucc_eq. 
    rewrite <- Pos.succ_le_mono. auto.
Qed.


Lemma pos_advance_N_ple_add: 
  forall b n1 n2, Ple (pos_advance_N b n1) (pos_advance_N b (n1+n2)).
Proof.
  intros. apply pos_advande_N_ple_mono.
  omega.
Qed.


Lemma partial_genv_genv_next_bound: 
  forall defs def gdefs prog i
    (DEFSTAIL: defs ++ (i, def) :: gdefs = AST.prog_defs prog),
    Plt (pos_advance_N (Globalenvs.Genv.genv_next (partial_genv defs)) num_segments)
        (pos_advance_N init_block (length (list_of_segments tprog) + length (AST.prog_defs prog))).
Proof.
  intros. rewrite partial_genv_next.
  rewrite pos_advance_N_succ_commut. simpl.
  rewrite <- DEFSTAIL. rewrite app_length. simpl.
  apply pos_advance_N_plt_add.
Qed.

Lemma find_symbol_sb_vit : forall i odef sid ofs
    (IN: In (i, odef) (AST.prog_defs prog))
    (FSYM: Genv.find_symbol (globalenv tprog) i = Some (gen_segblocks tprog sid, ofs)),
    (sdef_is_var_or_internal_fun odef).
Proof.
  intros.
  destruct (vit_dec _ _ odef); eauto.
  assert (Ple (pos_advance_N init_block (length (list_of_segments tprog))) 
              (gen_segblocks tprog sid)).
  eapply find_symbol_nvi_lower_bound; eauto.
  generalize (gen_segblocks_upper_bound tprog sid).
  intros. exfalso. eapply Plt_le_absurd; eauto.
Qed.



Lemma app_same_len_prefix : forall {A:Type} (l1:list A) l2 x l1' l2' x',
    length l1 = length l1' -> 
    l1 ++ x :: l2 = l1' ++ x':: l2' ->
    x = x'.
Proof.
  induction l1; intros; simpl in *.
  - destruct l1'. inv H0. auto. inv H.
  - destruct l1'. inv H. simpl in H. inv H.
    inv H0. eapply IHl1; eauto.
Qed.

Lemma zero_le_ptrofs_max: (0 <= Ptrofs.max_unsigned).
Proof.
  generalize (instr_size_repr (Asm.Pmovsb)). omega.
Qed.

Lemma four_le_suc_len :  
  forall {A:Type} (defs: list A),
    (4 <= Pos.succ (Pos.succ (Pos.succ (Pos.of_succ_nat (length defs)))))%positive.
Proof.
  intros.
  assert (pos_advance_N 4 (length defs) = Pos.succ (Pos.succ (Pos.succ (Pos.of_succ_nat (length defs))))).
  replace (4%positive) with (Pos.of_succ_nat 3).
  rewrite pos_advance_N_succ_commut. simpl. auto. unfold Pos.of_succ_nat. simpl. auto.
  rewrite <- H. apply pos_advance_N_ple.
Qed.

Lemma store_globals_inject :
  forall gdefs tgdefs defs m1 m2 m1' gmap lmap dsize csize 
    (DEFNAMES: list_norepet (map fst (AST.prog_defs prog)))
    (DEFSTAIL: defs ++ gdefs = AST.prog_defs prog)
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize))
    (BOUND: dsize + csize <= Ptrofs.max_unsigned)
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize = OK tprog)
    (TRANSG: transl_globdefs gmap gdefs = OK tgdefs)
    (MINJ: Mem.weak_inject globs_meminj (def_frame_inj m1) m1 m1')
    (ALLOCG: Genv.alloc_globals ge m1 gdefs = Some m2)
    (BLOCKEQ : Mem.nextblock m1 = Globalenvs.Genv.genv_next (partial_genv defs))
    (BLOCKEQ' : Mem.nextblock m1' = (pos_advance_N init_block (length (list_of_segments tprog) + length (AST.prog_defs prog))))
    (STK' : Mem.stack m1' = nil)
    (PERMOFS : forall b ofs k p, Mem.perm m1' b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned)
    (OFSBOUND: forall id b def ofs k p,
        Globalenvs.Genv.find_symbol (partial_genv defs) id = Some b ->
        In (id, def) defs -> Mem.perm m1 b ofs k p ->
        ofs < odef_size def)
    (FINDVALIDSYM: forall id b ofs k p,
       Globalenvs.Genv.find_symbol ge id = Some b ->
       Mem.perm m1 b ofs k p ->
       Globalenvs.Genv.find_symbol (partial_genv defs) id = Some b)
    (DEFSPERM: forall id odef b' delta,
       In (id, odef) gdefs ->
       Genv.find_symbol tge id = Some (b', delta) ->
       (forall ofs k p, 0 <= ofs < odef_size odef -> Mem.perm m1' b' (Ptrofs.unsigned delta+ofs) k p)),
    exists m2', store_globals_iter tge (length defs) (gen_segblocks tprog) m1' tgdefs = Some m2'
           /\ Mem.weak_inject globs_meminj (def_frame_inj m2) m2 m2'.
Proof.
  induction gdefs; intros.
  - monadInv TRANSG. inv ALLOCG. rewrite app_nil_r in DEFSTAIL. subst defs.
    simpl. eexists; split; eauto.
  - destruct a. destruct o.
    + destruct g. destruct f.
      * (** the head of gdefs is an internal function **)
        monadInv TRANSG. monadInv EQ.
        simpl in ALLOCG. destr_match_in ALLOCG; try now inversion ALLOCG.
        destruct (Mem.alloc m1 0 1) eqn:ALLOCF.
        exploit Mem.alloc_result; eauto using ALLOCF. intros.
        exploit update_map_gmap_some; eauto. red. auto.
        intros (slbl & GMAP & OFSRANGE & OFSRANGE2).

        (* globs_meminj *)
        assert (globs_meminj b = Some (gen_segblocks tprog (fst slbl), Ptrofs.unsigned (snd slbl))) as BINJ.
        {
          unfold globs_meminj. subst. rewrite BLOCKEQ.
          exploit genv_invert_symbol_next; eauto. intros INVSYM.
          setoid_rewrite INVSYM.
          erewrite gmap_to_find_symbol; eauto.
          rewrite <- DEFSTAIL. rewrite in_app. right. apply in_eq.
          red. auto.
        }

        (* alloc mapped injection *)
        exploit (Mem.alloc_left_mapped_weak_inject
                   globs_meminj (def_frame_inj m1) m1 m1' 0 1 m0
                   b (gen_segblocks tprog (fst slbl)) (Ptrofs.unsigned (snd slbl))
                   BINJ MINJ ALLOCF); eauto.
        (* valid block *)
        exploit update_map_gmap_range1; eauto. intros.
        exploit (gen_segblocks_in_valid tprog); eauto. intros SEGBVALID.
        red in SEGBVALID. destruct SEGBVALID. red.
        rewrite BLOCKEQ'.         
        eapply Plt_le_trans. eauto.
        apply pos_advance_N_ple_add.
        (* valid offset *)
        apply Ptrofs.unsigned_range_2.
        (* has permission *)
        intros ofs k p OFS INJPERM.
        exploit (fun id odef b' delta => DEFSPERM id odef b' delta); eauto.
        apply in_eq.
        eapply gmap_to_find_symbol; eauto. rewrite <- DEFSTAIL. rewrite in_app. right. apply in_eq.
        red. auto.
        instantiate (1:=ofs).
        exploit prog_odef_size_pos; eauto. intros.
        assert (ofs = 0) by omega. subst. split; auto. omega.
        rewrite Zplus_comm. eauto.
        (* correct alignment *)
        red. intros.
        eapply update_map_gmap_aligned; eauto.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS). omega.
        omega.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS). omega.
        omega.
        unfold default_gid_map. intros. congruence.
        (* alloced memory has not been injected before *)
        intros b0 delta' ofs k p GINJ PERM' OFSABSURD.
        unfold globs_meminj in GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destruct p0. inv GINJ.
        apply Genv.invert_find_symbol in EQ2.
        exploit FINDVALIDSYM; eauto. intros.
        exploit find_symbol_inversion_1; eauto. intros (def' & IN).        
        assert (sdef_is_var_or_internal_fun def').
        {
          eapply find_symbol_sb_vit; eauto.
          rewrite <- DEFSTAIL. rewrite in_app. auto.
        }
        exploit find_symbol_to_gmap; eauto.
        rewrite <- DEFSTAIL. rewrite in_app. auto.
        intros (slbl1 & GMAP1 & GEN & IEQ). subst.
        assert (fst slbl1 = fst slbl).
        { 
          generalize (gen_segblocks_injective tprog). intros SEGSINJ.
          red in SEGSINJ.
          exploit SEGSINJ; eauto.
          apply gen_segblocks_in_valid. eapply update_map_gmap_range1; eauto. auto.
        }
        exploit OFSBOUND; eauto. intros.
        assert (Ptrofs.unsigned (snd slbl1) + odef_size def' <= Ptrofs.unsigned (snd slbl)).
        { eapply (OFSRANGE _ _ _ IN GMAP1); eauto. }
        omega.
        (* stack frame is public *)
        intros fi INSTK o k pp PERM INJPERM.
        rewrite STK' in INSTK. inv INSTK.
        (* get the new weak injection *)
        intros MINJ'.
        erewrite alloc_pres_def_frame_inj in MINJ'; eauto.

        (* drop_perm injection *)
        exploit transf_prog_code_size_pos; eauto.
        rewrite <- DEFSTAIL. rewrite in_app. right. apply in_eq. intros.
        exploit (fun j g m1 m2 b1 b2 delta =>
                   Mem.drop_extended_parallel_weak_inject j g m1 m2 b1 b2 delta
                                                          0 1 0 (Asm.code_size (Asm.fn_code f))); eauto using MINJ'.
        (* inject perm *)
        red. simpl. auto. omega.
        (* hi *)
        omega.
        (* range perm *)
        simpl. red. intros ofs OFS.
        replace ofs with (Ptrofs.unsigned (snd slbl) + (ofs - (Ptrofs.unsigned (snd slbl)))) by omega.
        eapply DEFSPERM with (ofs:= ofs-Ptrofs.unsigned(snd slbl)); eauto. apply in_eq.
        eapply gmap_to_find_symbol; eauto. rewrite <- DEFSTAIL. rewrite in_app. right. apply in_eq.
        red. auto.
        simpl. omega.
        (* source memory have no permission on extended regions *)
        intros b' delta' ofs' k p BINJ' PERM' OFS. destruct OFS. omega.
        unfold globs_meminj in BINJ'. destr_match_in BINJ'; inv BINJ'.
        destr_match_in H3; inv H3.
        destruct p0. inv H2.
        generalize EQ2. intros IVSYM.
        apply Genv.invert_find_symbol in IVSYM.
        apply find_symbol_inversion_2 in IVSYM. destruct IVSYM as (def & IVSYM).
        exploit find_symbol_sb_vit; eauto.
        intros VIT.
        exploit Mem.perm_alloc_inv; eauto.
        destruct eq_block.
        (** b' = Mem.nextblock m1 **)
        subst.
        rewrite BLOCKEQ in EQ2.
        erewrite genv_invert_symbol_next in EQ2; eauto. inv EQ2.
        erewrite gmap_to_find_symbol in EQ3; eauto. inv EQ3. intros. omega.
        (** b' <> Mem.nextblock m1 **)
        intros PERM''.
        apply Genv.invert_find_symbol in EQ2.
        exploit FINDVALIDSYM; eauto.
        intros FINDSYM'.
        exploit find_symbol_inversion_1; eauto. intros (def' & IN). 
        exploit OFSBOUND; eauto. intros OFS'.
        exploit find_symbol_to_gmap; eauto. intros (slbl1 & GMAP' & GEQ & IEQ). subst.
        assert (Ptrofs.unsigned (snd slbl1) + odef_size def' <= Ptrofs.unsigned (snd slbl)) as SZBND.
        { 
          eapply OFSRANGE; eauto. 
          generalize (gen_segblocks_injective tprog). intros SEGSINJ.
          red in SEGSINJ.
          exploit SEGSINJ; eauto.
          apply gen_segblocks_in_valid. eapply update_map_gmap_range1; eauto. auto.          
        }
        simpl in SZBND. simpl in OFS'. omega.

        intros (m2' & DROP & MINJ'').
        erewrite drop_perm_pres_def_frame_inj in MINJ''; eauto.

        (* apply the induction hypothesis *)
        assert ((defs ++ (i, Some (Gfun (Internal f))) :: nil) ++ gdefs = AST.prog_defs prog) as DEFSTAIL'.
        rewrite <- DEFSTAIL. rewrite <- app_assoc. simpl. auto.
        exploit (IHgdefs x0 (defs ++ (i, Some (Gfun (Internal f))) :: nil) m); eauto using MINJ'', DEFSTAIL'.
        (* nextblock *)
        erewrite Mem.nextblock_drop; eauto.
        erewrite Mem.nextblock_alloc; eauto. rewrite BLOCKEQ.
        rewrite partial_genv_next_succ. auto.
        (* nextblock' *)
        erewrite Mem.nextblock_drop; eauto.
        (* stack *)
        erewrite Mem.drop_perm_stack; eauto.
        (* perm ofs *)
        intros b0 ofs k p PERM.
        exploit Mem.perm_drop_4; eauto.
        (* ofsbound *)
        intros id b0 def ofs k p FINDSYM IN PERM'.
        rewrite in_app in IN. destruct IN as [IN | IN].
        assert (i <> id).
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq in FINDSYM; eauto.
        assert (b <> b0).
        {
          unfold not. subst. rewrite BLOCKEQ. intros. subst.
          eapply Genv.find_symbol_genv_next_absurd; eauto.
        }
        erewrite (drop_perm_perm _ _ _ _ _ _ EQ) in PERM'. destruct PERM' as [PERM' PIN].
        exploit Mem.perm_alloc_inv; eauto using ALLOCF.
        rewrite dec_eq_false; auto. intros. eapply OFSBOUND; eauto.

        inv IN. inv H1.
        rewrite partial_genv_find_symbol_eq in FINDSYM. inv FINDSYM.
        rewrite <- BLOCKEQ in PERM'.
        erewrite (drop_perm_perm _ _ _ _ _ _ EQ) in PERM'. destruct PERM' as [PERM' PIN].
        exploit Mem.perm_alloc_inv; eauto using ALLOCF.
        rewrite dec_eq_true. intros.
        simpl. assert (ofs = 0). omega. subst.
        eapply (prog_odef_size_pos defs id (Some (Gfun (Internal f)))); eauto.

        inv H1.
        (* findvalidsym *)
        intros id b0 ofs k p FINDSYM PERM.
        erewrite drop_perm_perm in PERM; eauto. destruct PERM as [PERM COND].
        erewrite alloc_perm in PERM; eauto. destruct peq.
        subst. rewrite BLOCKEQ.
        rewrite BLOCKEQ in FINDSYM. apply Genv.find_invert_symbol in FINDSYM.
        unfold ge in FINDSYM. erewrite genv_invert_symbol_next in FINDSYM; eauto. inv FINDSYM.
        erewrite partial_genv_find_symbol_eq; eauto.
        exploit FINDVALIDSYM; eauto. intros FINDSYM'.
        apply find_symbol_inversion_1 in FINDSYM'. destruct FINDSYM' as [DEF' FINDSYM'].
        assert (i <> id).
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq; eauto.
        (* defs perm *)
        intros id odef b' delta IN FSYM ofs k p OFS.
        eapply Mem.perm_drop_3; eauto.
        destruct (eq_block b' (gen_segblocks tprog (fst slbl))); auto.
        right. right.
        destruct (vit_dec _ _ odef).
        exploit find_symbol_to_gmap; eauto. rewrite <- DEFSTAIL. rewrite in_app. right. simpl. auto.
        intros (slbl0 & GMAP' & BEQ & IEQ).
        assert (odef_size (Some (Gfun (Internal f))) + Ptrofs.unsigned (snd slbl) <= Ptrofs.unsigned (snd slbl0)) as SZBND.
        {
          eapply (make_maps_ofs_ordering prog (defs ++ (i, Some (Gfun (Internal f))) :: nil) gdefs
                                           i id (Some (Gfun (Internal f))) odef); eauto.
          rewrite in_app. right. apply in_eq.
          generalize (gen_segblocks_injective tprog). unfold injective_on_valid_segs.
          intros INJECTIVE. subst. eapply INJECTIVE; eauto.
          eapply gen_segblocks_in_valid; eauto.
          eapply update_map_gmap_range1; eauto.
        }
        subst. simpl in SZBND.
        exploit prog_odef_size_pos; eauto. intros. simpl in H. subst. omega.
        apply in_split in IN. destruct IN as (defs1 & gdefs1 & IN).
        erewrite find_symbol_nvi_eq with 
            (defs:=defs ++ (i, Some (Gfun (Internal f))) :: defs1)
            (gdefs:=gdefs1) in FSYM; eauto.
        inv FSYM.
        generalize (gen_segblocks_upper_bound tprog (fst slbl)). intros PLT.
        simpl in PLT.
        rewrite <- H2 in PLT.
        exfalso. eapply Plt_strict. eapply Plt_le_trans. apply PLT.
        apply pos_advance_N_ple. subst.
        rewrite <- DEFSTAIL. rewrite <- app_assoc. simpl. reflexivity.
        eapply DEFSPERM; eauto. apply in_cons; auto.
        
        (* finish this case *)
        intros (m3' & ALLOCG' & MINJ_FINAL).
        exists m3'. split; auto. simpl.
        exploit transl_fun_inversion; eauto.
        intros (slbl' & GMAP' & FRANGE).
        rewrite GMAP in GMAP'. inv GMAP'. rewrite FRANGE. simpl.
        setoid_rewrite Ptrofs.unsigned_repr.
        rewrite Z.add_comm. setoid_rewrite DROP. 
        rewrite app_length in ALLOCG'. 
        rewrite Nat.add_comm in ALLOCG'. simpl in ALLOCG'. auto.
        assert (code_size (Asm.fn_code f) <= csize).
        eapply code_size_upper_bound; eauto.
        exploit make_maps_sizes_pos; eauto. intros (DSZPOS & CSZPOS).
        omega.

      * (** the head of gdefs is an external function **)
        monadInv TRANSG.
        simpl in ALLOCG. destr_match_in ALLOCG; try now inversion ALLOCG.
        destruct (Mem.alloc m1 0 1) eqn:ALLOCF.
        exploit Mem.alloc_result; eauto using ALLOCF. intros.
        simpl.
        (* assert (gmap i = None). *)
        (* {  *)
        (*   eapply update_map_gmap_none with (def := (Some (Gfun (External e)))); eauto.  *)
        (*   rewrite <- DEFSTAIL. apply in_app. right. apply in_eq. *)
        (* } *)

        (* globs_meminj *)
        assert (globs_meminj b = Some ((pos_advance_N b num_segments),0)) as BINJ.
        {
          unfold globs_meminj. subst b. rewrite BLOCKEQ.
          erewrite genv_invert_symbol_next; eauto.
          erewrite find_symbol_nvi_eq; eauto.
          rewrite partial_genv_next. f_equal. f_equal. 
          apply pos_advance_N_succ_commut.
        }
        
        (* alloc mapped injection *)
        exploit (Mem.alloc_left_mapped_weak_inject
                   globs_meminj (def_frame_inj m1) m1 m1' 0 1 m0
                   b (pos_advance_N b num_segments) 0
                   BINJ MINJ ALLOCF); eauto.
        (* valid block *)
        red. rewrite BLOCKEQ'. subst b. rewrite BLOCKEQ.
        eapply partial_genv_genv_next_bound; eauto.
        (* valid offset *)
        generalize (instr_size_repr Pmovsb). omega.
        (* has permission *)
        intros.
        assert (ofs =Ptrofs.unsigned Ptrofs.zero). 
        unfold Ptrofs.zero. rewrite Ptrofs.unsigned_repr. omega. 
        generalize zero_le_ptrofs_max. omega.
        subst.
        eapply DEFSPERM; eauto.
        apply in_eq.
        erewrite find_symbol_nvi_eq; eauto.
        repeat apply f_equal; eauto. rewrite BLOCKEQ.
        rewrite partial_genv_next.
        rewrite pos_advance_N_succ_commut. auto.
        simpl. omega.
        (* correct alignment *)
        simpl. red. intros. apply Z.divide_0_r.
        (* alloced memory has not been injected before *)
        simpl.
        intros b0 delta' ofs k p GINJ PERM' OFSABSURD.
        unfold globs_meminj in GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destruct p0. inv GINJ.
        (* assert (ofs + Ptrofs.unsigned i1 = 0) by omega. *)
        assert (i0 = i).
        {
          eapply Genv.invert_find_symbol in EQ1.
          generalize EQ1. intros FSYM.
          apply find_symbol_inversion_2 in EQ1. destruct EQ1 as (def1 & EQ1).
          generalize EQ1. intros IN.
          apply in_split in EQ1. destruct EQ1 as (defs1 & gdefs1 & EQ1).
          destruct (vit_dec _ _ def1).
          (* def1 is vit *)
          exploit find_symbol_to_gmap; eauto.
          intros (slbl & GMAP & BEQ & IEQ). 
          erewrite gmap_to_find_symbol in EQ2; eauto. inv EQ2.
          generalize (gen_segblocks_upper_bound tprog (fst slbl)). 
          intros PLT. erewrite BLOCKEQ in H0.
          erewrite partial_genv_next in H0. rewrite H0 in PLT.
          exfalso. eapply Plt_strict. simpl in PLT. eapply Plt_le_trans. apply PLT.
          apply four_le_suc_len.
          (* def1 is not vit *)
          erewrite find_symbol_nvi_eq in EQ2; eauto. inv EQ2.
          rewrite BLOCKEQ in H0. rewrite partial_genv_next in H0.
          replace (4%positive) with (Pos.of_succ_nat 3) in H0.
          rewrite pos_advance_N_succ_commut in H0. simpl in H0. 
          repeat apply Pos.succ_inj in H0. apply SuccNat2Pos.inj in H0.
          rewrite <- DEFSTAIL in EQ1. symmetry in H0.
          assert ((i, Some (Gfun (External e))) = (i0, def1)).
          eapply app_same_len_prefix; eauto. inv H. auto.
          unfold Pos.of_succ_nat. simpl. auto.
        }
        subst i0. apply Genv.invert_find_symbol in EQ1.
        erewrite genv_find_symbol_next in EQ1; eauto. inv EQ1.
        apply Mem.perm_valid_block in PERM'. rewrite <- BLOCKEQ in PERM'.
        red in PERM'. eapply Plt_strict; eauto.

        (* stack frame is public *)
        intros fi INSTK o k pp PERM INJPERM.
        rewrite STK' in INSTK. inv INSTK.
        (* get the new weak injection *)
        intros MINJ'.
        erewrite alloc_pres_def_frame_inj in MINJ'; eauto.

        (* drop_perm injection *)
        exploit Mem.drop_parallel_weak_inject; eauto using MINJ'.
        red. simpl. auto.
        intros (m2' & DROP & MINJ'').
        erewrite drop_perm_pres_def_frame_inj in MINJ''; eauto.

        (* apply IH *)
        exploit (IHgdefs x (defs ++ (i, (Some (Gfun (External e)))) :: nil) m m2); eauto.
        rewrite <- DEFSTAIL. rewrite List.app_assoc_reverse. simpl. auto.

        (* next block *)
        erewrite Mem.nextblock_drop; eauto. 
        erewrite Mem.nextblock_alloc; eauto.
        erewrite partial_genv_next_succ. f_equal. 
        (* nextblock' *)
        rewrite BLOCKEQ. auto.
        erewrite Mem.nextblock_drop; eauto.
        (* stack *)
        erewrite Mem.drop_perm_stack; eauto.
        (* perm ofs *)
        intros b0 ofs k p PERM.
        exploit Mem.perm_drop_4; eauto.
        (* ofsbound *)
        intros id b0 def ofs k p FINDSYM IN PERM'.
        rewrite in_app in IN. destruct IN as [IN | IN].
        assert (i <> id).
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq in FINDSYM; eauto.
        assert (b <> b0).
        {
          unfold not. subst. rewrite BLOCKEQ. intros. subst.
          eapply Genv.find_symbol_genv_next_absurd; eauto.
        }
        erewrite (drop_perm_perm _ _ _ _ _ _ EQ0) in PERM'. destruct PERM' as [PERM' PIN].
        exploit Mem.perm_alloc_inv; eauto using ALLOCF.
        rewrite dec_eq_false; auto. intros. eapply OFSBOUND; eauto.

        inv IN. inv H0.
        rewrite partial_genv_find_symbol_eq in FINDSYM. inv FINDSYM.
        rewrite <- BLOCKEQ in PERM'.
        erewrite (drop_perm_perm _ _ _ _ _ _ EQ0) in PERM'. destruct PERM' as [PERM' PIN].
        exploit Mem.perm_alloc_inv; eauto using ALLOCF.
        rewrite dec_eq_true. intros.
        simpl. assert (ofs = 0). omega. subst.
        omega.

        inv H0.
        (* findvalidsym *)
        intros id b0 ofs k p FINDSYM PERM.
        erewrite drop_perm_perm in PERM; eauto. destruct PERM as [PERM COND].
        erewrite alloc_perm in PERM; eauto. destruct peq.
        subst. rewrite BLOCKEQ.
        rewrite BLOCKEQ in FINDSYM. apply Genv.find_invert_symbol in FINDSYM.
        unfold ge in FINDSYM. erewrite genv_invert_symbol_next in FINDSYM; eauto. inv FINDSYM.
        erewrite partial_genv_find_symbol_eq; eauto.
        exploit FINDVALIDSYM; eauto. intros FINDSYM'.
        apply find_symbol_inversion_1 in FINDSYM'. destruct FINDSYM' as [DEF' FINDSYM'].
        assert (i <> id).
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq; eauto.
        (* defs perm *)
        intros id odef b' delta IN FSYM ofs k p OFS.
        eapply Mem.perm_drop_3; eauto. 
        destruct (eq_block b' (pos_advance_N b num_segments)); auto. subst.
        destruct (vit_dec _ _ odef).
        exploit find_symbol_to_gmap; eauto. rewrite <- DEFSTAIL. rewrite in_app. right. simpl. auto.
        intros (slbl0 & GMAP' & BEQ & IEQ).
        generalize (gen_segblocks_upper_bound tprog (fst slbl0)). intros PLT.
        simpl in PLT.
        rewrite <- BEQ in PLT.
        exfalso. eapply Plt_strict. eapply Plt_le_trans. apply PLT.
        rewrite BLOCKEQ. rewrite partial_genv_next. simpl.
        apply four_le_suc_len.
        
        apply in_split in IN. destruct IN as (defs1 & gdefs1 & IN).
        erewrite find_symbol_nvi_eq with 
            (defs:=defs ++ (i, Some (Gfun (External e))) :: defs1)
            (gdefs:=gdefs1) in FSYM; eauto.
        inv FSYM.
        rewrite BLOCKEQ in H0. rewrite partial_genv_next in H0.
        replace (4%positive) with (Pos.of_succ_nat 3) in H0.
        rewrite pos_advance_N_succ_commut in H0. simpl in H0. 
        repeat apply Pos.succ_inj in H0. apply SuccNat2Pos.inj in H0.
        rewrite app_length in H0. simpl in H0. omega.
        unfold Pos.of_succ_nat. simpl. auto.
        rewrite <- DEFSTAIL. rewrite IN.
        rewrite <- app_assoc. auto.
        eapply DEFSPERM; eauto. simpl. eauto.

        (* finish this case *)
        intros (m3' & ALLOCG' & MINJ_FINAL).
        exists m3'. split; auto. simpl.
        simpl in DROP. subst. rewrite BLOCKEQ in DROP.
        rewrite partial_genv_next in DROP.
        replace (4%positive) with (Pos.of_succ_nat 3).
        rewrite pos_advance_N_succ_commut. simpl.
        setoid_rewrite DROP. 
        rewrite app_length in ALLOCG'. simpl in ALLOCG'.
        rewrite Nat.add_comm in ALLOCG'. simpl in ALLOCG'. auto.
        unfold Pos.of_succ_nat. simpl. auto.

      * (** the head of gdefs is a global variable **)
        monadInv TRANSG. destruct (gmap i) eqn:ILBL; try now inversion EQ.
        destruct s. monadInv EQ. 
        simpl in ALLOCG.
        destr_match_in ALLOCG; try now inversion ALLOCG.
        destr_match_in EQ.
        destr_match_in EQ; try now inversion EQ.
        destr_match_in EQ; try now inversion EQ.
        rename EQ0 into ALLOCINIT.
        rename EQ2 into STOREZERO.
        rename EQ3 into STOREINIT.
        rename EQ into DROP.
        exploit Mem.alloc_result; eauto using ALLOCINIT. intros.
        exploit update_map_gmap_some; eauto. red. auto.
        intros (slbl & GMAP & OFSRANGE & OFSRANGE2).

        (* globs_meminj *)
        assert (globs_meminj b = Some (gen_segblocks tprog (fst slbl), Ptrofs.unsigned (snd slbl))) as BINJ.
        {
          unfold globs_meminj. subst. rewrite BLOCKEQ.
          exploit genv_invert_symbol_next; eauto. intros INVSYM.
          setoid_rewrite INVSYM. 
          erewrite gmap_to_find_symbol; eauto.
          rewrite <- DEFSTAIL. rewrite in_app. right. apply in_eq.
          red. auto.
        }

        (* alloc mapped injection *)
        exploit (Mem.alloc_left_mapped_weak_inject
                   globs_meminj (def_frame_inj m1) m1 m1' 0 (init_data_list_size (gvar_init v)) m0
                   b (gen_segblocks tprog (fst slbl)) (Ptrofs.unsigned (snd slbl))
                   BINJ MINJ ALLOCINIT); eauto.
        (* valid block *)
        exploit update_map_gmap_range1; eauto. intros.
        exploit (gen_segblocks_in_valid tprog); eauto. intros SEGBVALID.
        red in SEGBVALID. destruct SEGBVALID. red.
        rewrite BLOCKEQ'. auto.
        eapply Plt_le_trans. eauto.
        apply pos_advance_N_ple_add.
        (* valid offset *)
        apply Ptrofs.unsigned_range_2.
        (* preservation of permission *)
        intros ofs k p OFS INJPERM.
        exploit (fun id odef b' delta => DEFSPERM id odef b' delta); eauto.
        apply in_eq.
        eapply gmap_to_find_symbol; eauto. rewrite <- DEFSTAIL. rewrite in_app. right. apply in_eq.
        red. auto.
        instantiate (1:=ofs).
        exploit prog_odef_size_pos; eauto. intros.
        rewrite Zplus_comm. eauto.
        (* correct alignment *)
        red. intros.
        eapply update_map_gmap_aligned; eauto.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS ). omega.
        omega.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS). omega.
        omega.
        unfold default_gid_map. intros. congruence.
        (* alloced memory has not been injected before *)
        intros b0 delta' ofs k p GINJ PERM' OFSABSURD.
        unfold globs_meminj in GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destruct p0. inv GINJ.
        apply Genv.invert_find_symbol in EQ.
        exploit FINDVALIDSYM; eauto. intros.
        exploit find_symbol_inversion_1; eauto. intros (def' & IN).        
        assert (sdef_is_var_or_internal_fun def').
        {
          eapply find_symbol_sb_vit; eauto.
          rewrite <- DEFSTAIL. rewrite in_app. auto.
        }
        exploit find_symbol_to_gmap; eauto.
        rewrite <- DEFSTAIL. rewrite in_app. auto.
        intros (slbl1 & GMAP1 & GEN & IEQ). subst.
        assert (fst slbl1 = fst slbl).
        { 
          generalize (gen_segblocks_injective tprog). intros SEGSINJ.
          red in SEGSINJ.
          exploit SEGSINJ; eauto.
          apply gen_segblocks_in_valid. eapply update_map_gmap_range1; eauto. auto.
        }
        exploit OFSBOUND; eauto. intros.
        assert (Ptrofs.unsigned (snd slbl1) + odef_size def' <= Ptrofs.unsigned (snd slbl)).
        { eapply (OFSRANGE _ _ _ IN GMAP1); eauto. }
        omega.
        (* stack frame is public *)
        intros fi INSTK o k pp PERM INJPERM.
        rewrite STK' in INSTK. inv INSTK.
        (* get the new weak injection *)
        intros MINJ'.
        erewrite alloc_pres_def_frame_inj in MINJ'; eauto.

        (* store_zeros injection *)
        exploit store_zeros_mapped_inject; eauto.
        intros (m2' & STOREZERO' & MINJZ).
        erewrite (store_zeros_pres_def_frame_inj m0) in MINJZ; eauto.
        
        (* store_init_data_list inject *)
        exploit store_init_data_list_mapped_inject; eauto.
        intros (m3' & STOREINIT' & MINJSI).
        erewrite store_init_data_list_pres_def_frame_inj in MINJSI; eauto.
        
        (* dorp_perm inject *)
        exploit Mem.drop_parallel_weak_inject; eauto.
        red. simpl. auto.
        intros (m4' & DROP' & MINJDR).
        erewrite drop_perm_pres_def_frame_inj in MINJDR; eauto.
        
        (* apply the induction hypothesis *)
        assert ((defs ++ (i, Some (Gvar v)) :: nil) ++ gdefs = AST.prog_defs prog) as DEFSTAIL'.
        rewrite <- DEFSTAIL. rewrite <- app_assoc. simpl. auto.
        exploit (IHgdefs x0 (defs ++ (i, Some (Gvar v)) :: nil) m); eauto using MINJDR, DEFSTAIL'.
        (* nextblock *)
        erewrite Mem.nextblock_drop; eauto.
        erewrite Genv.store_init_data_list_nextblock; eauto.
        erewrite Genv.store_zeros_nextblock; eauto.
        erewrite Mem.nextblock_alloc; eauto. rewrite BLOCKEQ.
        rewrite partial_genv_next_succ. auto.
        (* nextblock' *)
        erewrite (Mem.nextblock_drop m3'); eauto.
        erewrite (store_init_data_list_nextblock _ _ m2'); eauto.
        erewrite Genv.store_zeros_nextblock; eauto.
        (* stack *)
        erewrite (Mem.drop_perm_stack m3'); eauto.
        erewrite (store_init_data_list_stack _ _ m2'); eauto.
        erewrite (Genv.store_zeros_stack m1'); eauto.
        (* perm ofs *)
        intros b0 ofs k p PERM.
        exploit Mem.perm_drop_4; eauto. intros PERM'.
        erewrite <- (store_init_data_list_perm _ _ m2') in PERM'; eauto.
        erewrite <- (Genv.store_zeros_perm _ _ _ _ m1') in PERM'; eauto.
        (* perm *)
        intros id b0 def ofs k p FINDSYM IN PERM'.
        rewrite in_app in IN. destruct IN as [IN | IN].

        assert (i <> id).
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq in FINDSYM; eauto.
        assert (b <> b0).
        {
          unfold not. subst. rewrite BLOCKEQ. intros. subst.
          eapply Genv.find_symbol_genv_next_absurd; eauto.
        }
        erewrite (drop_perm_perm _ _ _ _ _ _ DROP) in PERM'. destruct PERM' as [PERM' PIN].
        erewrite <- (Genv.store_init_data_list_perm _ _ _ _ _ _ _ _ _ STOREINIT) in PERM'; eauto.
        erewrite <- (Genv.store_zeros_perm _ _ _ _ _ _ _ _ STOREZERO) in PERM'; eauto.
        exploit Mem.perm_alloc_inv; eauto using ALLOCINIT.
        rewrite dec_eq_false; auto. intros. eapply OFSBOUND; eauto.

        inv IN. inv H0.
        rewrite partial_genv_find_symbol_eq in FINDSYM. inv FINDSYM.
        rewrite <- BLOCKEQ in PERM'.
        erewrite (drop_perm_perm _ _ _ _ _ _ DROP) in PERM'. destruct PERM' as [PERM' PIN].
        erewrite <- (Genv.store_init_data_list_perm _ _ _ _ _ _ _ _ _ STOREINIT) in PERM'; eauto.
        erewrite <- (Genv.store_zeros_perm _ _ _ _ _ _ _ _ STOREZERO) in PERM'; eauto.
        exploit Mem.perm_alloc_inv; eauto using ALLOCINIT.
        rewrite dec_eq_true. intros.
        simpl. omega.

        inv H0.
        
        (* findvalidsym *)
        intros id b0 ofs k p FINDSYM PERM.
        erewrite drop_perm_perm in PERM; eauto. destruct PERM as [PERM COND].
        erewrite <- Genv.store_init_data_list_perm in PERM; eauto.
        erewrite <- Genv.store_zeros_perm in PERM; eauto.
        erewrite alloc_perm in PERM; eauto. destruct peq.
        subst. rewrite BLOCKEQ.
        rewrite BLOCKEQ in FINDSYM. apply Genv.find_invert_symbol in FINDSYM.
        unfold ge in FINDSYM. erewrite genv_invert_symbol_next in FINDSYM; eauto. inv FINDSYM.
        erewrite partial_genv_find_symbol_eq; eauto.
        exploit FINDVALIDSYM; eauto. intros FINDSYM'.
        apply find_symbol_inversion_1 in FINDSYM'. destruct FINDSYM' as [DEF' FINDSYM'].
        assert (i <> id).
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq; eauto.
        (* defs perm *)
        intros id odef b' delta IN FSYM ofs k p OFS.
        eapply Mem.perm_drop_3; eauto.
        destruct (eq_block b' (gen_segblocks tprog (fst slbl))); auto.
        right. right.
        destruct (vit_dec _ _ odef).
        exploit find_symbol_to_gmap; eauto. rewrite <- DEFSTAIL. rewrite in_app. right. simpl. auto.
        intros (slbl0 & GMAP' & BEQ & IEQ).
        assert (odef_size (Some (Gvar v)) + Ptrofs.unsigned (snd slbl) <= Ptrofs.unsigned (snd slbl0)) as SZBND.
        {
          eapply (make_maps_ofs_ordering prog (defs ++ (i, Some (Gvar v)) :: nil) gdefs
                                           i id (Some (Gvar v)) odef); eauto.
          rewrite in_app. right. apply in_eq.
          generalize (gen_segblocks_injective tprog). unfold injective_on_valid_segs.
          intros INJECTIVE. subst. eapply INJECTIVE; eauto.
          eapply gen_segblocks_in_valid; eauto.
          eapply update_map_gmap_range1; eauto.
        }
        subst. simpl in SZBND.
        exploit prog_odef_size_pos; eauto. intros. simpl in H. subst. omega.
        apply in_split in IN. destruct IN as (defs1 & gdefs1 & IN).
        erewrite find_symbol_nvi_eq with 
            (defs:=defs ++ (i, Some (Gvar v)) :: defs1)
            (gdefs:=gdefs1) in FSYM; eauto.
        inv FSYM.
        generalize (gen_segblocks_upper_bound tprog (fst slbl)). intros PLT.
        simpl in PLT.
        rewrite <- H1 in PLT.
        exfalso. eapply Plt_strict. eapply Plt_le_trans. apply PLT.
        apply pos_advance_N_ple. subst.
        rewrite <- DEFSTAIL. rewrite <- app_assoc. simpl. reflexivity.
        erewrite <- store_init_data_list_perm; eauto.
        erewrite <- Genv.store_zeros_perm; eauto.
        eapply DEFSPERM; eauto. apply in_cons; auto.

        (* Finish this case *)
        intros (m5' & ALLOCG' & MINJ_FINAL).
        exists m5'. split; auto. simpl.
        rewrite GMAP in ILBL. inv ILBL.
        unfold tge. 
        setoid_rewrite STOREZERO'.
        unfold tge in STOREINIT'. setoid_rewrite STOREINIT'.
        rewrite Z.add_comm.
        setoid_rewrite DROP'. 
        rewrite app_length in ALLOCG'. rewrite Nat.add_comm in ALLOCG'.
        simpl in ALLOCG'. auto.
        
    + (** the head of gdefs is None **)
        monadInv TRANSG.
        simpl in ALLOCG. destr_match_in ALLOCG; try now inversion ALLOCG.
        destruct (Mem.alloc m1 0 0) eqn:ALLOCF. inv EQ0.
        exploit Mem.alloc_result; eauto using ALLOCF. intros.
        simpl.

        (* globs_meminj *)
        assert (globs_meminj b = Some ((pos_advance_N b num_segments),0)) as BINJ.
        {
          unfold globs_meminj. subst b. rewrite BLOCKEQ.
          erewrite genv_invert_symbol_next; eauto.
          erewrite find_symbol_nvi_eq; eauto.
          rewrite partial_genv_next. f_equal. f_equal. 
          apply pos_advance_N_succ_commut.
        }
        
        (* alloc mapped injection *)
        exploit (Mem.alloc_left_mapped_weak_inject
                   globs_meminj (def_frame_inj m1) m1 m1' 0 0 m
                   b (pos_advance_N b num_segments) 0
                   BINJ MINJ ALLOCF); eauto.
        (* valid block *)
        red. rewrite BLOCKEQ'. subst b. rewrite BLOCKEQ.
        eapply partial_genv_genv_next_bound; eauto.
        (* valid offset *)
        generalize (instr_size_repr Pmovsb). omega.
        (* preservation of permission *)
        intros. omega.
        (* correct alignment *)
        simpl. red. intros. apply Z.divide_0_r.
        (* alloced memory has not been injected before *)
        simpl.
        intros b0 delta' ofs k p GINJ PERM' OFSABSURD.
        unfold globs_meminj in GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destruct p0. inv GINJ.
        (* assert (ofs + Ptrofs.unsigned i1 = 0) by omega. *)
        assert (i0 = i).
        {
          eapply Genv.invert_find_symbol in EQ0.
          generalize EQ0. intros FSYM.
          apply find_symbol_inversion_2 in EQ0. destruct EQ0 as (def1 & EQ0).
          generalize EQ0. intros IN.
          apply in_split in EQ0. destruct EQ0 as (defs1 & gdefs1 & EQ0).
          destruct (vit_dec _ _ def1).
          (* def1 is vit *)
          exploit find_symbol_to_gmap; eauto.
          intros (slbl & GMAP & BEQ & IEQ). 
          erewrite gmap_to_find_symbol in EQ1; eauto. inv EQ1.
          generalize (gen_segblocks_upper_bound tprog (fst slbl)). 
          intros PLT. erewrite BLOCKEQ in H0.
          erewrite partial_genv_next in H0. rewrite H0 in PLT.
          exfalso. eapply Plt_strict. simpl in PLT. eapply Plt_le_trans. apply PLT.
          assert (pos_advance_N 4 (length defs) = Pos.succ (Pos.succ (Pos.succ (Pos.of_succ_nat (length defs))))).
          replace (4%positive) with (Pos.of_succ_nat 3).
          rewrite pos_advance_N_succ_commut. simpl. auto. unfold Pos.of_succ_nat. simpl. auto.
          rewrite <- H. apply pos_advance_N_ple.
          (* def1 is not vit *)
          erewrite find_symbol_nvi_eq in EQ1; eauto. inv EQ1.
          rewrite BLOCKEQ in H0. rewrite partial_genv_next in H0.
          replace (4%positive) with (Pos.of_succ_nat 3) in H0.
          rewrite pos_advance_N_succ_commut in H0. simpl in H0. 
          repeat apply Pos.succ_inj in H0. apply SuccNat2Pos.inj in H0.
          rewrite <- DEFSTAIL in EQ0. symmetry in H0.
          assert ((i, None) = (i0, def1)).
          eapply app_same_len_prefix; eauto. inv H. auto.
          unfold Pos.of_succ_nat. simpl. auto.
        }
        subst i0. apply Genv.invert_find_symbol in EQ0.
        erewrite genv_find_symbol_next in EQ0; eauto. inv EQ0.
        apply Mem.perm_valid_block in PERM'. rewrite <- BLOCKEQ in PERM'.
        red in PERM'. eapply Plt_strict; eauto.

        (* stack frame is public *)
        intros fi INSTK o k pp PERM INJPERM.
        rewrite STK' in INSTK. inv INSTK.
        (* get the new weak injection *)
        intros MINJ'.
        erewrite alloc_pres_def_frame_inj in MINJ'; eauto.

        (* apply IH *)
        exploit (IHgdefs x (defs ++ (i, None) :: nil) m m2); eauto.
        rewrite <- DEFSTAIL. rewrite List.app_assoc_reverse. simpl. auto.

        (* next block *)
        erewrite Mem.nextblock_alloc; eauto.
        erewrite partial_genv_next_succ. f_equal. congruence.

        (* ofsbound *)
        intros id b0 def ofs k p FINDSYM IN PERM'.
        rewrite in_app in IN. destruct IN as [IN | IN].
        assert (i <> id).
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq in FINDSYM; eauto.
        assert (b <> b0).
        {
          unfold not. subst. rewrite BLOCKEQ. intros. subst.
          eapply Genv.find_symbol_genv_next_absurd; eauto.
        }
        exploit Mem.perm_alloc_inv; eauto using ALLOCF.
        rewrite dec_eq_false; auto. intros. eapply OFSBOUND; eauto.

        inv IN. inv H0.
        rewrite partial_genv_find_symbol_eq in FINDSYM. inv FINDSYM.
        rewrite <- BLOCKEQ in PERM'.
        exploit Mem.perm_alloc_inv; eauto using ALLOCF.
        rewrite dec_eq_true. intros.
        simpl. assert (ofs = 0). omega. subst.
        omega.

        inv H0.
        (* findvalidsym *)
        intros id b0 ofs k p FINDSYM PERM.
        erewrite alloc_perm in PERM; eauto. destruct peq.
        subst. rewrite BLOCKEQ.
        rewrite BLOCKEQ in FINDSYM. apply Genv.find_invert_symbol in FINDSYM.
        unfold ge in FINDSYM. erewrite genv_invert_symbol_next in FINDSYM; eauto. inv FINDSYM.
        erewrite partial_genv_find_symbol_eq; eauto.
        exploit FINDVALIDSYM; eauto. intros FINDSYM'.
        apply find_symbol_inversion_1 in FINDSYM'. destruct FINDSYM' as [DEF' FINDSYM'].
        assert (i <> id).
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq; eauto.
        (* defs perm *)
        intros id odef b' delta IN FSYM ofs k p OFS.
        eapply DEFSPERM; eauto. simpl. eauto.

        (* finish this case *)
        intros (m2' & STORE & WJ).
        exists m2'. split; auto.
        rewrite app_length in STORE. rewrite Nat.add_comm in STORE. simpl in STORE.
        auto.
Qed.



Lemma store_all_globals_inject :
  forall tgdefs m2 m1' gmap lmap dsize csize 
    (DEFNAMES: list_norepet (map fst (AST.prog_defs prog)))
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize))
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize = OK tprog)
    (TRANSG: transl_globdefs gmap (AST.prog_defs prog) = OK tgdefs)
    (BOUND: dsize + csize <= Ptrofs.max_unsigned)
    (MINJ: Mem.weak_inject globs_meminj (def_frame_inj Mem.empty) Mem.empty m1')
    (BLOCKEQ: Mem.nextblock m1' = (pos_advance_N init_block (length (list_of_segments tprog) + length (AST.prog_defs prog))))
    (STK: Mem.stack m1' = nil)
    (PERMOFS : forall b ofs k p, Mem.perm m1' b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned)
    (DEFSPERM: forall id odef b' delta,
       In (id, odef) (AST.prog_defs prog) ->
       Genv.find_symbol tge id = Some (b', delta) ->
       (forall ofs k p, 0 <= ofs < odef_size odef -> Mem.perm m1' b' ((Ptrofs.unsigned delta)+ofs) k p))
    (ALLOCG: Genv.alloc_globals ge Mem.empty (AST.prog_defs prog) = Some m2),
    exists m2',store_globals tge (gen_segblocks tprog) m1' tgdefs = Some m2'
           /\ Mem.inject globs_meminj (def_frame_inj m2) m2 m2'.
Proof.
  intros. exploit (store_globals_inject (AST.prog_defs prog) tgdefs nil); eauto.
  rewrite Mem.nextblock_empty; eauto.
  intros id b def ofs k p FINDSYM IN PERM. inv IN.
  intros id b ofs k p FINDSYM PERM.
  exploit Mem.perm_empty; eauto. contradiction.
  intros (m2' & ALLOCG' & WINJ). exists m2'. split; auto.
  eapply Mem.weak_inject_to_inject; eauto.
  intros. eapply globs_meminj_domain_valid; eauto.
Qed.

Lemma globs_meminj_ofs_pos : forall b b' delta,
    globs_meminj b = Some (b', delta) -> delta >= 0.
Proof.
  unfold globs_meminj. intros. destr_match_in H; inv H.
  destr_match_in H1; inv H1. destruct p. inv H0.
  generalize (Ptrofs.unsigned_range i0). omega.
Qed.

Lemma alloc_global_exists: forall I (def: (ident * option (@gdef I) * segblock)) m,
    exists m', alloc_global m def = Some m'.
Proof.
  intros. destruct def. destruct p. destruct o. destruct g. destruct f.
  - simpl. destruct (Mem.alloc m 0 1) eqn:ALLOC. eauto.
  - simpl. destruct (Mem.alloc m 0 1) eqn:ALLOC. eauto.
  - simpl. destruct (Mem.alloc m 0 0) eqn:ALLOC. eauto.
  - simpl. destruct (Mem.alloc m 0 0) eqn:ALLOC. eauto.
Qed.

Lemma alloc_globals_exists: forall I (defs: list (ident * option (@gdef I) * segblock)) m,
    exists m', alloc_globals m defs = Some m'.
Proof.
  induction defs; intros.
  - simpl. eauto.
  - simpl. generalize (alloc_global_exists _ a m); eauto.
    intros (m' & ALLOC).  rewrite ALLOC. 
    eapply IHdefs; eauto.
Qed.


Lemma alloc_globals_segments_weak_inject: forall gmap lmap dsize csize m
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize))
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize = OK tprog)
    (NEXTBLOCK: Mem.nextblock m = init_block)
    (STACK: Mem.stack m = nil),
    exists m', 
      alloc_globals (alloc_segments m (list_of_segments tprog)) (prog_defs tprog) = Some m'
      /\ Mem.weak_inject globs_meminj (def_frame_inj Mem.empty) Mem.empty m'.
Proof.
  intros. unfold def_frame_inj. erewrite Mem.empty_stack; eauto. 
  generalize (alloc_globals_exists Asm.instruction
                                    (prog_defs tprog)
                                    (alloc_segments m (list_of_segments tprog))).
  intros (m' & ALLOC). exists m'. split. auto.
  eapply Mem.empty_weak_inject; eauto.
  - etransitivity. 
    erewrite <- (alloc_globals_stack (prog_defs tprog) (alloc_segments m (list_of_segments tprog))); eauto.
    erewrite alloc_segments_stack; eauto.
  - intros b b' delta H. eapply globs_meminj_ofs_pos; eauto.
  - intros b b' delta H. unfold globs_meminj in H.
    destr_match_in H; inv H.
    destr_match_in H1; inv H1. 
    destruct p. inv H0.
    apply Genv.invert_find_symbol in EQ.
    exploit (find_symbol_inversion_2 prog); eauto.
    intros (def & IN).
    red.
    erewrite alloc_globals_nextblock; eauto.
    erewrite alloc_segments_nextblock; eauto.
    simpl. erewrite NEXTBLOCK. simpl.
    destruct (vit_dec _ _ def).
    + exploit find_symbol_to_gmap; eauto.
      intros (slbl & GMAP & BEQ & IEQ). subst.
      eapply Plt_le_trans.
      apply gen_segblocks_upper_bound. simpl.
      apply pos_advance_N_ple.
    + apply in_split in IN. destruct IN as (defs & gdefs & DEFS).
      erewrite transl_prog_pres_len; eauto.
      erewrite find_symbol_nvi_eq in EQ0; eauto.
      inv EQ0. rewrite DEFS. rewrite app_length.
      simpl. apply pos_advance_N_plt_add.
      generalize TRANSF. intros TRANSF'.
      unfold match_prog, transf_program in TRANSF'.
      repeat destr_in TRANSF'. destruct w. auto.
Qed.


Definition find_segsize (segs: list segment) id : option ptrofs :=
  match (List.find (fun s => ident_eq (segid s) id) segs) with
  | None => None
  | Some s => Some (segsize s)
  end.

Definition gen_segs dsize csize : list segment :=
  (mkSegment data_segid (Ptrofs.repr dsize))
    :: (mkSegment code_segid (Ptrofs.repr csize))
    :: nil.

Lemma update_maps_gmap_ofs_le_segsize :
  forall defs (gmap : GID_MAP_TYPE) (lmap : LABEL_MAP_TYPE) (dsize csize : Z) (id : ident)
    def slbl
    gmap1 lmap1 dsize1 csize1 
    (DZLBND: dsize1 >= 0)
    (DZUBND: dsize <= Ptrofs.max_unsigned)
    (CZALNG: (alignw | csize1))
    (CZLBND: csize1 >= 0)
    (CZUBND: csize <= Ptrofs.max_unsigned)
    (UPDATE: update_maps gmap1 lmap1 dsize1 csize1 defs = (gmap, lmap, dsize, csize))
    (NORPT: list_norepet (map fst defs))
    (VI: sdef_is_var_or_internal_fun (Some def))
    (IN: In (id, Some def) defs)
    (GMAP: gmap id = Some slbl),
    exists sz, find_segsize (gen_segs dsize csize) (fst slbl) = Some sz /\
          (Ptrofs.unsigned (snd slbl)) + (def_size def) <= Ptrofs.unsigned sz.
Proof.
  induction defs. intros.
  - inv IN.
  - intros.
    assert (dsize1 <= dsize) as DSZLE. eapply dsize_mono; eauto.
    assert (csize1 <= csize) as CSZLE. eapply csize_mono; eauto.
    inv IN.
    + destruct def. destruct f.
      * unfold update_maps in UPDATE. simpl in UPDATE.
        destruct (update_instrs lmap1 csize1 id (Asm.fn_code f)) eqn:UPDINSTRS.
        exploit update_instrs_code_size; eauto. intros. subst. simpl.
        inv NORPT. exploit update_gmap_not_in; eauto.
        intros GMAP'. rewrite GMAP in GMAP'.
        unfold update_gid_map in GMAP'. rewrite peq_true in GMAP'. inv GMAP'.
        unfold code_label. simpl.
        exists (Ptrofs.repr csize). split; auto.
        repeat rewrite Ptrofs.unsigned_repr.
        apply Zle_trans with (align (csize1 + code_size (Asm.fn_code f)) alignw).
        apply alignw_le. eapply csize_mono; eauto. apply alignw_divides.
        split; auto. omega. omega.
      * inv VI.
      * unfold update_maps in UPDATE. simpl in UPDATE.
        simpl.
        inv NORPT. exploit update_gmap_not_in; eauto.
        intros GMAP'. rewrite GMAP in GMAP'.
        unfold update_gid_map in GMAP'. rewrite peq_true in GMAP'. inv GMAP'.
        unfold data_label. simpl.
        exists (Ptrofs.repr dsize). split; auto.
        repeat rewrite Ptrofs.unsigned_repr.
        apply Zle_trans with (dsize1 + align (init_data_list_size (gvar_init v)) alignw).
        generalize (alignw_le (init_data_list_size (gvar_init v))). omega.
        eapply dsize_mono; eauto. omega. omega.
    + inv NORPT. unfold update_maps in UPDATE. simpl in UPDATE.
      destruct a.
      destruct (update_maps_def gmap1 lmap1 dsize1 csize1 i o) eqn:UPDDEF.
      destruct p. destruct p. 
      eapply (IHdefs _ _ _ _ id def slbl g l z0 z); eauto.
      assert (dsize1 <= z0). eapply update_dsize_mono; eauto. omega.
      eapply update_csize_div; eauto.
      assert (csize1 <= z). eapply update_csize_mono; eauto. omega.
Qed.

Lemma transl_prog_segs : forall gmap lmap prog dsize csize tprog,
    transl_prog_with_map gmap lmap prog dsize csize = OK tprog ->
    list_of_segments tprog = gen_segs dsize csize.
Proof.
  intros. monadInv H. unfold list_of_segments.
  simpl. unfold gen_segs. auto.
Qed.
 
Lemma make_maps_gmap_ofs_le_segsize :
  forall (gmap : GID_MAP_TYPE) (lmap : LABEL_MAP_TYPE) (dsize csize : Z) (id : ident)
    def slbl
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize))
    (VI: sdef_is_var_or_internal_fun (Some def))
    (IN: In (id, Some def) (AST.prog_defs prog))
    (GMAP: gmap id = Some slbl),
    exists sz, find_segsize (list_of_segments tprog) (fst slbl) = Some sz /\
          (Ptrofs.unsigned (snd slbl)) + (def_size def) <= Ptrofs.unsigned sz.
Proof.
intros.
  generalize TRANSF. intros TRANSF'.
  unfold match_prog, transf_program in TRANSF'.
  repeat destr_in TRANSF'.
  inv UPDATE.
  unfold make_maps in Heqp.
  assert (0 <= dsize). eapply dsize_mono; eauto.
  assert (0 <= csize). eapply csize_mono; eauto. apply Z.divide_0_r.
  erewrite transl_prog_segs; eauto.
  eapply update_maps_gmap_ofs_le_segsize; eauto; try omega.
  apply Z.divide_0_r.
  destruct w. auto.
Qed.

Lemma alloc_segments_pres_perm: forall segs m b m' ofs k p
  (ALLOCSEGS: m' = alloc_segments m segs)
  (PERM: Mem.perm m b ofs k p),
  Mem.perm m' b ofs k p.
Proof.
  induction segs; intros.
  - inv ALLOCSEGS. simpl. auto.
  - inv ALLOCSEGS. simpl.
    destruct (Mem.alloc m 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    eapply IHsegs; eauto.
    eapply Mem.perm_alloc_1; eauto.
Qed.
      
Lemma alloc_segments_acc_segblocks_perm : forall segs m m' sid sz k p ofs smap
    (ALLOCSEGS: m' = alloc_segments m segs)
    (FINDSZ: find_segsize segs sid = Some sz)
    (SMAP: smap = acc_segblocks (Mem.nextblock m) (map segid segs) (fun id => undef_seg_block))
    (OFSBND: 0 <= ofs < Ptrofs.unsigned sz),
    Mem.perm m' (smap sid) ofs k p.
Proof.
  induction segs; intros.
  - inv FINDSZ.
  - simpl in ALLOCSEGS.
    destruct (Mem.alloc m 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    rewrite map_cons in SMAP. simpl in SMAP. subst.
    destruct ident_eq.
    + unfold find_segsize in FINDSZ.
      simpl in FINDSZ.  subst. setoid_rewrite peq_true in FINDSZ.
      inv FINDSZ. exploit Mem.nextblock_alloc; eauto. intros NB.
      exploit Mem.alloc_result; eauto. intros. subst.
      eapply alloc_segments_pres_perm; eauto.
      apply Mem.perm_implies with (p1:=Freeable); auto.
      eapply Mem.perm_alloc_2; eauto.
      constructor.
    + unfold find_segsize in FINDSZ.
      simpl in FINDSZ.  setoid_rewrite peq_false in FINDSZ; auto.
      eapply IHsegs; eauto.
      erewrite <- Mem.nextblock_alloc; eauto.
Qed.

Lemma alloc_segments_init_perm : 
  forall id odef b' delta ofs k p m
    (IN: In (id, odef) (AST.prog_defs prog))
    (VI: sdef_is_var_or_internal_fun odef)
    (FSYM: Genv.find_symbol tge id = Some (b', delta))
    (NB: Mem.nextblock m = init_block)
    (OFS: 0 <= ofs < odef_size odef),
    Mem.perm (alloc_segments m (list_of_segments tprog)) b' ((Ptrofs.unsigned delta)+ofs) k p.
Proof.
  intros. destruct odef as [|def].
  - generalize TRANSF. intros TRANSF'. unfold match_prog in TRANSF'.
    unfold transf_program in TRANSF'.
    destruct (check_wellformedness prog) eqn:WF; try congruence. repeat destr_in TRANSF'.
    exploit find_symbol_to_gmap; eauto.
    intros (slbl & GID & BEQ & DELTA). subst.
    exploit make_maps_gmap_ofs_le_segsize; eauto.
    intros (sz & FINDSEGSZ & BND). simpl in OFS.
    eapply alloc_segments_acc_segblocks_perm; eauto.
    unfold gen_segblocks. rewrite NB. reflexivity.
    generalize (Ptrofs.unsigned_range_2 (snd slbl)); eauto. intros.
    omega.
  - simpl in OFS. omega.
Qed.

Definition odef_size' {I:Type} (def: (ident * option (@gdef I) * segblock)) : Z :=
  let '(id, def', sb) := def in
  match def' with 
  | None => 0
  | Some (Gfun (External f)) => 1
  | Some _ => Ptrofs.unsigned (segblock_size sb)
  end.

Lemma alloc_globals_ne_perm : 
  forall (I:Type) defs def' n m m' ofs k p
    (NE: def_is_none_or_external_fun def')
    (NTH: Nth n defs def')
    (ALLOC: alloc_globals m defs = Some m')
    (OFS: 0 <= ofs < @odef_size' I def'),
    Mem.perm m' (pos_advance_N (Mem.nextblock m) n) ofs k p.
Proof.
  induction defs; intros; simpl in *. inv NTH.
  destr_in ALLOC; inv ALLOC. 
  destruct def'. destruct p0. 
  inv NTH.
  - red in NE. destruct NE.
    + subst. simpl in OFS. omega.
    + destruct H. subst. 
      simpl in *.
      destruct (Mem.alloc m 0 1) eqn: ALLOC. inv Heqo.
      eapply alloc_globals_pres_perm; eauto.
      erewrite <- Mem.alloc_result; eauto.
      erewrite alloc_perm; eauto.
      rewrite peq_true. omega.
  - exploit IHdefs; eauto.
    cut (Mem.nextblock m0 = Psucc (Mem.nextblock m)).
    intros NB PM. rewrite NB in PM.
    simpl. eauto.
    erewrite alloc_global_nextblock; eauto.
Qed.


Lemma transl_prog_pres_odef_size : 
  forall odef g id odef'
    (TL: transl_globdef g id odef = OK odef')
    (BND: odef_size odef <= Ptrofs.max_unsigned),
    odef_size odef = odef_size' odef'.
Proof.
  intros. 
  generalize (odef_size_pos odef). intros.
  destruct odef. destruct g0. destruct f.
  - monadInv TL. simpl. monadInvX EQ.
    destr_in EQ3; inv EQ3. simpl.
    rewrite Ptrofs.unsigned_repr. eauto.
    simpl in *. omega.
  - monadInv TL. simpl. auto.
  - monadInvX TL. simpl.
    rewrite Ptrofs.unsigned_repr. eauto.
    simpl in *. omega.
  - monadInv TL. simpl. omega.
Qed.
    

Lemma transl_prog_pres_nvi'' : 
  forall odef g id def' sb
    (NVI: ~sdef_is_var_or_internal_fun odef)
    (TL: transl_globdef g id odef = OK (id, def', sb)),
    def_is_none_or_external_fun (id, def', sb).
Proof.
  intros. destruct odef. destruct g0. destruct f.
  - exfalso. apply NVI. red. auto.
  - monadInv TL. red. eauto.
  - exfalso. apply NVI. red. auto.
  - monadInv TL. simpl. eauto.
Qed.

Lemma size_gvar_pos: 
  forall v, 0 <= size_gvar v.
Proof.
  intros. unfold size_gvar. repeat destr; try omega. subst.
  generalize (init_data_list_size_pos (gvar_init v0)); omega.
Qed.

Lemma size_gvar_bound : 
  forall defs id v
    (IN: In (id, Some (Gvar v)) defs),
    size_gvar (Some (Gvar v)) <= sizes_gvars (defs).
Proof.
  induction defs; intros; simpl in *. contradiction.
  inv IN.
  - simpl. 
    unfold sizes_gvars. unfold sum.
    rewrite fold_left_plus. simpl. unfold sum. simpl.
    rewrite fold_left_plus.
    match goal with
    | [ |- ?a <= ?b + ?s] =>
      cut (0 <= s)
    end.
    intros. 
    generalize (alignw_le (init_data_list_size (gvar_init v))).
    intros.
    omega.
    apply sum_pos. intros.
    transitivity (size_gvar (snd x)). apply size_gvar_pos.
    apply alignw_le.
  - etransitivity.
    eapply IHdefs; eauto. unfold sizes_gvars. 
    unfold sum. simpl. rewrite fold_left_plus with (d := (align (size_gvar (snd a)) alignw)).
    generalize (alignw_le (size_gvar (snd a))). 
    generalize (size_gvar_pos (snd a)).
    unfold sum. omega.
Qed.

Lemma odef_size_bound : 
  forall g l dz cz id odef
    (MP: make_maps prog = (g, l, dz, cz))
    (BND: dz + cz <= Ptrofs.max_unsigned)
    (IN: In (id, odef) (AST.prog_defs prog)),
    odef_size odef <= Ptrofs.max_unsigned.
Proof.
  intros.
  exploit make_maps_sizes_pos; eauto.
  intros (DZ & CZ).
  assert (0 <= dz) by omega.
  assert (0 <= cz) by omega.
  unfold make_maps in MP.
  destruct odef. destruct g0. destruct f. 
  - simpl. 
    assert (code_size (Asm.fn_code f) <= cz).
    eapply code_size_upper_bound' with (csize1:=0); eauto. 
    omega. omega.
  - simpl.
    apply one_le_ptrofs_max_unsigned.
  - simpl.
    exploit updates_dsize; eauto. simpl. intros.    
    assert (size_gvar (Some (Gvar v)) <= sizes_gvars (AST.prog_defs prog)).
    eapply size_gvar_bound; eauto.
    simpl in H2. omega.
  - simpl. omega.
Qed.

Lemma alloc_globals_init_perm : 
  forall id odef b' delta ofs k p m m'
    (IN: In (id, odef) (AST.prog_defs prog))
    (NVI: ~ sdef_is_var_or_internal_fun odef)
    (FSYM: Genv.find_symbol tge id = Some (b', delta))
    (OFS: 0 <= ofs < odef_size odef)
    (NB: Mem.nextblock m = Pos.of_succ_nat num_segments)
    (GALLOC: alloc_globals m (prog_defs tprog) = Some m'),
    Mem.perm m' b' ((Ptrofs.unsigned delta)+ofs) k p.
Proof.
  intros. unfold tge, globalenv in FSYM.
  generalize TRANSF. intros TRANSF'. unfold match_prog in TRANSF'.
  unfold transf_program in TRANSF'.
  destruct (check_wellformedness prog) eqn:WF; try congruence. repeat destr_in TRANSF'.
  exploit transl_prog_pres_def; eauto.
  intros (def' & sb & IN' & TLDEF).
  destruct w.
  exploit transl_prog_list_norepet; eauto. intros NPT.
  apply In_Nth in IN'. destruct IN' as (n & nLE & IN').
  exploit transl_prog_pres_nvi''; eauto. intros NE.
  erewrite add_globals_find_symbol_ne in FSYM; eauto. inv FSYM.
  rewrite Ptrofs.unsigned_zero. simpl.
  erewrite transl_prog_pres_odef_size in OFS; eauto.
  simpl in NB. rewrite <- NB.
  eapply alloc_globals_ne_perm; eauto.
  eapply odef_size_bound; eauto.
Qed.
    

Lemma init_mem_pres_inject : forall m gmap lmap dsize csize 
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize))
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize = OK tprog)
    (INITMEM: Genv.init_mem prog = Some m),
    exists m', init_mem tprog = Some m' /\ Mem.inject globs_meminj (def_frame_inj m) m m'.
Proof.
  unfold Genv.init_mem, init_mem. intros.
  destruct (Mem.alloc Mem.empty 0 0) eqn:IALLOC.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  rewrite Mem.nextblock_empty in NEXTBLOCK. simpl in NEXTBLOCK.
  exploit alloc_globals_segments_weak_inject; eauto.
  erewrite Mem.alloc_stack_blocks; eauto.
  erewrite Mem.empty_stack; eauto.
  intros (m' & GALLOC & SINJ).
  set (m1 := alloc_segments m0 (list_of_segments tprog)) in *.
  rewrite GALLOC.
  generalize (store_all_globals_inject). intro AAGI.
  generalize TRANSF. intros TRANSF'. unfold match_prog in TRANSF'.
  unfold transf_program in TRANSF'.
  destruct (check_wellformedness prog) eqn:WF; try congruence. repeat destr_in TRANSF'.
  unfold transl_prog_with_map in H0. 
  destruct (transl_globdefs g (AST.prog_defs prog)) eqn: TLGLB; inversion H0. 
  clear H0. simpl.
  inversion UPDATE. subst g l z0 z.
  exploit AAGI; eauto using INITMEM, SINJ, Mem.inject_ext.
  - inv w. auto.
  - erewrite alloc_globals_nextblock; eauto.
    subst m1.
    erewrite alloc_segments_nextblock; eauto.
    erewrite Mem.nextblock_alloc; eauto. 
    erewrite Mem.nextblock_empty. simpl.    
    subst tprog. simpl.
    erewrite transl_globdefs_pres_len; eauto.
  - erewrite <- alloc_globals_stack; eauto.
    subst m1. erewrite alloc_segments_stack; eauto.
    erewrite Mem.alloc_stack_blocks; eauto.
    erewrite Mem.empty_stack; eauto.
  - eapply alloc_globals_perm_ofs; eauto. subst m1.
    eapply alloc_segments_perm_ofs; eauto. 
    intros b0 ofs k p PERM. erewrite alloc_perm in PERM; eauto.
    destruct peq. omega. apply Mem.perm_empty in PERM. contradiction.
  - intros id odef b' delta IN FSYM ofs k p OFS.
    destruct (vit_dec _ _ odef).
    + eapply alloc_globals_pres_perm; eauto.
      subst m1. eapply alloc_segments_init_perm; eauto.
    + eapply alloc_globals_init_perm; eauto.
      subst m1. erewrite alloc_segments_nextblock; eauto. simpl.
      rewrite NEXTBLOCK. auto.
  - intros (m1' & ALLOC' & MINJ).
    exists m1'. split. subst. simpl.
    unfold tge in ALLOC'. auto.
    auto.
Qed.


Lemma push_new_stage_def_frame_inj : forall m,
    def_frame_inj (Mem.push_new_stage m) = (1%nat :: def_frame_inj m).
Proof.
  unfold def_frame_inj. intros.
  erewrite Mem.push_new_stage_stack. simpl. auto.
Qed.

Definition find_symbol_block_bound (ge:FlatAsm.genv) :=
  forall id b ofs, Genv.find_symbol ge id = Some (b, ofs) -> Pos.lt b (Genv.genv_next ge).

Lemma add_global_pres_find_symbol_block_bound: forall ge def,
  find_symbol_block_bound ge -> find_symbol_block_bound (add_global ge def).
Proof.
  unfold find_symbol_block_bound. intros.
  unfold add_global in *. destruct def. destruct p. simpl in *.
  destruct o. destruct g. destruct f.
  - apply Pos.lt_lt_succ. eapply H; eauto.
  - destruct ident_eq. 
    + subst. inv H0. apply Pos.lt_succ_diag_r.
    + apply Pos.lt_lt_succ. eapply H; eauto.
  - apply Pos.lt_lt_succ. eapply H; eauto.
  - destruct ident_eq. 
    + subst. inv H0. apply Pos.lt_succ_diag_r.
    + apply Pos.lt_lt_succ. eapply H; eauto.
Qed.

Lemma add_globals_pres_find_symbol_block_bound: forall defs ge,
  find_symbol_block_bound ge -> find_symbol_block_bound (add_globals ge defs).
Proof.
  induction defs; intros; simpl.
  - auto.
  - apply IHdefs. apply add_global_pres_find_symbol_block_bound. auto.
Qed.


Lemma find_symbol_globenv_block_bound :
  forall (id : ident) b ofs, Genv.find_symbol (globalenv tprog) id = Some (b, ofs) 
                        -> Pos.lt b (Genv.genv_next (globalenv tprog)).
Proof.
  unfold globalenv. simpl. intros.
  exploit add_globals_pres_find_symbol_block_bound; eauto. 
  red. simpl. intros.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  repeat destr_in TRANSF.
  clear H. monadInv H2; simpl in H0.
  unfold gidmap_to_symbmap in H0. 
  destr_match_in H0; inv H0. destruct s.
  inv H1. 
  exploit update_map_gmap_range; eauto. simpl.
  intros.
  apply gen_segblocks_upper_bound.
Qed.

Lemma init_meminj_genv_next_inv : forall b delta
    (MINJ: init_meminj b = Some (Genv.genv_next tge, delta)),
    b = Globalenvs.Genv.genv_next ge.
Proof.
  intros.
  unfold init_meminj in MINJ. destruct eq_block; inv MINJ.
  - unfold ge. auto.
  - destr_match_in H0; inv H0.
    destr_match_in H1; inv H1.
    destruct p. inv H0.
    exploit find_symbol_globenv_block_bound; eauto. 
    intros.
    exfalso. generalize H.
    setoid_rewrite <- Pos.compare_nlt_iff.
    apply Pos.lt_irrefl.
Qed.



(* Lemma genv_segblocks_add_globals: *)
(*   forall l g, *)
(*     Genv.genv_segblocks (add_globals g l) = Genv.genv_segblocks g. *)
(* Proof. *)
(*   induction l; simpl; intros; auto. *)
(*   rewrite IHl. unfold add_global.  *)
(*   destruct a, p, o; auto. *)
(*   destruct g0; auto. *)
(* Qed. *)


Lemma update_map_funct':
  forall gmap lmap dsize csize f i s,
    make_maps prog = (gmap, lmap, dsize, csize) ->
    list_norepet (map fst (AST.prog_defs prog)) ->
    In (i, Some (Gfun (Internal f))) (AST.prog_defs prog) ->
    gmap i = Some s ->
    fst s = code_segid.
Proof.
  unfold make_maps. intros gmap lmap dsize csize f i s UM LNR IN GM.

  eapply (umind _ _ _ _ _ _ _ _ _ UM (fun g l d c => forall s, g i = Some s -> In (i, Some (Gfun (Internal f))) (AST.prog_defs prog) -> fst s = code_segid)).
  inversion 1.
  - intros.
    erewrite update_gmap in H2. 2: eauto.
    destr_in H2; eauto.
    subst.
    exploit @norepet_unique. apply LNR. apply H3. apply H1. reflexivity. intro A; inv A. inv H2.
    reflexivity.
  - auto.
  - auto.
Qed.

Lemma update_map_funct:
  forall gmap lmap dsize csize b f i s,
    make_maps prog = (gmap, lmap, dsize, csize) ->
    list_norepet (map fst (AST.prog_defs prog)) ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Genv.invert_symbol ge b = Some i ->
    gmap i = Some s ->
    fst s = code_segid.
Proof.
  unfold make_maps. intros gmap lmap dsize csize b f i s UM LNR FFP IVS GM.
  exploit @Genv.find_symbol_funct_ptr_inversion. reflexivity.
  apply Genv.invert_find_symbol. unfold ge in IVS. apply IVS.
  eauto.
  intros; eapply update_map_funct'; eauto.
Qed.


Lemma gen_segblocks_code_map : forall g l p dz cz p'
                                 (TL: transl_prog_with_map g l p dz cz = OK p'),
    gen_segblocks p' code_segid = code_block.
Proof.
  intros. monadInv TL. unfold gen_segblocks.
  simpl. auto.
Qed.

Lemma gidmap_symbmap_internal_block:
  forall gmap lmap dsize csize b b' f i ofs,
    make_maps prog = (gmap, lmap, dsize, csize) ->
    transl_prog_with_map gmap lmap prog dsize csize = OK tprog ->
    list_norepet (map fst (AST.prog_defs prog)) ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Genv.invert_symbol ge b = Some i ->
    gidmap_to_symbmap (gen_segblocks tprog) (glob_map tprog) i = Some (b',ofs) ->
    b' = code_block.
Proof.
  intros. 
  exploit transl_prog_gmap; eauto. intros. subst.
  unfold gidmap_to_symbmap in H4. destr_match_in H4; inv H4.
  destruct s. inv H6.
  exploit update_map_funct; eauto. simpl. intros. subst.
  eapply gen_segblocks_code_map; eauto.
Qed.


Lemma find_symbol_internal_block:
  forall gmap lmap dsize csize b b' f i ofs
    (MK: make_maps prog = (gmap, lmap, dsize, csize))
    (TL: transl_prog_with_map gmap lmap prog dsize csize = OK tprog)
    (NPT: list_norepet (map fst (AST.prog_defs prog)))
    (FPTR: Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f))
    (INVS: Globalenvs.Genv.invert_symbol ge b = Some i)
    (FSYM: Genv.find_symbol tge i = Some (b',ofs)),
    b' = code_block.
Proof.
  intros. apply Genv.invert_find_symbol in INVS.
  unfold ge in *. exploit Genv.find_symbol_funct_ptr_inversion; eauto.
  intros INS.
  exploit transl_prog_list_norepet; eauto. intros NPT'.
  exploit transl_prog_pres_def; eauto. 
  intros (def' & sb & IN' & TLGF).
  monadInv TLGF.
  unfold tge, globalenv in FSYM. 
  assert (defs_is_var_or_internal_fun i (prog_defs tprog)).
  eapply unique_def_is_internal_fun; eauto.
  erewrite add_globals_pres_find_symbol in FSYM; eauto. simpl in FSYM.
  eapply gidmap_symbmap_internal_block; eauto.
  apply Genv.find_invert_symbol. auto.
Qed.

Lemma valid_instr_offset_is_internal_init:
  list_norepet (map fst (AST.prog_defs prog)) ->
  valid_instr_offset_is_internal init_meminj.
Proof.
  intro NRP.
  red.
  intros b b' f ofs i ofs' FFP FI INJ.
  unfold Genv.genv_internal_codeblock. 
  destruct tge eqn:TGE.
  unfold tge in TGE. unfold globalenv in TGE.
  exploit (fun ge ge' => add_globals_pres_internal_block (prog_defs tprog) ge ge' b'); eauto. 
  simpl. intros. rewrite H. clear TGE H.
  assert (match_prog prog tprog) as TRANSF' by auto.
  unfold match_prog in TRANSF'. unfold transf_program in TRANSF'.
  repeat destr_in TRANSF'.
  unfold gen_internal_codeblock.
  erewrite transl_prog_seg_code; eauto.
  erewrite gen_segblocks_code_map; eauto.
  unfold init_meminj in INJ. destr_in INJ.
  exfalso. subst. unfold ge in FFP. 
  exploit Globalenvs.Genv.genv_next_find_funct_ptr_absurd; eauto.
  destr_in INJ; inv INJ.
  destr_in H1; inv H1. destruct p. inv H2.
  fold tge in Heqo0.
  assert (b' = code_block).
  eapply find_symbol_internal_block; eauto. subst. auto.
Qed.

Fixpoint filter_map {A B: Type} (f: A -> option B) (l: list A): list B :=
  match l with
    nil => nil
  | a::r => match f a with
             Some b => b :: filter_map f r
           | None => filter_map f r
           end
  end.

Lemma in_filter_map_iff {A B} (f: A -> option B) : forall l x,
    In x (filter_map f l) <-> (exists y, f y = Some x /\ In y l).
Proof.
  induction l; simpl; intros.
  split. easy. intros (y & EQ & F); auto.
  destr. simpl. rewrite IHl.
  split.
  intros [EQ | (y & EQ & INy)]; subst; eauto.
  intros (y & EQ & [EQ1 | IN]); subst; eauto. left; congruence.
  rewrite IHl.
  split.
  intros (y & EQ & INy); subst; eauto.
  intros (y & EQ & [EQ1 | IN]); subst; eauto. congruence.
Qed.

Lemma filter_map_ext:
  forall {A B} (f g: A -> option B) (EXT: forall x, f x = g x) l,
    filter_map f l = filter_map g l.
Proof.
  induction l; simpl; intros; eauto.
  rewrite EXT. destr.
Qed.

Lemma list_norepet_filter_map:
  forall {A B} (f: A -> option B) a l,
    list_norepet (filter_map f (a::l)) ->
    list_norepet (filter_map f l).
Proof.
  simpl; intros.
  destr_in H; inv H; auto.
Qed.      


Lemma external_in_defs_inversion : forall defs f sb i (ge:FlatAsm.genv)
  (NPT: list_norepet (map (fun '(i, _, _) => i) defs))
  (IN: In (i, Some (Gfun (External f)), sb) defs),
  exists b o,
    Genv.find_symbol (add_globals ge defs) i = Some (b, o) /\
    Genv.find_def (add_globals ge defs) b o = Some (Gfun (External f)).
Proof.
  induction defs; simpl; intros.
  - contradiction.
  - destruct a. destruct p. destruct IN.
    + inv H. inv NPT.
      eexists. eexists. split.
      erewrite add_globals_pres_find_symbol_not_in; eauto.
      simpl. rewrite peq_true. eauto.
      erewrite add_globals_pres_find_def; eauto.
      simpl. rewrite Ptrofs.eq_true. 
      destruct peq. simpl. auto. contradiction.
      simpl. apply Pos.lt_succ_diag_r.
    + eapply IHdefs; eauto. inv NPT. auto.
Qed.
      

Lemma external_in_prog_defs_inversion : forall f sb i
  (NPT: list_norepet (map (fun '(i, _, _) => i) (prog_defs tprog)))
  (IN: In (i, Some (Gfun (External f)), sb) (prog_defs tprog)),
  exists b o,
    Genv.find_symbol (globalenv tprog) i = Some (b, o) /\
    Genv.find_def (globalenv tprog) b o = Some (Gfun (External f)).
Proof.
  unfold globalenv. intros.
  eapply external_in_defs_inversion; eauto.
Qed.
  

Lemma external_find_symbol_det : forall defs (ge:FlatAsm.genv) i b1 b2 o1 o2 f sb
  (IN: In (i, Some (Gfun (External f)), sb) defs)
  (NPT: list_norepet (map (fun '(i, _, _) => i) defs))
  (FINSYM1: Genv.find_symbol (add_globals ge defs) i = Some (b1, o1))
  (FINSYM2: Genv.find_symbol (add_globals ge defs) i = Some (b2, o2)),
  b1 = b2 /\ o1 = o2.
Proof.
  induction defs; simpl; intros. contradiction. 
  destruct IN. 
  - subst. inv NPT.
    erewrite add_globals_pres_find_symbol_not_in in FINSYM1; eauto.
    erewrite add_globals_pres_find_symbol_not_in in FINSYM2; eauto.
    simpl in FINSYM1. rewrite peq_true in FINSYM1. inv FINSYM1.
    simpl in FINSYM2. rewrite peq_true in FINSYM2. inv FINSYM2.
    auto.
  - destruct a. destruct p. inv NPT.
    eapply IHdefs; eauto.
Qed.


Lemma external_find_symbol_det' : forall i b1 b2 o1 o2 f sb
  (IN: In (i, Some (Gfun (External f)), sb) (prog_defs tprog))
  (NPT: list_norepet (map (fun '(i, _, _) => i) (prog_defs tprog)))
  (FINSYM1: Genv.find_symbol (globalenv tprog) i = Some (b1, o1))
  (FINSYM2: Genv.find_symbol (globalenv tprog) i = Some (b2, o2)),
  b1 = b2 /\ o1 = o2.
Proof.
  unfold globalenv. intros.
  eapply external_find_symbol_det; eauto.
Qed.

Lemma extfun_transf:
  forall gmap lmap dsize csize 
    (* wf_prog prog -> *)
    (TL: transl_prog_with_map gmap lmap prog dsize csize = OK tprog)
    (* make_maps prog = (gmap, lmap, dsize, csize) -> *)
    (* dsize + csize <= Ptrofs.max_unsigned -> *)
    (NPT: list_norepet (map fst (AST.prog_defs prog))),
    forall b b' f ofs
      (FFP : Globalenvs.Genv.find_funct_ptr ge b = Some (External f))
      (JB: init_meminj b = Some (b', ofs)),
      Genv.find_funct tge (Vptr b' (Ptrofs.repr ofs)) = Some (External f).
Proof.
  intros.
  unfold init_meminj in JB. destr_in JB.
  - inv JB. unfold ge in FFP.
    exploit Genv.genv_next_find_funct_ptr_absurd; eauto. contradiction.
  - destr_in JB; inv JB. destr_in H0; inv H0.
    destruct p. inv H1.
    apply Genv.invert_find_symbol in Heqo.
    exploit Genv.find_symbol_funct_ptr_inversion; eauto. intros IN.
    exploit transl_prog_list_norepet; eauto. intros NPT'.
    exploit transl_prog_pres_def; eauto.
    intros (def' & sb & IN' & TLDEF).
    monadInv TLDEF.    
    unfold tge. rewrite Ptrofs.repr_unsigned.
    exploit (external_in_prog_defs_inversion f); eauto.
    intros (b1 & o1 & FSYM & FDEF).
    assert (b1 = b' /\ o1 = i0). eapply external_find_symbol_det'; eauto. 
    destruct H. subst. 
    unfold Genv.find_funct. unfold Genv.find_funct_ptr.
    rewrite FDEF. auto.
Qed.

(* Lemma extfun_transf: *)
(*   forall gmap lmap dsize csize j, *)
(*     wf_prog prog -> *)
(*     transl_prog_with_map gmap lmap prog dsize csize = OK tprog -> *)
(*     make_maps prog = (gmap, lmap, dsize, csize) -> *)
(*     dsize + csize <= Ptrofs.max_unsigned -> *)
(*     list_norepet (map fst (AST.prog_defs prog)) -> *)
(*     (forall b, b <> Globalenvs.Genv.genv_next ge -> j b = init_meminj b) -> *)
(*     forall b b' f ofs *)
(*       (FFP : Globalenvs.Genv.find_funct_ptr ge b = Some (External f)) *)
(*       (JB: j b = Some (b', ofs)), *)
(*       Genv.find_funct tge (Vptr b' (Ptrofs.repr ofs)) = Some (External f). *)
(* Proof. *)  
(*   intros gmap lmap dsize csize efsize j WF TP UM SZ LNR INJ b b' f ofs FFP JB. *)
(*   assert (b <> Globalenvs.Genv.genv_next ge). *)
(*   { *)
(*     unfold Genv.find_funct_ptr in FFP. destr_in FFP. *)
(*     unfold Genv.find_def in Heqo. eapply Globalenvs.Genv.genv_defs_range in Heqo. *)
(*     apply Plt_ne. auto. *)
(*   } *)
(*   rewrite INJ in JB; auto. *)
(*   unfold init_meminj in JB. *)
(*   rewrite pred_dec_false in JB by auto. *)
(*   repeat destr_in JB. *)
(*   unfold tge, Genv.find_funct. *)
(*   unfold globalenv. simpl. *)
(*   rewrite genv_segblocks_add_globals. simpl. *)
(*   unfold gen_segblocks. simpl. *)
(*   exploit update_map_ext_funct; eauto. intro EQ. rewrite EQ. *)
(*   rewrite pred_dec_false. rewrite pred_dec_false. rewrite pred_dec_true. *)
(*   2: erewrite transl_prog_seg_ext; eauto. *)
(*   2: erewrite transl_prog_seg_code; eauto; unfold code_segid, extfuns_segid; congruence. *)
(*   2: erewrite transl_prog_seg_data; eauto; unfold extfuns_segid, data_segid; congruence. *)
(*   exploit @Genv.find_symbol_funct_ptr_inversion. reflexivity. *)
(*   apply Genv.invert_find_symbol. eauto. eauto. intro IN. *)
(*   unfold transl_prog_with_map in TP. monadInv TP. simpl in *. *)
(*   destruct s. simpl in *. subst s. *)
(*   edestruct transl_extfun_exists as (ss & INs & EQs & EQo); eauto. *)
(*   destruct ss; simpl in *. subst segblock_id segblock_start. *)
(*   erewrite genv_defs_add_globals. eauto. *)
(*   eauto. *)
(*   unfold Genv.symbol_address. simpl. unfold Genv.label_to_ptr. simpl. *)
(*   { *)
(*     eapply list_map_norepet_kv. rewrite <- map_map. eapply transl_globdefs_norepet; eauto. *)
(*     simpl. *)
(*     intros ((i1 & o1) & s1) ((i2 & o2) & s2) v1 v2 IN1 IN2 DIFF. simpl in DIFF. *)
(*     destruct o1, o2; try congruence. *)
(*     destruct (in_transl_globdefs' _ _ _ _ _ EQ0 _ _ _ IN1) as (sb1 & G1 & SI1 & SS1). *)
(*     destruct (in_transl_globdefs' _ _ _ _ _ EQ0 _ _ _ IN2) as (sb2 & G2 & SI2 & SS2). *)
(*     destruct (in_transl_globdefs'' _ _ _ _ _ EQ0 _ _ _ IN1) as (d1 & ? & ? & INl1 & TG1). *)
(*     destruct (in_transl_globdefs'' _ _ _ _ _ EQ0 _ _ _ IN2) as (d2 & ? & ? & INl2 & TG2). *)
(*     rewrite ! Ptrofs.add_zero. intros A B VEQ. subst v2. rewrite <- B in A. *)
(*     clear B. *)
(*     inversion A. clear A. *)
(*     destruct s1, s2, sb1, sb2. simpl in *. subst s0 i4 s i3 segblock_start0. *)
(*     exploit update_maps_gmap_inj. eauto. eauto. auto. apply INl1. apply INl2. auto. eauto. eauto. *)
(*     destruct (peq segblock_id segblock_id0). *)
(*     - subst segblock_id0. *)
(*       intros [A | A]. congruence. *)
(*       assert (odef_size d1 <= 0 \/ odef_size d2 <= 0). omega. *)
(*       clear A. clear H2. *)
(*       destruct d1; simpl in TG1; try congruence. *)
(*       destruct d2; simpl in TG2; try congruence. simpl in H0. *)
(*       clear - WF INl1 INl2 H0. *)
(*       inv WF. red in wf_prog_not_empty. rewrite Forall_forall in wf_prog_not_empty. *)
(*       exploit wf_prog_not_empty. apply in_map, INl1. *)
(*       exploit wf_prog_not_empty. apply in_map, INl2. simpl. *)
(*       unfold def_not_empty. simpl. omega. *)
(*     - intros _. apply n. clear n. repeat destr_in H2. *)
(*       exploit update_map_gmap_range. eauto. apply G1. *)
(*       exploit update_map_gmap_range. eauto. apply G2. simpl. clear H1. intuition subst; congruence. *)
(*   } *)
(*   unfold Genv.symbol_address. simpl. unfold Genv.label_to_ptr. *)
(*   simpl. f_equal. rewrite Ptrofs.add_zero. rewrite Ptrofs.repr_unsigned. auto. *)
(* Qed. *)

Lemma add_globals_find_symbol_external: forall defs i f sb b ofs (ge:FlatAsm.genv)
     (NPT: list_norepet (map (fun '(i, _, _) => i) defs))
     (IN: In (i, Some (Gfun (External f)), sb) defs)
     (GNXT: Pos.lt (Pos.of_nat num_segments) (Genv.genv_next ge))
     (FSYM: Genv.find_symbol (add_globals ge defs) i = Some (b, ofs)),
     Pos.lt (Pos.of_nat num_segments) b.
Proof.
  induction defs; simpl; intros. contradiction.
  destruct a. destruct p. inv NPT.
  inv IN.
  - inv H.
    erewrite add_globals_pres_find_symbol_not_in in FSYM; eauto.
    simpl in FSYM. rewrite peq_true in FSYM. inv FSYM. auto.
  - eapply (IHdefs _ _ _ _ _ (add_global ge0 (i0, o, s))); eauto.
    rewrite add_global_next_block. simpl.
    apply Pos.lt_lt_succ; eauto.
Qed.    

Lemma find_symbol_external_block:
  forall gmap lmap dsize csize b b' f i ofs
    (MK: make_maps prog = (gmap, lmap, dsize, csize))
    (TL: transl_prog_with_map gmap lmap prog dsize csize = OK tprog)
    (NPT: list_norepet (map fst (AST.prog_defs prog)))
    (FPTR: Globalenvs.Genv.find_funct_ptr ge b = Some (External f))
    (INVS: Globalenvs.Genv.invert_symbol ge b = Some i)
    (FSYM: Genv.find_symbol tge i = Some (b',ofs)),
    b' <> code_block.
Proof.
  intros. apply Genv.invert_find_symbol in INVS.
  unfold ge in *. exploit Genv.find_symbol_funct_ptr_inversion; eauto.
  intros INS.
  exploit transl_prog_list_norepet; eauto. intros NPT'.
  exploit transl_prog_pres_def; eauto. 
  intros (def' & sb & IN' & TLGF).
  monadInv TLGF.
  unfold tge, globalenv in FSYM. 
  exploit add_globals_find_symbol_external; eauto. 
  simpl. apply Pos.lt_succ_diag_r.
  intros BRNG. unfold not. intros. subst.
  unfold num_segments, code_block in BRNG. simpl in BRNG. 
  eapply Pos.lt_irrefl; eauto.
Qed.
  
Lemma extfun_entry_is_external_init:
  list_norepet (map fst (AST.prog_defs prog)) ->
  extfun_entry_is_external init_meminj.
Proof.
  intros NPT.
  red. intros b b' f ofs FPTR JB.
  unfold tge. unfold globalenv.
  erewrite add_globals_pres_internal_block; eauto. simpl.
  unfold gen_internal_codeblock.
  unfold init_meminj in JB.
  destruct eq_block.
  subst. unfold ge in FPTR.
  exploit Globalenvs.Genv.genv_next_find_funct_ptr_absurd; eauto. contradiction.
  destr_match_in JB; inv JB.
  destr_match_in H0; inv H0.
  destruct p. inv H1.
  assert (match_prog prog tprog) as TRANSF' by auto.
  unfold match_prog in TRANSF'. unfold transf_program in TRANSF'.
  repeat destr_in TRANSF'.
  assert (b' <> code_block).
  eapply find_symbol_external_block; eauto. 
  erewrite transl_prog_seg_code; eauto. 
  erewrite gen_segblocks_code_map; eauto.
  destruct eq_block. contradiction. auto.
Qed.


  

Lemma transl_prog_pres_main_id : forall gmap lmap prog dsize csize tprog,
    transl_prog_with_map gmap lmap prog dsize csize = OK tprog ->
    AST.prog_main prog = prog_main tprog.
Proof.
  intros. monadInv H. simpl. auto.
Qed.


Lemma symbol_address_inject : forall j id ofs
                                (MATCHINJ: match_inj j),
    Val.inject j (Senv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs).
Proof.
  intros. unfold Senv.symbol_address.
  inv MATCHINJ.
  unfold Senv.find_symbol. simpl.
  destruct (Globalenvs.Genv.find_symbol ge id) eqn:FINDSYM; auto.
  exploit agree_inj_glob0; eauto.
  intros (b' & ofs' & FINDSYM' & JB).
  erewrite Genv.symbol_address_offset; eauto. 
  eapply Val.inject_ptr; eauto.
  rewrite Ptrofs.repr_unsigned. apply Ptrofs.add_commut.
  unfold Genv.symbol_address. rewrite FINDSYM'. 
  rewrite Ptrofs.add_zero_l. auto.
Qed.

Lemma main_ptr_inject:
  forall gmap lmap dsize csize 
    (MATCH_INJ: match_inj init_meminj)
    (MAKEMAPS: make_maps prog = (gmap, lmap, dsize, csize))
    (TRANSL: transl_prog_with_map gmap lmap prog dsize csize = OK tprog),
    Val.inject init_meminj
               (Globalenvs.Genv.symbol_address
                  (Globalenvs.Genv.globalenv prog)
                  (AST.prog_main prog) Ptrofs.zero)
               (Genv.symbol_address
                  (globalenv tprog)
                  (prog_main tprog) Ptrofs.zero).
Proof.
  intros.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  repeat destr_in TRANSF.  inv MAKEMAPS. inv w. auto.
  red in wf_prog_main_exists. rewrite Exists_exists in wf_prog_main_exists.
  destruct wf_prog_main_exists as (def & IN & P).
  destruct def. destruct o; destruct P as [IDEQ P]; inv P.
  erewrite <- transl_prog_pres_main_id; eauto.
  eapply symbol_address_inject; eauto.
Qed.



Lemma transf_initial_states : forall rs (SELF: forall j, forall r : PregEq.t, Val.inject j (rs r) (rs r)) st1,
    RealAsm.initial_state prog rs st1  ->
    exists st2, FlatAsm.initial_state tprog rs st2 /\ match_states st1 st2.
Proof.
  intros rs SELFINJECT st1 INIT.
  generalize TRANSF. intros TRANSF'.
  unfold match_prog in TRANSF'. unfold transf_program in TRANSF'.
  destruct (check_wellformedness prog) eqn:WF. 2: congruence. repeat destr_in TRANSF'.
  rename g into gmap.
  rename l into lmap.
  rename z0 into dsize. rename z into csize. 
  inv INIT.
  generalize init_meminj_match_sminj.
  (* exploit init_meminj_match_sminj; eauto. *)
  intros MATCH_SMINJ.
  exploit (init_mem_pres_inject m gmap); eauto.
  intros (m' & INITM' & MINJ).
  inversion H1.
  (* push_new stage *)
  exploit Mem.push_new_stage_inject; eauto. intros NSTGINJ.
  exploit (Mem.alloc_parallel_inject globs_meminj (1%nat :: def_frame_inj m)
          (Mem.push_new_stage m) (Mem.push_new_stage m')
          0 (Mem.stack_limit + align (size_chunk Mptr) 8) m1 bstack
          0 (Mem.stack_limit + align (size_chunk Mptr) 8)); eauto. omega. omega.
  intros (j' & m1' & bstack' & MALLOC' & AINJ & INCR & FBSTACK & NOTBSTK).
  rewrite <- push_new_stage_def_frame_inj in AINJ.
  erewrite alloc_pres_def_frame_inj in AINJ; eauto.
  assert (bstack = Globalenvs.Genv.genv_next ge).
  {
    exploit (Genv.init_mem_genv_next prog m); eauto. intros BEQ. unfold ge. rewrite BEQ.
    apply Mem.alloc_result in MALLOC; eauto.
    subst bstack. apply Mem.push_new_stage_nextblock.
  }
  assert (bstack' = Genv.genv_next tge).
  {
    exploit (@init_mem_genv_next instruction); eauto. intros BEQ.
    unfold tge. rewrite BEQ.
    exploit Mem.alloc_result; eauto.
    intros. subst. apply Mem.push_new_stage_nextblock.
  }
  assert (forall x, j' x = init_meminj x).
  {
    intros. destruct (eq_block x bstack).
    subst x. rewrite FBSTACK. unfold init_meminj. subst.
    rewrite dec_eq_true; auto.
    erewrite NOTBSTK; eauto.
    unfold init_meminj. subst.
    rewrite dec_eq_false; auto.
  }
  exploit Mem.inject_ext; eauto. intros MINJ'.
  exploit Mem.drop_parallel_inject; eauto. red. simpl. auto.
  unfold init_meminj. fold ge. rewrite <- H4. rewrite pred_dec_true. eauto. auto.
  intros (m2' & MDROP' & DMINJ). simpl in MDROP'. rewrite Z.add_0_r in MDROP'.
  erewrite (drop_perm_pres_def_frame_inj m1) in DMINJ; eauto.
  
  assert (exists m3', Mem.record_stack_blocks m2' (make_singleton_frame_adt' bstack' RawAsm.frame_info_mono 0) = Some m3'
                 /\ Mem.inject (init_meminj) (def_frame_inj m3) m3 m3') as RCD.
  {
    unfold def_frame_inj. unfold def_frame_inj in DMINJ.
    eapply (Mem.record_stack_block_inject_flat m2 m3 m2' (init_meminj)
           (make_singleton_frame_adt' bstack RawAsm.frame_info_mono 0)); eauto.
    (* frame inject *)
    red. unfold make_singleton_frame_adt'. simpl. constructor. 
    simpl. intros b2 delta FINJ.
    unfold init_meminj in FINJ. fold ge in FINJ. rewrite <- H4 in FINJ.
    rewrite pred_dec_true in FINJ; auto. inv FINJ.
    exists RawAsm.frame_info_mono. split. auto. apply inject_frame_info_id.
    constructor.
    (* in frame *)
    unfold make_singleton_frame_adt'. simpl. unfold in_frame. simpl.
    repeat rewrite_stack_blocks.
    erewrite init_mem_stack; eauto.
    (* valid frame *)
    unfold make_singleton_frame_adt'. simpl. red. unfold in_frame.
    simpl. intuition. subst.
    eapply Mem.drop_perm_valid_block_1; eauto.
    eapply Mem.valid_new_block; eauto.
    (* frame_agree_perms *)
    red. unfold make_singleton_frame_adt'. simpl.
    intros b fi o k p BEQ PERM. inv BEQ; try contradiction.
    inv H7. unfold RawAsm.frame_info_mono. simpl.
    erewrite drop_perm_perm in PERM; eauto. destruct PERM.
    eapply Mem.perm_alloc_3; eauto.
    (* in frame iff *)
    unfold make_singleton_frame_adt'. unfold in_frame. simpl.
    intros b1 b2 delta INJB. split.
    intros BEQ. destruct BEQ; try contradiction. subst b1.
    unfold init_meminj in INJB. fold ge in INJB. rewrite <- H4 in INJB.
    rewrite pred_dec_true in INJB; auto. inv INJB. left; auto.
    intros BEQ. destruct BEQ; try contradiction. subst b2.
    assert (bstack' = Mem.nextblock (Mem.push_new_stage m')) as BEQ.
    eapply Mem.alloc_result; eauto using MALLOC'.
    rewrite Mem.push_new_stage_nextblock in BEQ.
    erewrite <- init_mem_genv_next in BEQ; eauto using INITM'.
    subst bstack'.
    destruct (eq_block bstack b1); auto.
    assert (b1 <> bstack) by congruence.
    apply NOTBSTK in H5. rewrite H6 in H5. rewrite INJB in H5.
    left. symmetry. subst bstack. eapply init_meminj_genv_next_inv; eauto.

    (* top frame *)
    red. repeat rewrite_stack_blocks. constructor. auto.
    (* size stack *)
    repeat rewrite_stack_blocks.
    erewrite init_mem_stack; eauto. simpl. omega.
  }

  destruct RCD as (m3' & RCDSB & RMINJ).
  set (rs0' := rs # PC <- (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero)
                  # RA <- Vnullptr
                  # RSP <- (Vptr bstack' (Ptrofs.sub (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr))))) in *.
  edestruct storev_mapped_inject' as (m4' & ST & SMINJ). apply RMINJ. eauto. econstructor.
  rewrite <- H6, FBSTACK; eauto. reflexivity. constructor.
  exists (State rs0' m4'). split.
  - eapply initial_state_intro; eauto.
    eapply initial_state_gen_intro; eauto.
    subst. fold tge in MDROP'. eauto.
    subst. fold tge in MDROP'. rewrite Ptrofs.add_zero in ST. eauto.
  - eapply match_states_intro; eauto.
    + eapply valid_instr_offset_is_internal_init; eauto. inv w; auto.
    + eapply extfun_entry_is_external_init; eauto. inv w; auto.
    + red.
      intros. eapply extfun_transf; eauto. inv w; auto.
    + red. unfold rs0, rs0'.
      apply val_inject_set.
      apply val_inject_set.
      apply val_inject_set.
      auto.
      exploit (main_ptr_inject); eauto. unfold Globalenvs.Genv.symbol_address.
      unfold ge, ge0 in *. rewrite H2. fold tge. auto.
      unfold Vnullptr. destr; auto.
      econstructor. unfold init_meminj. subst bstack. fold ge. rewrite peq_true. subst bstack'.  fold tge. eauto.
      rewrite Ptrofs.add_zero.
      apply Ptrofs.sub_add_opp.
    + red. intros b g FD.
      unfold Genv.find_def in FD. eapply Genv.genv_defs_range in FD.
      revert FD. red. rewnb.
      fold ge. intros. xomega.
Qed.


Context `{external_calls_ops : !ExternalCallsOps mem }.
Context `{!EnableBuiltins mem}.
Existing Instance Asm.mem_accessors_default.
Existing Instance FlatAsm.mem_accessors_default.

Lemma eval_builtin_arg_inject : forall j m m' rs rs' sp sp' arg varg
    (MATCHINJ: match_inj j)
    (MINJ: Mem.inject j (def_frame_inj m) m m')
    (RSINJ: regset_inject j rs rs')
    (VINJ: Val.inject j sp sp')
    (EVALBI: eval_builtin_arg ge rs sp m arg varg),
    exists varg', FlatAsmBuiltin.eval_builtin_arg _ _ _ _ tge rs' sp' m' arg varg' /\
             Val.inject j varg varg'.
Proof.
  unfold regset_inject.
  induction arg; intros; inv EVALBI.
  - eexists; split; auto. constructor.
  - eexists; split; auto. constructor.
  - eexists; split; auto. constructor.
  - eexists; split; auto. constructor.
  - eexists; split; auto. constructor.
  - exploit Mem.loadv_inject; eauto.
    apply Val.offset_ptr_inject; eauto.
    intros (v2 & ML & VJ); auto.
    eexists; split. constructor. apply ML. auto.
  - eexists; split. constructor.
    apply Val.offset_ptr_inject; eauto.
  - exploit Mem.loadv_inject; eauto.
    apply symbol_address_inject; eauto.
    intros (v2 & ML & VJ); auto.
    eexists; split. constructor. apply ML. auto.
  - eexists; split. constructor.
    apply symbol_address_inject; eauto.
  - exploit IHarg1; eauto.
    intros (varg1 & EVALBI1 & JB1).
    exploit IHarg2; eauto.
    intros (varg2 & EVALBI2 & JB2).
    eexists; split. constructor; eauto.
    apply Val.longofwords_inject; auto.
Qed.    
   

Lemma eval_builtin_args_inject : forall j m m' rs rs' sp sp' args vargs
    (MATCHINJ: match_inj j)
    (MINJ: Mem.inject j (def_frame_inj m) m m')
    (RSINJ: regset_inject j rs rs')
    (VINJ: Val.inject j sp sp')
    (EVALBI: eval_builtin_args ge rs sp m args vargs),
    exists vargs', FlatAsmBuiltin.eval_builtin_args _ _ _ _ tge rs' sp' m' args vargs' /\
             Val.inject_list j vargs vargs'.
Proof.
  induction args; intros; simpl; inv EVALBI.
  - eexists. split. constructor. auto.
  - exploit eval_builtin_arg_inject; eauto.
    intros (varg' & EVARG & JB).
    exploit IHargs; eauto.
    intros (vargs' & EVARGS & JBS).
    exists (varg' :: vargs'). split; auto.
    unfold FlatAsmBuiltin.eval_builtin_args.
    apply list_forall2_cons; auto.
Qed.

Lemma extcall_arg_inject : forall rs1 rs2 m1 m2 l arg1 j,
    extcall_arg rs1 m1 l arg1 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists arg2,
      Val.inject j arg1 arg2 /\
      extcall_arg rs2 m2 l arg2.
Proof.
  intros. inv H.
  - unfold regset_inject in *.
    specialize (H1 (Asm.preg_of r)). eexists; split; eauto.
    constructor.
  - exploit Mem.loadv_inject; eauto.
    apply Val.offset_ptr_inject. apply H1.
    intros (arg2 & MLOADV & ARGINJ).
    exists arg2. split; auto.
    eapply extcall_arg_stack; eauto.
Qed.

Lemma extcall_arg_pair_inject : forall rs1 rs2 m1 m2 lp arg1 j,
    extcall_arg_pair rs1 m1 lp arg1 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists arg2,
      Val.inject j arg1 arg2 /\
      extcall_arg_pair rs2 m2 lp arg2.
Proof.
  intros. inv H.
  - exploit extcall_arg_inject; eauto.
    intros (arg2 & VINJ & EXTCALL).
    exists arg2. split; auto. constructor. auto.
  - exploit (extcall_arg_inject rs1 rs2 m1 m2 hi vhi); eauto.
    intros (arghi & VINJHI & EXTCALLHI).
    exploit (extcall_arg_inject rs1 rs2 m1 m2 lo vlo); eauto.
    intros (arglo & VINJLO & EXTCALLLO).
    exists (Val.longofwords arghi arglo). split.
    + apply Val.longofwords_inject; auto.
    + constructor; auto.
Qed.

Lemma extcall_arguments_inject_aux : forall rs1 rs2 m1 m2 locs args1 j,
   list_forall2 (extcall_arg_pair rs1 m1) locs args1 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists args2,
      Val.inject_list j args1 args2 /\
      list_forall2 (extcall_arg_pair rs2 m2) locs args2.
Proof.
  induction locs; simpl; intros; inv H.
  - exists nil. split.
    + apply Val.inject_list_nil.
    + unfold Asm.extcall_arguments. apply list_forall2_nil.
  - exploit extcall_arg_pair_inject; eauto.
    intros (arg2 & VINJARG2 & EXTCALLARG2).
    exploit IHlocs; eauto.
    intros (args2 & VINJARGS2 & EXTCALLARGS2).
    exists (arg2 :: args2). split; auto.
    apply list_forall2_cons; auto.
Qed.

Lemma extcall_arguments_inject : forall rs1 rs2 m1 m2 ef args1 j,
    Asm.extcall_arguments rs1 m1 (ef_sig ef) args1 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists args2,
      Val.inject_list j args1 args2 /\
      Asm.extcall_arguments rs2 m2 (ef_sig ef) args2.
Proof.
  unfold Asm.extcall_arguments. intros.
  eapply extcall_arguments_inject_aux; eauto.
Qed.

Axiom external_call_inject : forall ge j vargs1 vargs2 m1 m2 m1' vres1 t ef,
    Val.inject_list j vargs1 vargs2 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    external_call ef ge vargs1 m1 t vres1 m1' ->
    exists j' vres2 m2',
      external_call ef ge vargs2 m2 t vres2 m2' /\
      Val.inject j' vres1 vres2 /\ Mem.inject j' (def_frame_inj m1') m1' m2' /\
      inject_incr j j' /\
      inject_separated j j' m1 m2.

Axiom  external_call_valid_block: forall ef ge vargs m1 t vres m2 b,
    external_call ef ge vargs m1 t vres m2 -> Mem.valid_block m1 b -> Mem.valid_block m2 b.

Lemma extcall_pres_glob_block_valid : forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold glob_block_valid in *. intros.
  eapply external_call_valid_block; eauto.
Qed.

Lemma regset_inject_incr : forall j j' rs rs',
    regset_inject j rs rs' ->
    inject_incr j j' ->
    regset_inject j' rs rs'.
Proof.
  unfold inject_incr, regset_inject. intros.
  specialize (H r).
  destruct (rs r); inversion H; subst; auto.
  eapply Val.inject_ptr. apply H0. eauto. auto.
Qed.

Lemma undef_regs_pres_inject : forall j rs rs' regs,
  regset_inject j rs rs' ->
  regset_inject j (Asm.undef_regs regs rs) (Asm.undef_regs regs rs').
Proof.
  unfold regset_inject. intros. apply val_inject_undef_regs.
  auto.
Qed.    
  
Lemma Pregmap_gsspec_alt : forall (A : Type) (i j : Pregmap.elt) (x : A) (m : Pregmap.t A),
    (m # j <- x) i  = (if Pregmap.elt_eq i j then x else m i).
Proof.
  intros. apply Pregmap.gsspec.
Qed.

Lemma regset_inject_expand : forall j rs1 rs2 v1 v2 r,
  regset_inject j rs1 rs2 ->
  Val.inject j v1 v2 ->
  regset_inject j (rs1 # r <- v1) (rs2 # r <- v2).
Proof.
  intros. unfold regset_inject. intros.
  repeat rewrite Pregmap_gsspec_alt. 
  destruct (Pregmap.elt_eq r0 r); auto.
Qed.

Lemma regset_inject_expand_vundef_left : forall j rs1 rs2 r,
  regset_inject j rs1 rs2 ->
  regset_inject j (rs1 # r <- Vundef) rs2.
Proof.
  intros. unfold regset_inject. intros.
  rewrite Pregmap_gsspec_alt. destruct (Pregmap.elt_eq r0 r); auto.
Qed.

Lemma set_res_pres_inject : forall res j rs1 rs2,
    regset_inject j rs1 rs2 ->
    forall vres1 vres2,
    Val.inject j vres1 vres2 ->
    regset_inject j (set_res res vres1 rs1) (set_res res vres2 rs2).
Proof.
  induction res; auto; simpl; unfold regset_inject; intros.
  - rewrite Pregmap_gsspec_alt. destruct (Pregmap.elt_eq r x); subst.
    + rewrite Pregmap.gss. auto.
    + rewrite Pregmap.gso; auto.
  - exploit (Val.hiword_inject j vres1 vres2); eauto. intros. 
    exploit (Val.loword_inject j vres1 vres2); eauto. intros.
    apply IHres2; auto.
Qed.


Lemma nextinstr_pres_inject : forall j rs1 rs2 sz,
    regset_inject j rs1 rs2 ->
    regset_inject j (nextinstr rs1 sz) (nextinstr rs2 sz).
Proof.
  unfold nextinstr. intros. apply regset_inject_expand; auto.
  apply Val.offset_ptr_inject. auto.
Qed.  

Lemma nextinstr_nf_pres_inject : forall j rs1 rs2 sz,
    regset_inject j rs1 rs2 ->
    regset_inject j (nextinstr_nf rs1 sz) (nextinstr_nf rs2 sz).
Proof.
  intros. apply nextinstr_pres_inject.
  apply undef_regs_pres_inject. auto.
Qed. 


Lemma set_pair_pres_inject : forall j rs1 rs2 v1 v2 loc,
    regset_inject j rs1 rs2 ->
    Val.inject j v1 v2 ->
    regset_inject j (set_pair loc v1 rs1) (set_pair loc v2 rs2).
Proof.
  intros. unfold set_pair, Asm.set_pair. destruct loc; simpl.
  - apply regset_inject_expand; auto.
  - apply regset_inject_expand; auto.
    apply regset_inject_expand; auto.
    apply Val.hiword_inject; auto.
    apply Val.loword_inject; auto.
Qed.

Lemma vinject_pres_not_vundef : forall j v1 v2,
  Val.inject j v1 v2 -> v1 <> Vundef -> v2 <> Vundef.
Proof.
  intros. destruct v1; inversion H; subst; auto.
  congruence.
Qed.

Lemma vinject_pres_has_type : forall j v1 v2 t,
    Val.inject j v1 v2 -> v1 <> Vundef ->
    Val.has_type v1 t -> Val.has_type v2 t.
Proof.
  intros. destruct v1; inversion H; subst; simpl in H; auto. 
  congruence.
Qed.

Lemma inject_decr : forall b j j' m1 m2 b' ofs,
  Mem.valid_block m1 b -> inject_incr j j' -> inject_separated j j' m1 m2 ->
  j' b = Some (b', ofs) -> j b = Some (b', ofs).
Proof.
  intros. destruct (j b) eqn:JB.
  - unfold inject_incr in *. destruct p. exploit H0; eauto.
    intros. congruence.
  - unfold inject_separated in *. exploit H1; eauto.
    intros (NVALID1 & NVALID2). congruence.
Qed.

Lemma inject_pres_match_sminj : 
  forall j j' m1 m2 (ms: match_inj j), 
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 -> 
    match_inj j'.
Proof.
  unfold glob_block_valid.
  intros. inversion ms. constructor; intros.
  -
    eapply (agree_inj_instr0 b b'); eauto.
    unfold Globalenvs.Genv.find_funct_ptr in H2. destruct (Globalenvs.Genv.find_def ge b) eqn:FDEF; try congruence.
    exploit H; eauto. intros.
    eapply inject_decr; eauto.
  -
    exploit agree_inj_glob0; eauto.
    intros (b' & ofs' & GLBL & JB).
    eexists; eexists; eexists; eauto.
  -
    exploit agree_inj_lbl0; eauto.
Qed.


Lemma inject_pres_valid_instr_offset_is_internal : forall j j' m1 m2,
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 ->
    valid_instr_offset_is_internal j -> valid_instr_offset_is_internal j'.
Proof.
  unfold glob_block_valid.
  unfold valid_instr_offset_is_internal. intros.
  eapply H2; eauto.
  unfold Globalenvs.Genv.find_funct_ptr in H3. destruct (Globalenvs.Genv.find_def ge b) eqn:FDEF; try congruence.
  exploit H; eauto. intros.
  eapply inject_decr; eauto.
Qed.

Lemma inject_pres_extfun_entry_is_external : forall j j' m1 m2,
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 ->
    extfun_entry_is_external j -> extfun_entry_is_external j'.
Proof.
  unfold glob_block_valid.
  unfold extfun_entry_is_external. intros.
  eapply H2; eauto.
  unfold Globalenvs.Genv.find_funct_ptr in H3. destruct (Globalenvs.Genv.find_def ge b) eqn:FDEF; try congruence.
  exploit H; eauto. intros.
  eapply inject_decr; eauto.
Qed.

Lemma inject_pres_match_find_funct : forall j j' m1 m2,
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 ->
    match_find_funct j -> match_find_funct j'.
Proof.
  unfold glob_block_valid, match_find_funct. intros.
  eapply H2; eauto.
  unfold Globalenvs.Genv.find_funct_ptr in H3. destruct (Globalenvs.Genv.find_def ge b) eqn:FDEF; try congruence.
  exploit H; eauto. intros.
  eapply inject_decr; eauto.
Qed.



Lemma inject_symbol_address : forall j id ofs,
    match_inj j ->
    Val.inject j (Globalenvs.Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs).
Proof.
  unfold Globalenvs.Genv.symbol_address.
  intros.
  destruct (Globalenvs.Genv.find_symbol ge id) eqn:FINDSYM; auto.
  inv H. exploit agree_inj_glob0; eauto.
  intros (b' & ofs' & SBOFS & JB).
  erewrite Genv.symbol_address_offset; eauto. 
  eapply Val.inject_ptr; eauto.
  rewrite Ptrofs.repr_unsigned. apply Ptrofs.add_commut.
  unfold Genv.symbol_address. rewrite SBOFS.
  rewrite Ptrofs.add_zero_l. auto.
Qed.


Ltac simpl_goal :=
  repeat match goal with
         | [ |- context [ Int.add Int.zero _ ] ] =>
           rewrite Int.add_zero_l
         | [ |- context [ Int64.add Int64.zero _ ] ] =>
           rewrite Int64.add_zero_l
         | [ |- context [Ptrofs.add _ (Ptrofs.of_int Int.zero)] ] =>
           rewrite Ptrofs.add_zero
         | [ |- context [Ptrofs.add _ (Ptrofs.of_int64 Int64.zero)] ] =>
           rewrite Ptrofs.add_zero
         | [ |- context [Ptrofs.add Ptrofs.zero _] ] =>
           rewrite Ptrofs.add_zero_l
         | [ |- context [Ptrofs.repr (Ptrofs.unsigned _)] ] =>
           rewrite Ptrofs.repr_unsigned
         end.

(* Ltac solve_symb_inj := *)
(*   match goal with *)
(*   | [  H1 : Globalenvs.Genv.symbol_address _ _ _ = _, *)
(*        H2 : Genv.symbol_address _ _ _ = _ |- _ ] => *)
(*     exploit inject_symbol_sectlabel; eauto; *)
(*     rewrite H1, H2; auto *)
(*   end. *)

Ltac destr_pair_if :=
  repeat match goal with
         | [ |- context [match ?a with pair _ _ => _ end] ] =>
           destruct a eqn:?
         | [ |- context [if ?h then _ else _] ] =>
           destruct h eqn:?
         end.

Ltac inject_match :=
  match goal with
  | [ |- Val.inject ?j (match ?a with _ => _ end) (match ?b with _ => _ end) ] =>
    assert (Val.inject j a b)
  end.

Ltac inv_valinj :=
  match goal with
         | [ H : Val.inject _ (Vint _) _ |- _ ] =>
           inversion H; subst
         | [ H : Val.inject _ (Vlong _) _ |- _ ] =>
           inversion H; subst
         | [ H : Val.inject _ (Vptr _ _) _ |- _ ] =>
           inversion H; subst
         end.

Ltac destr_valinj_right H :=
  match type of H with
  | Val.inject _ _ ?a =>
    destruct a eqn:?
  end.

Ltac destr_valinj_left H :=
  match type of H with
  | Val.inject _ ?a ?b =>
    destruct a eqn:?
  end.

Lemma eval_addrmode32_inject: forall j a rs1 rs2,
    match_inj j ->
    regset_inject j rs1 rs2 ->
    Val.inject j (Asm.eval_addrmode32 ge a rs1) (FlatAsm.eval_addrmode32 tge a rs2).
Proof.
  intros. unfold Asm.eval_addrmode32, FlatAsm.eval_addrmode32.
  destruct a. 
  destruct base, ofs, const; simpl in *. 
  - destruct p. repeat apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply Val.mul_inject; auto.
  - destruct p,p0. repeat apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply Val.mul_inject; auto.
    apply inject_symbol_address. auto.
  - repeat apply Val.add_inject; auto.
  - destruct p. apply Val.add_inject; auto. 
    inject_match. apply inject_symbol_address; auto.
    destr_valinj_left H1; inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int. 
    repeat rewrite Int.unsigned_zero. 
    repeat rewrite Ptrofs.add_zero. auto.
  - destruct p.
    inject_match.
    apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply Val.mul_inject; auto.
    destr_valinj_left H1; inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int. 
    repeat rewrite Int.unsigned_zero. 
    repeat rewrite Ptrofs.add_zero. auto.
  - destruct p,p0.
    inject_match.
    apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply Val.mul_inject; auto.
    apply inject_symbol_address; auto.
    destr_valinj_left H1; inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int. 
    repeat rewrite Int.unsigned_zero. 
    repeat rewrite Ptrofs.add_zero. auto.
  - repeat apply Val.add_inject; auto.
  - destruct p. 
    inject_match. inject_match.
    apply inject_symbol_address; auto.
    destr_valinj_left H1; inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int. 
    repeat rewrite Int.unsigned_zero. 
    repeat rewrite Ptrofs.add_zero. auto.
    destr_valinj_left H1; inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int. 
    repeat rewrite Int.unsigned_zero. 
    repeat rewrite Ptrofs.add_zero. auto.
Qed.    

Lemma eval_addrmode64_inject: forall j a rs1 rs2,
    match_inj j ->
    regset_inject j rs1 rs2 ->
    Val.inject j (Asm.eval_addrmode64 ge a rs1) (FlatAsm.eval_addrmode64 tge a rs2).
Proof.
  intros. unfold Asm.eval_addrmode32, FlatAsm.eval_addrmode32.
  destruct a. 
  destruct base, ofs, const; simpl in *.
  - destruct p. repeat apply Val.addl_inject; auto.
    destr_pair_if; auto.
    apply Val.mull_inject; auto.
  - destruct p,p0. repeat apply Val.addl_inject; auto.
    destr_pair_if; auto.
    apply Val.mull_inject; auto.
    apply inject_symbol_address. auto.
  - repeat apply Val.addl_inject; auto.
  - destruct p. apply Val.addl_inject; auto. 
    inject_match. apply inject_symbol_address; auto.
    destr_valinj_left H1; inv H1; auto.
    (* destr_pair_if; auto. *)
    (* eapply Val.inject_ptr; eauto.  *)
    (* repeat rewrite Ptrofs.add_assoc.  *)
    (* rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto. *)
  - destruct p. 
    inject_match.
    apply Val.addl_inject; auto.
    destr_pair_if; auto. 
    apply Val.mull_inject; auto.
    destr_valinj_left H1; inv H1; auto.
    (* destr_pair_if; auto. *)
    (* eapply Val.inject_ptr; eauto.  *)
    (* repeat rewrite Ptrofs.add_assoc.  *)
    (* rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto. *)
  - destruct p,p0.
    inject_match.
    apply Val.addl_inject; auto.
    destr_pair_if; auto. 
    apply Val.mull_inject; auto.
    apply inject_symbol_address; auto.
    destr_valinj_left H1; inv H1; auto.
    (* destr_pair_if; auto. *)
    (* eapply Val.inject_ptr; eauto.  *)
    (* repeat rewrite Ptrofs.add_assoc.  *)
    (* rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto. *)
  - repeat apply Val.addl_inject; auto.
  - destruct p. inject_match. inject_match.
    apply inject_symbol_address; auto.
    destr_valinj_left H1; inv H1; auto.
    destr_valinj_left H1; inv H1; auto.
    (* eapply Val.inject_ptr; eauto.  *)
    (* repeat rewrite Ptrofs.add_assoc.  *)
    (* rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto. *)    
Qed.

Lemma eval_addrmode_inject: forall j a rs1 rs2,
    match_inj j ->
    regset_inject j rs1 rs2 ->
    Val.inject j (Asm.eval_addrmode ge a rs1) (FlatAsm.eval_addrmode tge a rs2).
Proof.
  intros. unfold Asm.eval_addrmode, eval_addrmode. destruct Archi.ptr64.
  + eapply eval_addrmode64_inject; eauto.
  + eapply eval_addrmode32_inject; eauto.
Qed.

Lemma exec_load_step: forall j rs1 rs2 m1 m2 rs1' m1' sz chunk rd a
                          (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                          (MATCHINJ: match_inj j)
                          (* (GINJFLATMEM: globs_inj_into_flatmem j) *)
                          (INSTRINTERNAL: valid_instr_offset_is_internal j)
                          (EXTEXTERNAL: extfun_entry_is_external j)
                          (MATCHFINDFUNCT: match_find_funct j)
                          (RSINJ: regset_inject j rs1 rs2)
                          (GBVALID: glob_block_valid m1),
                          (* (GMUNDEF: gid_map_for_undef_syms gm), *)
    Asm.exec_load ge chunk m1 a rs1 rd sz = Next rs1' m1' ->
    exists rs2' m2',
      FlatAsm.exec_load tge chunk m2 a rs2 rd sz = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_load in *.
  exploit eval_addrmode_inject; eauto. intro EMODINJ.
  destruct (Mem.loadv chunk m1 (Asm.eval_addrmode ge a rs1)) eqn:MLOAD; try congruence.
  exploit Mem.loadv_inject; eauto. intros (v2 & MLOADV & VINJ).
  eexists. eexists. split.
  - unfold exec_load. rewrite MLOADV. auto.
  - inv H. eapply match_states_intro; eauto.
    apply nextinstr_pres_inject. apply undef_regs_pres_inject.
    apply regset_inject_expand; eauto.
Qed.

Lemma store_pres_glob_block_valid : forall m1 chunk b v ofs m2,
  Mem.store chunk m1 b ofs v = Some m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold glob_block_valid in *. intros.
  eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma storev_pres_glob_block_valid : forall m1 chunk ptr v m2,
  Mem.storev chunk m1 ptr v = Some m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold Mem.storev. intros. destruct ptr; try congruence.
  eapply store_pres_glob_block_valid; eauto.
Qed.

Lemma exec_store_step: forall j rs1 rs2 m1 m2 rs1' m1' sz chunk r a dregs
                         (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                         (MATCHINJ: match_inj j)
                         (* (GINJFLATMEM: globs_inj_into_flatmem j) *)
                         (INSTRINTERNAL: valid_instr_offset_is_internal j)
                         (EXTEXTERNAL: extfun_entry_is_external j)
                         (MATCHFINDFUNCT: match_find_funct j)
                         (RSINJ: regset_inject j rs1 rs2)
                         (GBVALID: glob_block_valid m1),
                         (* (GMUNDEF: gid_map_for_undef_syms gm), *)
    Asm.exec_store ge chunk m1 a rs1 r dregs sz = Next rs1' m1' ->
    exists rs2' m2',
      FlatAsm.exec_store tge chunk m2 a rs2 r dregs sz = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_store in *.
  exploit eval_addrmode_inject; eauto. intro EMODINJ.
  destruct (Mem.storev chunk m1 (Asm.eval_addrmode ge a rs1) (rs1 r)) eqn:MSTORE; try congruence.
  exploit Mem.storev_mapped_inject; eauto. intros (m2' & MSTOREV & MINJ').
  eexists. eexists. split.
  - unfold exec_store. rewrite MSTOREV. auto.
  - inv H. eapply match_states_intro; eauto.
    erewrite <- storev_pres_def_frame_inj; eauto.
    apply nextinstr_pres_inject. repeat apply undef_regs_pres_inject. auto.
    eapply storev_pres_glob_block_valid; eauto.
Qed.


(* Injection for cmpu_bool and cmplu_bool *)
Lemma valid_ptr_inj : forall j m m',
    Mem.inject j (def_frame_inj m) m m' ->
    forall b i b' delta,                                  
      j b = Some (b', delta) ->
      Mem.valid_pointer m b (Ptrofs.unsigned i) = true ->
      Mem.valid_pointer m' b' (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply Mem.valid_pointer_inject'; eauto.
Qed.


Lemma weak_valid_ptr_inj: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject'; eauto.
Qed.

Lemma weak_valid_ptr_no_overflow: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
Qed.

Lemma valid_different_ptrs_inj: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  j b1 = Some (b1', delta1) ->
  j b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros. eapply Mem.different_pointers_inject; eauto.
Qed.

Definition cmpu_bool_inject := fun j m m' (MINJ: Mem.inject j (def_frame_inj m) m m') =>
                     Val.cmpu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                          (valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_no_overflow j m m' MINJ)
                                          (valid_different_ptrs_inj j m m' MINJ).

Lemma cmpu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.opt_lessdef (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmpu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmpu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Definition cmplu_bool_inject := fun j m m' (MINJ: Mem.inject j (def_frame_inj m) m m') =>
                     Val.cmplu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                           (valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_no_overflow j m m' MINJ)
                                           (valid_different_ptrs_inj j m m' MINJ).


Lemma cmplu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.opt_lessdef (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmplu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmplu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Lemma val_of_optbool_lessdef : forall j v1 v2,
    Val.opt_lessdef v1 v2 -> Val.inject j (Val.of_optbool v1) (Val.of_optbool v2).
Proof.
  intros. destruct v1; auto.
  simpl. inv H. destruct b; constructor.
Qed.

Lemma cmpu_inject : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.inject j (Val.cmpu (Mem.valid_pointer m) c v1 v2)
               (Val.cmpu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmpu.
  exploit (cmpu_bool_lessdef j v1 v2); eauto. intros. 
  exploit val_of_optbool_lessdef; eauto.
Qed.

Lemma val_negative_inject: forall j v1 v2,
  Val.inject j v1 v2 -> Val.inject j (Val.negative v1) (Val.negative v2).
Proof.
  intros. unfold Val.negative. destruct v1; auto.
  inv H. auto.
Qed.

Lemma val_negativel_inject: forall j v1 v2,
  Val.inject j v1 v2 -> Val.inject j (Val.negativel v1) (Val.negativel v2).
Proof.
  intros. unfold Val.negativel. destruct v1; auto.
  inv H. auto.
Qed.

Lemma sub_overflow_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> 
    Val.inject j (Val.sub_overflow v1 v1') (Val.sub_overflow v2 v2').
Proof.
  intros. unfold Val.sub_overflow. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma subl_overflow_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> 
    Val.inject j (Val.subl_overflow v1 v1') (Val.subl_overflow v2 v2').
Proof.
  intros. unfold Val.subl_overflow. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma compare_ints_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_ints v1 v2 rs m) (compare_ints v1' v2' rs' m').
Proof.
  intros. unfold compare_ints, Asm.compare_ints.
  repeat apply regset_inject_expand; auto.
  - apply cmpu_inject; auto.
  - apply cmpu_inject; auto.
  - apply val_negative_inject. apply Val.sub_inject; auto.
  - apply sub_overflow_inject; auto.
Qed.

Lemma cmplu_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.opt_val_inject j (Val.cmplu (Mem.valid_pointer m) c v1 v2)
                     (Val.cmplu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmplu.
  exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' c); eauto. intros.
  inversion H2; subst; simpl; constructor.
  apply Val.vofbool_inject.
Qed.

Lemma compare_longs_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_longs v1 v2 rs m) (compare_longs v1' v2' rs' m').
Proof.
  intros. unfold compare_longs, Asm.compare_longs.
  repeat apply regset_inject_expand; auto.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Ceq); eauto. intros.
    inversion H3; subst.
    + simpl. auto. 
    + simpl. apply Val.vofbool_inject.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Clt); eauto. intros.
    inversion H3; subst.
    + simpl. auto. 
    + simpl. apply Val.vofbool_inject.
  - apply val_negativel_inject. apply Val.subl_inject; auto.
  - apply subl_overflow_inject; auto.
Qed.

Ltac solve_val_inject :=
  match goal with
  (* | [ H : Val.inject _ (Vint _) (Vlong _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vfloat _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vsingle _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vptr _ _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vlong _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vfloat _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vsingle _) |- _] => inversion H *)
  | [ H : Val.inject _ (Vfloat _) Vundef |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vint _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vlong _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vsingle _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vptr _ _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vfloat _) |- _] => inv H; solve_val_inject
  | [ H : Val.inject _ (Vsingle _) Vundef |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vint _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vlong _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vsingle _) |- _] => inv H; solve_val_inject
  | [ H : Val.inject _ (Vsingle _) (Vptr _ _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vfloat _) |- _] => inversion H
  | [ |- Val.inject _ (Val.of_bool ?v) (Val.of_bool ?v) ] => apply Val.vofbool_inject
  | [ |- Val.inject _ Vundef _ ] => auto
  end.

Ltac solve_regset_inject :=
  match goal with
  | [ H: regset_inject ?j ?rs1 ?rs2 |- regset_inject ?j (Asm.undef_regs ?uregs ?rs1) (Asm.undef_regs ?uregs ?rs2)] =>
    apply undef_regs_pres_inject; auto
  | [ |- regset_inject _ (Asm.undef_regs _ _) _ ] =>
    unfold Asm.undef_regs; solve_regset_inject
  | [ |- regset_inject _ _ (Asm.undef_regs _ _) ] =>
    unfold Asm.undef_regs; simpl; solve_regset_inject
  | [ |- regset_inject _ (?rs1 # ?r <- ?v1) (?rs2 # ?r <- ?v2) ] =>
    apply regset_inject_expand; [solve_regset_inject | solve_val_inject]
  | [ H: regset_inject ?j ?rs1 ?rs2 |- regset_inject ?j ?rs1 ?rs2 ] =>
    auto
  end.

Lemma compare_floats_inject: forall j v1 v2 v1' v2' rs rs',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_floats v1 v2 rs) (compare_floats v1' v2' rs').
Proof.
  intros. unfold compare_floats, Asm.compare_floats.
  destruct v1, v2, v1', v2'; try solve_regset_inject. 
Qed.

Lemma compare_floats32_inject: forall j v1 v2 v1' v2' rs rs',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_floats32 v1 v2 rs) (compare_floats32 v1' v2' rs').
Proof.
  intros. unfold compare_floats32, Asm.compare_floats32.
  destruct v1, v2, v1', v2'; try solve_regset_inject. 
Qed.

  
Ltac solve_store_load :=
  match goal with
  | [ H : Asm.exec_instr _ _ _ _ _ _ = Next _ _ |- _ ] =>
    unfold Asm.exec_instr in H; simpl in H; solve_store_load
  | [ H : Asm.exec_store _ _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_store_step; eauto
  | [ H : Asm.exec_load _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_load_step; eauto
  end.

Ltac solve_opt_lessdef := 
  match goal with
  | [ |- Val.opt_lessdef (match ?rs1 ?r with
                     | _ => _
                     end) _ ] =>
    let EQ := fresh "EQ" in (destruct (rs1 r) eqn:EQ; solve_opt_lessdef)
  | [ |- Val.opt_lessdef None _ ] => constructor
  | [ |- Val.opt_lessdef (Some _) (match ?rs2 ?r with
                              | _ => _
                              end) ] =>
    let EQ := fresh "EQ" in (destruct (rs2 r) eqn:EQ; solve_opt_lessdef)
  | [ H1: regset_inject _ ?rs1 ?rs2, H2: ?rs1 ?r = _, H3: ?rs2 ?r = _ |- _ ] =>
    generalize (H1 r); rewrite H2, H3; clear H2 H3; inversion 1; subst; solve_opt_lessdef
  | [ |- Val.opt_lessdef (Some ?v) (Some ?v) ] => constructor
  end.

Lemma eval_testcond_inject: forall j c rs1 rs2,
    regset_inject j rs1 rs2 ->
    Val.opt_lessdef (Asm.eval_testcond c rs1) (Asm.eval_testcond c rs2).
Proof.
  intros. destruct c; simpl; try solve_opt_lessdef.
Qed.

Hint Resolve nextinstr_nf_pres_inject nextinstr_pres_inject regset_inject_expand
  regset_inject_expand_vundef_left undef_regs_pres_inject
  Val.zero_ext_inject Val.sign_ext_inject Val.longofintu_inject Val.longofint_inject
  Val.singleoffloat_inject Val.loword_inject Val.floatofsingle_inject Val.intoffloat_inject Val.maketotal_inject
  Val.intoffloat_inject Val.floatofint_inject Val.intofsingle_inject Val.singleofint_inject
  Val.longoffloat_inject Val.floatoflong_inject Val.longofsingle_inject Val.singleoflong_inject
  eval_addrmode32_inject eval_addrmode64_inject eval_addrmode_inject
  Val.neg_inject Val.negl_inject Val.add_inject Val.addl_inject
  Val.sub_inject Val.subl_inject Val.mul_inject Val.mull_inject Val.mulhs_inject Val.mulhu_inject
  Val.mullhs_inject Val.mullhu_inject Val.shr_inject Val.shrl_inject Val.or_inject Val.orl_inject
  Val.xor_inject Val.xorl_inject Val.and_inject Val.andl_inject Val.notl_inject
  Val.shl_inject Val.shll_inject Val.vzero_inject Val.notint_inject
  Val.shru_inject Val.shrlu_inject Val.ror_inject Val.rorl_inject
  compare_ints_inject compare_longs_inject compare_floats_inject compare_floats32_inject
  Val.addf_inject Val.subf_inject Val.mulf_inject Val.divf_inject Val.negf_inject Val.absf_inject
  Val.addfs_inject Val.subfs_inject Val.mulfs_inject Val.divfs_inject Val.negfs_inject Val.absfs_inject
  val_of_optbool_lessdef eval_testcond_inject Val.offset_ptr_inject: inject_db.

Ltac solve_exec_instr :=
  match goal with
  | [ |- Next _ _ = Next _ _ ] =>
    reflexivity
  | [ |- context [eval_testcond _ _] ]=>
    unfold eval_testcond; solve_exec_instr
  | [ H: Asm.eval_testcond ?c ?r = _ |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite H; solve_exec_instr
  | [ H: _ = Asm.eval_testcond ?c ?r |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite <- H; solve_exec_instr
  end.

Ltac solve_match_states :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ |- exists _, _ ] => eexists; solve_match_states
  | [ |- (FlatAsm.exec_instr _ _ _ _ = Next _ _) /\ match_states _ _ ] =>
    split; [simpl; solve_exec_instr | econstructor; eauto; solve_match_states]
  | [ |- regset_inject _ _ _ ] =>
    eauto 10 with inject_db
  end.

Ltac destr_eval_testcond :=
  match goal with
  | [ H : match Asm.eval_testcond ?c ?rs with | _ => _ end = Next _ _ |- _ ] =>
    let ETEQ := fresh "ETEQ" in (
      destruct (Asm.eval_testcond c rs) eqn:ETEQ); destr_eval_testcond
  | [ H : Some ?b = Asm.eval_testcond _ _ |- _ ] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.eval_testcond _ _ = Some ?b |- _] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.Next _ _ = Next _ _ |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: Val.opt_lessdef (Some true) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: Val.opt_lessdef (Some false) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | _ => idtac
  end.

Ltac destr_match_outcome :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ H: Asm.Next _ _ = Next _ _ |- _ ] => inv H; destr_match_outcome
  | [ H: match ?a with _ => _ end = Next _ _ |- _] =>
    let EQ := fresh "EQ" in (destruct a eqn:EQ; destr_match_outcome)
  | _ => idtac
  end.


Lemma goto_label_pres_mem : forall f l rs1 m1 rs1' m1',
    Asm.goto_label ge f l rs1 m1 = Next rs1' m1' -> m1 = m1'.
Proof.
  unfold Asm.goto_label. intros.
  destruct (label_pos l 0 (Asm.fn_code f)); try inv H. 
  destruct (rs1 Asm.PC); try inv H1.
  destruct (Globalenvs.Genv.find_funct_ptr ge b); try inv H0. auto.
Qed.

Lemma goto_label_inject : forall rs1 rs2 id b f l j m1 m2 rs1' m1' ofs
                            (MATCHSMINJ: match_inj j)
                            (RINJ: regset_inject j rs1 rs2)
                            (MINJ:Mem.inject j (def_frame_inj m1) m1 m2),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_symbol ge id = Some b ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.goto_label ge f l rs1 m1 = Next rs1' m1' ->
    exists rs2', goto_label tge id l rs2 m2 = Next rs2' m2 /\
            regset_inject j rs1' rs2' /\ Mem.inject j (def_frame_inj m1') m1' m2.
Proof.
  intros. unfold Asm.goto_label in H2.
  destruct (label_pos l 0 (Asm.fn_code f)) eqn:EQLBL; try inv H2.
  setoid_rewrite H in H4. rewrite H1 in H4. inv H4.
  exploit agree_inj_lbl; eauto. intros.
  eexists. split.
  unfold goto_label. auto. split; auto.
  repeat apply regset_inject_expand; auto.
Qed.

Lemma goto_tbl_label_inject : forall id tbl l b f j rs1 rs2 m1 m2 rs1' m1' i ofs
                                (MATCHSMINJ: match_inj j)
                                (RINJ: regset_inject j rs1 rs2)
                                (MINJ:Mem.inject j (def_frame_inj m1) m1 m2),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_symbol ge id = Some b ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    list_nth_z tbl i = Some l ->
    Asm.goto_label ge f l ((rs1 # RAX <- Vundef) # RDX <- Vundef) m1 = Next rs1' m1' ->
    exists rs2',
      FlatAsm.goto_label tge id l ((rs2 # RAX <- Vundef) # RDX <- Vundef) m2 = Next rs2' m2 /\
      regset_inject j rs1' rs2' /\ Mem.inject j (def_frame_inj m1') m1' m2.
Proof.
  induction tbl; simpl; intros.
  - congruence.
  - destruct (zeq i 0).
    + inv H2. 
      exploit (goto_label_inject ((rs1 # RAX <- Vundef) # RDX <- Vundef) ((rs2 # RAX <- Vundef) # RDX <- Vundef)); eauto with inject_db.
    + exploit IHtbl; eauto.
Qed.

Lemma add_globals_pres_senv :
  forall (defs : list (ident * option gdef * segblock)) (ge : FlatAsm.genv),
  Genv.genv_senv (add_globals ge defs) = Genv.genv_senv ge.
Proof.
  induction defs; intros.
  - simpl. auto.
  - simpl. erewrite IHdefs; eauto.
    unfold add_global. destruct a. destruct p. 
    destruct (Genv.genv_symb ge0 i) eqn:GENVSYM.
    + destruct p. simpl. auto.
    + auto.
Qed.

Lemma transl_prog_pres_senv : forall gmap lmap dsize csize tprog prog,
    transl_prog_with_map gmap lmap prog dsize csize = OK tprog ->
    (Genv.genv_senv (globalenv tprog)) = (Globalenvs.Genv.globalenv prog).
Proof.
  intros gmap lmap dsize csize tprog0 prog0 H.
  monadInv H. unfold globalenv. simpl.
  rewrite add_globals_pres_senv; eauto.
Qed.


(* Hypothesis no_pseudo_instrs: *)
(*   forall id b f ofs i *)
(*     (FS: Globalenvs.Genv.find_symbol ge id = Some b) *)
(*     (FFP: Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f)) *)
(*     (FI : find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i), *)
(*     match i with *)
(*       Pallocframe _ _ _ *)
(*     | Pfreeframe _ _ *)
(*     | Pload_parent_pointer _ _ => False *)
(*     | _ => True *)
(*     end. *)

(** The internal step preserves the invariant *)
Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' i i' id sid ofs ofs' f b
                        (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                        (MATCHSMINJ: match_inj j)
                        (* (GINJFLATMEM: globs_inj_into_flatmem j) *)
                        (INSTRINTERNAL: valid_instr_offset_is_internal j)
                        (EXTEXTERNAL: extfun_entry_is_external j)
                        (MATCHFINDFUNCT: match_find_funct j)
                        (RSINJ: regset_inject j rs1 rs2)
                        (GBVALID: glob_block_valid m1),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_symbol ge id = Some b ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    RealAsm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
    transl_instr ofs' id sid i = OK i' ->
    exists rs2' m2',
      FlatAsm.exec_instr tge i' rs2 m2 = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros.
  destruct i; inv H3; simpl in *; monadInvX H4;
                        try first [solve_store_load |
                                   solve_match_states].

  - (* Pmov_rs *)
    apply nextinstr_nf_pres_inject.
    apply regset_inject_expand; auto.
    inv MATCHSMINJ.
    unfold Globalenvs.Genv.symbol_address.
    destruct (Globalenvs.Genv.find_symbol ge id0) eqn:FINDSYM; auto.
    exploit agree_inj_glob0; eauto.
    intros (b1 & ofs1 & GLBL & JB).
    erewrite Genv.find_sym_to_addr with (ofs:=ofs1); eauto.
    rewrite <- (Ptrofs.add_zero_l ofs1).
    eapply Val.inject_ptr; eauto.
    rewrite Ptrofs.repr_unsigned. auto.

  (* Divisions *)
  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.
     
  - (* Pcmov *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c rs1 rs2); eauto.
    intros. 
    destr_eval_testcond; try solve_match_states.
    destruct (Asm.eval_testcond c rs2) eqn:EQ'. destruct b0; solve_match_states.
    solve_match_states.

  - (* Pjmp_l *)
    unfold Asm.exec_instr in H6; simpl in H6.
    unfold Asm.goto_label in H6. destruct (label_pos l 0 (Asm.fn_code f)) eqn:LBLPOS; inv H6.
    destruct (rs1 Asm.PC) eqn:PC1; inv H4. 
    destruct (Globalenvs.Genv.find_funct_ptr ge b0); inv H5.
    eexists; eexists. split. simpl.
    unfold goto_label. eauto.
    eapply match_states_intro; eauto.
    apply regset_inject_expand; auto. 
    rewrite H in *. inv PC1. inv H.
    eapply agree_inj_lbl; eauto.

  - (* Pjmp_s *)
    repeat destr_in H6.
    destruct ros; simpl in *.
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
    inversion MATCHSMINJ.
    unfold Globalenvs.Genv.symbol_address. destr_match; auto.
    exploit (agree_inj_glob0 i b0); eauto.
    intros (b1 & ofs1 & LBLOFS & JB).
    erewrite Genv.find_sym_to_addr with (ofs:=ofs1); eauto.
    rewrite <- (Ptrofs.add_zero_l ofs1).
    eapply Val.inject_ptr; eauto.
    rewrite Ptrofs.repr_unsigned. auto.

  - (* Pjcc *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c rs1 rs2); eauto.
    intros.
    destr_eval_testcond; try solve_match_states.
    exploit goto_label_inject; eauto. intros (rs2' & GOTO & RINJ' & MINJ').
    exists rs2', m2. split. simpl. rewrite <- H7. auto.
    eapply match_states_intro; eauto.
    assert (m1 = m1') by (eapply goto_label_pres_mem; eauto). subst. auto.

  - (* Pjcc2 *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c1 rs1 rs2); eauto.
    exploit (eval_testcond_inject j c2 rs1 rs2); eauto.
    intros ELF1 ELF2.
    destr_eval_testcond; try solve_match_states.
    exploit goto_label_inject; eauto. intros (rs2' & GOTO & RINJ' & MINJ').
    exists rs2', m2. split. simpl. setoid_rewrite <- H5. setoid_rewrite <- H7. auto.
    eapply match_states_intro; eauto.
    assert (m1 = m1') by (eapply goto_label_pres_mem; eauto). subst. auto.

  - (* Pjmptbl *)
    unfold Asm.exec_instr in H6; simpl in H6.
    destruct (rs1 r) eqn:REQ; inv H6.
    destruct (list_nth_z tbl (Int.unsigned i)) eqn:LEQ; inv H4.
    assert (rs2 r = Vint i) by
        (generalize (RSINJ r); rewrite REQ; inversion 1; auto).
    exploit (goto_tbl_label_inject id tbl l); eauto. 
    intros (rs2' & GLBL & RSINJ' & MINJ').
    exists rs2', m2. split. simpl. setoid_rewrite H3. setoid_rewrite LEQ. auto. 
    eapply match_states_intro; eauto.
    assert (m1 = m1') by (eapply goto_label_pres_mem; eauto). subst. auto.
    
  - (* Pcall_s *)
    repeat destr_in H6.
    generalize (RSINJ PC).
    edestruct storev_mapped_inject' as (m2' & ST & MINJ'). apply MINJ. eauto.
    apply Val.offset_ptr_inject. eauto.
    apply Val.offset_ptr_inject. eauto.
    do 2 eexists; split; eauto. simpl.
    rewrite ST. eauto.
    econstructor; eauto.
    repeat apply regset_inject_expand; auto.
    apply Val.offset_ptr_inject. eauto.
    destruct ros; simpl; repeat apply regset_inject_expand; auto.
    exploit (inject_symbol_address j i Ptrofs.zero); eauto.
    apply Val.offset_ptr_inject. eauto.
    eapply storev_pres_glob_block_valid; eauto.      
  (* - (* Pallocframe *) *)
  (*   generalize (RSINJ RSP). intros RSPINJ. *)
  (*   destruct (Mem.storev Mptr m1 *)
  (*                        (Val.offset_ptr *)
  (*                           (Val.offset_ptr (rs1 RSP) *)
  (*                                           (Ptrofs.neg (Ptrofs.repr (align (frame_size frame) 8)))) *)
  (*                           ofs_ra) (rs1 RA)) eqn:STORERA; try inv H6. *)
  (*   exploit (fun a1 a2 => *)
  (*              storev_mapped_inject' j Mptr m1 a1 (rs1 RA) m1' m2 a2 (rs2 RA)); eauto with inject_db. *)
  (*   intros (m2' & STORERA' & MINJ2). *)
  (*   destruct (rs1 RSP) eqn:RSP1; simpl in *; try congruence. *)
  (*   inv RSPINJ. *)
  (*   eexists; eexists. *)
  (*   (* Find the resulting state *) *)
  (*   rewrite <- H5 in STORERA'. rewrite STORERA'. split. eauto. *)
  (*   (* Solve match states *) *)
  (*   eapply match_states_intro; eauto. *)
  (*   eapply nextinstr_pres_inject; eauto. *)
  (*   repeat eapply regset_inject_expand; eauto. *)
  (*   eapply Val.inject_ptr; eauto. *)
  (*   repeat rewrite (Ptrofs.add_assoc i). *)
  (*   rewrite (Ptrofs.add_commut (Ptrofs.repr delta)). auto. *)
  (*   eapply store_pres_glob_block_valid; eauto. *)

  (* - (* Pfreeframe *) *)
  (*   generalize (RSINJ RSP). intros. *)
  (*   destruct (Mem.loadv Mptr m1 (Val.offset_ptr (rs1 RSP) ofs_ra)) eqn:EQRA; try inv H6. *)
  (*   exploit (fun g a2 => Mem.loadv_inject j g m1' m2 Mptr (Val.offset_ptr (rs1 Asm.RSP) ofs_ra) a2 v); eauto. *)
  (*   apply Val.offset_ptr_inject. auto. *)
  (*   intros (v2 & MLOAD2 & VINJ2). *)
  (*   eexists; eexists. split. simpl. *)
  (*   setoid_rewrite MLOAD2. auto. *)
  (*   eapply match_states_intro; eauto with inject_db. *)

  - repeat destr_in H6. simpl.
    exploit Mem.loadv_inject; eauto. intros (v2 & LD & VI). rewrite LD.
    eexists _, _; split; eauto. econstructor; eauto.
    repeat apply regset_inject_expand; auto.
    apply Val.offset_ptr_inject. eauto.
Qed.

Theorem step_simulation:
  forall S1 t S2,
    RealAsm.step ge S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2',
      FlatAsm.step tge S1' t S2' /\
      match_states S2 S2'.
Proof.
  destruct 1; intros; inv MS.

  - (* Internal step *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst.
    exploit (agree_inj_instr j MATCHSMINJ b b2 f ofs delta i); eauto.
    intros (id & i' & sid & ofs1 & FITARG & FSYMB & TRANSL).
    exploit (exec_instr_step j rs rs'0 m m'0 rs' m' i i' id); eauto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    eapply FlatAsm.exec_step_internal; eauto.
        
  - (* Builtin *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H.
    inversion 1; subst.
    exploit (agree_inj_instr j MATCHSMINJ b b2 f ofs delta (Asm.Pbuiltin ef args res)); auto.
    intros (id & i' & sid & ofs1 & FITARG & FSYMB & TRANSL).
    (* exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst. *)
    monadInv TRANSL. (* monadInv EQ. *)
    set (pbseg := {| segblock_id := sid; segblock_start := Ptrofs.repr ofs1; segblock_size := Ptrofs.repr (instr_size (Pbuiltin ef args res)) |}) in *.
    exploit (eval_builtin_args_inject j m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { 
      unfold match_prog in TRANSF. unfold transf_program in TRANSF.
      repeat destr_in TRANSF. 
      symmetry. eapply transl_prog_pres_senv; eauto.
    }
    generalize (external_call_inject ge j vargs vargs' m m'0 m' vres t ef ARGSINJ MINJ H3).
    rewrite SENVEQ.
    intros (j' & vres2 & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    set (rs' := nextinstr_nf (set_res res vres2 (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0)) (segblock_size pbseg)).
    exploit (fun b ofs => FlatAsm.exec_step_builtin tge id b ofs
                                       ef args res rs'0  m'0 vargs' t vres2 rs' m2' pbseg); eauto. 
    (* unfold valid_instr_offset_is_internal in INSTRINTERNAL. *)
    (* eapply INSTRINTERNAL; eauto. *)
    intros FSTEP. eexists; split; eauto.
    eapply match_states_intro with (j:=j'); eauto.
    (* Supposely the following propreties can proved by separation property of injections *)
    + eapply (inject_pres_match_sminj j); eauto.
    (* + eapply (inject_pres_globs_inj_into_flatmem j); eauto. *)
    + eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
    + eapply (inject_pres_extfun_entry_is_external j); eauto.
    + eapply (inject_pres_match_find_funct j); eauto.
    + subst rs'. intros. subst pbseg; simpl.
      assert (regset_inject j' rs rs'0) by 
          (eapply regset_inject_incr; eauto).
      set (dregs := (map Asm.preg_of (Machregs.destroyed_by_builtin ef))) in *.
      generalize (undef_regs_pres_inject j' rs rs'0 dregs H5). intros.
      set (rs1 := (Asm.undef_regs dregs rs)) in *.
      set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
      generalize (fun h => set_res_pres_inject res j' 
                  rs1 rs2 h vres vres2 RESINJ).
      set (rs3 := (Asm.set_res res vres rs1)) in *.
      set (rs4 := (Asm.set_res res vres2 rs2)) in *.
      intros.
      eauto with inject_db.
    + eapply extcall_pres_glob_block_valid; eauto.

  - (* External call *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst. rewrite Ptrofs.add_zero_l in H6.
    (* exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst. *)
    (* edestruct storev_mapped_inject' as (m2' & SV & INJ2); eauto. *)
    (* apply Val.offset_ptr_inject. eauto. *)
    exploit Mem.loadv_inject. apply MINJ. apply LOADRA. eauto. intros (v2 & LRA & VI).
    edestruct (extcall_arguments_inject) as (args2 & ARGSINJ & EXTCALLARGS); eauto.
    apply regset_inject_expand. eauto.
    apply Val.offset_ptr_inject. eauto.
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { 
      unfold match_prog in TRANSF. unfold transf_program in TRANSF.
      repeat destr_in TRANSF. 
      symmetry. eapply transl_prog_pres_senv; eauto.
    }
    exploit (external_call_inject ge j args args2 ); eauto.
    rewrite SENVEQ.
    
    intros (j' & res' & m2'' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    exploit (fun ofs => FlatAsm.exec_step_external tge b2 ofs ef args2 res'); eauto.
    + intro; subst. inv VI. congruence.
    + intros FSTEP. eexists. split. apply FSTEP.
      eapply match_states_intro with (j := j'); eauto.
      * eapply (inject_pres_match_sminj j); eauto.
      * eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
      * eapply (inject_pres_extfun_entry_is_external j); eauto.
      * eapply (inject_pres_match_find_funct j); eauto.
      * assert (regset_inject j' rs rs'0) by 
            (eapply regset_inject_incr; eauto).
        set (dregs := (map Asm.preg_of Conventions1.destroyed_at_call)) in *.
        generalize (undef_regs_pres_inject j' rs rs'0 dregs H4). intros.
        set (rs1 := (Asm.undef_regs dregs rs)) in *.
        set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
        set (cdregs := (CR Asm.ZF :: CR Asm.CF :: CR Asm.PF :: CR Asm.SF :: CR Asm.OF :: nil)) in *.
        generalize (undef_regs_pres_inject j' rs1 rs2 cdregs). intros.
        set (rs3 := (Asm.undef_regs cdregs rs1)) in *.
        set (rs4 := (Asm.undef_regs cdregs rs2)) in *.
        generalize (set_pair_pres_inject j' rs3 rs4 res res' 
                                         (Asm.loc_external_result (ef_sig ef))).
        intros.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto. eapply val_inject_incr; eauto.
        apply Val.offset_ptr_inject; eauto.
      * eapply extcall_pres_glob_block_valid; eauto.
Qed.        

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Asm.final_state st1 r -> FlatAsm.final_state st2 r.
Proof.
  intros st1 st2 r MATCH FINAL.
  inv FINAL. inv MATCH. constructor. 
  - red in RSINJ. generalize (RSINJ PC). rewrite H. 
    unfold Vnullptr. destruct Archi.ptr64; inversion 1; auto.
  - red in RSINJ. generalize (RSINJ RAX). rewrite H0.
    inversion 1. auto.
Qed.
  
Theorem transf_program_correct:
  forward_simulation (RealAsm.semantics prog (Pregmap.init Vundef)) (FlatAsm.semantics tprog (Pregmap.init Vundef)).
Proof.
  eapply forward_simulation_step with match_states.
  - simpl. intros. 
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    repeat destr_in TRANSF.    
    erewrite transl_prog_pres_senv; eauto. auto.
  - simpl. intros s1 IS. 
    exploit transf_initial_states; eauto.
    intros.
    rewrite Pregmap.gi. auto.
  - simpl. intros s1 s2 r MS FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS. 
    edestruct step_simulation as (STEP' & MS'); eauto.
Qed.

Require Import MCgen.
Arguments is_valid_label_dec: simpl nomatch.

Lemma transl_instrs_id_code:
  forall c i  ii sbb id s i0 x x0,
    FlatAsmgen.transl_instrs i s i0 c = OK (x, x0) ->
    In (ii, sbb, id) x0 ->
    segblock_id sbb = s /\ i = id.
Proof.
  induction c; simpl; intros; eauto.
  inv H. easy.
  monadInv H.
  destruct H0.
  - subst.
    unfold FlatAsmgen.transl_instr in EQ.
    repeat destr_in EQ; simpl; auto.
  - eapply IHc; eauto.
Qed.


Lemma in_transl_globdefs_code:
  forall defs g tdefs i tdef sb,
    FlatAsmgen.transl_globdefs g defs = OK tdefs ->
    In (i, Some tdef, sb) tdefs ->
    exists def,
      In (i, def) defs /\ FlatAsmgen.transl_globdef g i def = OK (i, Some tdef, sb).
Proof.
  induction defs; simpl; intros; eauto.
  - inv H; easy.
  - repeat destr_in H. monadInv H2.
    destruct H0. subst.
    assert (i = i0).
    {
      unfold FlatAsmgen.transl_globdef in EQ. repeat destr_in EQ.
      monadInv H0. auto.
    } subst.
    eexists; split; eauto.
    edestruct IHdefs as (def & IN & FATG); eauto.
Qed.

Lemma transl_fun_id_code:
  forall g i f1 f2 ii sbb id,
    FlatAsmgen.transl_fun g i f1 = OK f2 ->
    In (ii, sbb, id) (fn_code f2) ->
    exists s i0,
      g i = Some (s, i0) /\
      segblock_id sbb = s /\ i = id.
Proof.
  unfold FlatAsmgen.transl_fun.
  intros g i f1 f2 ii sbb id TF IN.
  do 2 destr_in TF. monadInv TF. repeat destr_in EQ0.
  simpl in IN.
  do 2 eexists; split; eauto.
  eapply transl_instrs_id_code; eauto.
Qed.

Lemma transl_instrs_back:
  forall c i  ii sbb id s i0 x x0,
    FlatAsmgen.transl_instrs i s i0 c = OK (x, x0) ->
    In (ii, sbb, id) x0 ->
    exists ofs ii1,
      FlatAsmgen.transl_instr ofs i s ii1 = OK (ii, sbb,id) /\
      In ii1 c.
Proof.
  induction c; simpl; intros; eauto.
  inv H. easy.
  monadInv H.
  destruct H0.
  - subst. eauto.
  - eapply IHc in EQ1; eauto.
    decompose [ex and] EQ1; eauto.
Qed.

Lemma transf_check_faprog:
  wf_prog prog -> check_faprog tprog = true.
Proof.
  destruct 1.
  unfold check_faprog.
  rewrite forallb_forall.
  intros ((i & og) & sb) IN.
  generalize TRANSF. unfold match_prog. 
  unfold FlatAsmgen.transf_program.
  repeat destr.
  unfold transl_prog_with_map. intro A; monadInv A. unfold check_fadef.
  repeat destr.
  simpl in *.
  subst.
  rewrite andb_true_iff; split.
  rewrite forallb_forall.
  - intros ((ii & sbb) & id) INc.
    edestruct in_transl_globdefs_code as (def & INdefs & TG); eauto.
    unfold FlatAsmgen.transl_globdef in TG. repeat destr_in TG.
    monadInv H0.
    exploit transl_fun_id_code. eauto. eauto.
    intros (s & i0 & GID & SBB & IID).
    rewrite SBB, IID.
    apply andb_true_iff; split.
    apply andb_true_iff; split.
    2: apply peq_true.
    eapply update_map_funct' in GID; eauto. simpl in GID. subst. apply peq_true.
    red in wf_prog_valid_labels.
    rewrite Forall_forall in wf_prog_valid_labels.
    specialize (wf_prog_valid_labels _ INdefs).
    simpl in wf_prog_valid_labels.
    red in wf_prog_valid_labels.
    rewrite Forall_forall in wf_prog_valid_labels.
    unfold FlatAsmgen.transl_fun in EQ0.
    rewrite GID in EQ0. monadInv EQ0. repeat destr_in EQ2.
    edestruct transl_instrs_back as (ofs & ii1 & TI & INcode); eauto.
    specialize (wf_prog_valid_labels _ INcode).
    unfold is_valid_label_dec. destr.
    {
      destruct ii1; simpl in TI; repeat destr_in TI.
      simpl in wf_prog_valid_labels.
      specialize (wf_prog_valid_labels _ eq_refl).
      edestruct (update_maps_lmap_in) as (sid & ofs' & LEQ).
      apply wf_prog_norepet_defs. apply INdefs. eauto.
      apply Heqp. unfold proj_sumbool.  destr. rewrite LEQ in n. contradict n. congruence.
    }
    {
      destruct ii1; simpl in TI; repeat destr_in TI.
      simpl in wf_prog_valid_labels.
      specialize (wf_prog_valid_labels _ eq_refl).
      edestruct (update_maps_lmap_in) as (sid & ofs' & LEQ).
      apply wf_prog_norepet_defs. apply INdefs. eauto.
      apply Heqp. unfold proj_sumbool.  destr. rewrite LEQ in n. contradict n. congruence.
    }
    {
      destruct ii1; simpl in TI; repeat destr_in TI.
      simpl in wf_prog_valid_labels.
      specialize (wf_prog_valid_labels _ eq_refl).
      edestruct (update_maps_lmap_in) as (sid & ofs' & LEQ).
      apply wf_prog_norepet_defs. apply INdefs. eauto.
      apply Heqp. unfold proj_sumbool.  destr. rewrite LEQ in n. contradict n. congruence.
    }
    {
      unfold proj_sumbool. destr. contradict n.
      rewrite Forall_forall; intros xx INN.
      destruct ii1; simpl in TI; repeat destr_in TI.
      simpl in wf_prog_valid_labels.
      specialize (wf_prog_valid_labels _ INN).
      edestruct (update_maps_lmap_in) as (sid & ofs' & LEQ).
      apply wf_prog_norepet_defs. apply INdefs. eauto.
      apply Heqp. congruence. 
    }
  - simpl.
    edestruct in_transl_globdefs_code as (def & INdefs & TG); eauto.
    unfold FlatAsmgen.transl_globdef in TG. repeat destr_in TG.
    monadInv H0.
    unfold FlatAsmgen.transl_fun in EQ0.
    repeat destr_in EQ0. monadInv H0. repeat destr_in EQ1.
    simpl.
    unfold get_instr_ptr. unfold Genv.label_to_ptr.
    unfold proj_sumbool; destr. contradict n.
    cut (list_norepet (map (fun '(_, bi, _) => snd (segblock_to_label bi)) x1)). clear.
    induction x1; simpl; intros; eauto. constructor.
    repeat destr. inv H; constructor. rewrite in_map_iff in H2 |- *.
    intros (x0 & EQ & IN). apply H2.
    exists x0. repeat destr.
    apply IHx1. auto.
    exploit transl_instrs_diff_labels. 3: apply EQ0. split; auto.
    etransitivity. 2: eapply transl_instrs_ofs_bound; eauto. apply Ptrofs.unsigned_range.
    apply Ptrofs.unsigned_range.
    assert (Forall (fun s => s = s0) (map (fun i1 => fst (segblock_to_label (snd (fst i1)))) x1)).
    {
      clear - EQ0. revert EQ0.
      generalize (Asm.fn_code f1) (Ptrofs.unsigned i0) x0 x1. clear.
      induction c; simpl; intros; eauto.
      inv EQ0; constructor.
      monadInv EQ0.
      simpl.
      constructor; eauto.
      destruct a; simpl in EQ; inv EQ; simpl; auto.
    }
    revert H.
    clear.
    intros.
    eapply list_map_norepet with (f := snd) in H0.
    rewrite map_map in H0. erewrite map_ext. apply H0.
    intros. repeat destr.
    intros.
    rewrite in_map_iff in H1, H2.
    destruct H1 as (y1 & EQ1 & IN1).
    destruct H2 as (y2 & EQ2 & IN2).
    subst.
    intro EQ.
    rewrite Forall_forall in H.
    generalize (H (fst (segblock_to_label (snd (fst y1))))).
    generalize (H (fst (segblock_to_label (snd (fst y2))))).
    intros A B.
    trim A. apply in_map_iff. eexists; split; eauto.
    trim B. apply in_map_iff. eexists; split; eauto.
    subst.
    apply H3.
    rewrite (surjective_pairing (segblock_to_label (snd (fst y1)))).
    rewrite (surjective_pairing (segblock_to_label (snd (fst y2)))).
    rewrite B, EQ. reflexivity.
Qed.

End PRESERVATION.


End WITHMEMORYMODEL.