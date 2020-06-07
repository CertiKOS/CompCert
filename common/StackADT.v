Require Import Coqlib.
Require Import MemPerm.
Require Import Memdata.
Require Import AST.
Require Import Values.
Require Export Assoc.
Require Intv.

Local Open Scope nat_scope.

(* To be moved to Coqlib *)
Definition option_prop {A} (P: A -> Prop) (oa: option A): Prop :=
  match oa with
    Some a => P a
  | None => True
  end.

Definition option_prop2 {A} (P: A -> A -> Prop) (oa ob: option A): Prop :=
  match oa, ob with
    Some a, Some b => P a b
  | Some a, None => False
  | _, _ => True
  end.


(** This file holds definitions related to our stack abstract data type (ADT).   *)

(** * Block information  *)

(** A block information records its size ([frame_size]) and the stack
    permissions for each offset of that block in [frame_perm]. *)

Record frame_info :=
  {
    frame_size: Z;
    frame_size_pos: (0 <= frame_size)%Z;
  }.

Definition default_frame_info sz : frame_info :=
  {|
    frame_size := Z.max 0 sz;
    frame_size_pos := Z.le_max_l _ _;
  |}.

Program Definition empty_frame: frame_info :=
  {|
    frame_size := 0;
  |}.

(** * Frame ADT  *)

(** A frame ADT records a list of blocks [frame_adt_blocks] and the size of the
    frame [frame_adt_size]. This size is _not_ the cumulated size of the blocks,
    but rather the stack space that will be necessary for the corresponding
    concrete frame down at the Mach and assembly languages. This size will match
    the size of the stack blocks in those low-level languages and will be used
    to construct the injection from the separate assembly blocks for every
    function to the continuous single stack in [RawAsm]. *)

Record frame_adt : Type :=
  {
    frame_adt_blocks: list (block * frame_info);
    frame_adt_size : Z;
    frame_adt_blocks_norepet:
      list_norepet (map fst frame_adt_blocks);
    frame_adt_size_pos:
      (0 <= frame_adt_size)%Z;
  }.

(** * Tailcall frames *)

(** Tailcall frames are non-empty lists of [frame_adt]s. In most cases this list will be a
    singleton. When a tailcall is performed though, instead of popping the frame
    of the tail-caller and pushing the frame of the tailcalled function, we will
    append the frame of the tailcalled function to the current list. In this
    way, we record some form of history of the frames, enabling us to reason
    finely about tailcalls. *)

Definition tframe_adt := (option frame_adt * list frame_adt)%type.

(** * Stack ADT  *)

(** Finally, the stack itself is a list of tailcall frames.  *)

Definition stack := list tframe_adt.

(** Blocks belonging to frames, tframes, stacks.  *)

Definition get_frame_blocks (f: frame_adt) : list block :=
  map fst (frame_adt_blocks f).

Definition get_opt_frame_blocks (of: option frame_adt) : list block :=
  match of with
  | None => nil
  | Some f => get_frame_blocks f
  end.

Definition get_frames_blocks (tf: tframe_adt) : list block :=
  get_opt_frame_blocks (fst tf).  (* ++ concat (map get_frame_blocks (snd tf)). *)

Definition get_stack_blocks (s: stack) : list block :=
  concat (map get_frames_blocks s).

Definition in_frame (f: frame_adt) (b: block) : Prop :=
  In b (get_frame_blocks f).

(* In top tailcall stage of tailcall frame *)
Definition in_frames (l: tframe_adt) (b: block) :=
  In b (get_opt_frame_blocks (fst l)).

(* In some top tailcall stage of some taillcall frame in stack *)
Definition in_stack (s: stack) (b: block) :=
  In b (get_stack_blocks s).

Definition in_frame' (f: frame_adt) bfi :=
  In bfi (frame_adt_blocks f).

Definition in_frames' (tf: tframe_adt) bfi :=
  match fst tf with
  | Some f => in_frame' f bfi
  | None => False
  end.

Fixpoint in_stack' (s: stack) bfi :=
  match s with
  | nil => False
  | tf::s => in_frames' tf bfi \/ in_stack' s bfi
  end.

Lemma in_frames'_rew:
  forall tf bfi,
    in_frames' tf bfi <->
    exists fr, in_frame' fr bfi /\ fst tf = Some fr.
Proof.
  unfold in_frames'. intros.
  destr; split; intros A; try decompose [ex and] A; try (intuition congruence);
    eexists; eauto.
Qed.

Lemma in_stack'_rew:
  forall s bfi,
    in_stack' s bfi <->
    exists (tf: tframe_adt),
      in_frames' tf bfi /\ In tf s.
Proof.
  induction s; simpl; split; intros; eauto.
  - easy.
  - decompose [ex and] H; easy.
  - destruct H; eauto. rewrite IHs in H.
    decompose [ex and] H; eauto.
  - rewrite IHs.
    decompose [ex and] H; eauto. destruct H2; subst; eauto.
Qed.

Lemma in_frame_dec:
  forall f b, {in_frame f b} + {~ in_frame f b}.
Proof.
  intros; apply in_dec, eq_block.
Defined.

Hint Resolve in_frame_dec.

Lemma in_frames_dec:
  forall l b, {in_frames l b} + {~ in_frames l b}.
Proof.
  intros; apply in_dec, eq_block.
Defined.

Hint Resolve in_frames_dec.

Lemma in_stack_dec:
  forall l b, {in_stack l b} + {~ in_stack l b}.
Proof.
  intros; apply in_dec, eq_block.
Defined.

Hint Resolve in_stack_dec.

Lemma in_stack_cons:
  forall a r b,
    in_stack (a::r) b <-> in_frames a b \/ in_stack r b.
Proof.
  unfold in_stack,in_frames.
  unfold get_stack_blocks.
  simpl.
  intros a r b. rewrite in_app. tauto.
Qed.

Lemma in_frames_cons:
  forall a r b,
    in_frames (a,r) b <-> (exists fa, a = Some fa /\ in_frame fa b).
Proof.
  unfold in_frames,in_frame.
  simpl. intuition.
  destruct a; simpl in *. eauto. easy.
  destruct H as (fa & EQ & IN); subst; eauto.
Qed.

Lemma in_stack_app:
  forall l1 l2 b,
    in_stack l1 b \/ in_stack l2 b <->
    in_stack (l1 ++ l2) b.
Proof.
  intros.
  unfold in_stack, get_stack_blocks in *.
  rewrite map_app, concat_app, in_app; tauto.
Qed.

Lemma in_frame_info:
  forall b (f: frame_adt),
    in_frame f b ->
    exists fi,
      In (b,fi) (frame_adt_blocks f).
Proof.
  unfold in_frame, get_frame_blocks. intros b f.
  rewrite in_map_iff. intros ((bb & fi) & EQ & IN). simpl in *. subst.
  eauto.
Qed.

(** Fetching the frame information associated with a specific block. *)

Definition get_assoc_tframes (l: tframe_adt) (b: block) : option frame_info :=
  match fst l with
    Some fr =>
    if in_frame_dec fr b then
      get_assoc _ _ peq (frame_adt_blocks fr) b
    else None
  | _ => None
  end.

Fixpoint get_assoc_stack (l: stack) (b: block) : option frame_info :=
  match l with
    nil => None
  | lfr::r => if in_frames_dec lfr b then
              get_assoc_tframes lfr b
            else get_assoc_stack r b
  end.

Lemma not_in_stack_get_assoc:
  forall l b,
    ~ in_stack l b ->
    get_assoc_stack l b = None.
Proof.
  induction l; simpl; intros; eauto.
  rewrite in_stack_cons in H.
  repeat destr. eauto.
Qed.

Definition get_frame_info s : block -> option frame_info :=
  get_assoc_stack s.

(** * Injection of frame information  *)

Definition inject_frame_info delta fi fi' := forall o, (0 <= o < frame_size fi -> 0 <= o + delta < frame_size fi')%Z.

Lemma inject_frame_info_id:
  forall f,
    inject_frame_info 0 f f.
Proof.
  constructor; intros; omega.
Qed.

Hint Resolve inject_frame_info_id.

Lemma inject_frame_info_trans:
  forall f1 f2 f3 delta1 delta2,
    inject_frame_info delta1 f1 f2 ->
    inject_frame_info delta2 f2 f3 ->
    inject_frame_info (delta1 + delta2) f1 f3.
Proof.
  intros f1 f2 f3 delta1 delta2 A B; unfold inject_frame_info in A, B; constructor; apply A in H; apply B in H;
    rewrite Z.add_assoc; destruct H; eauto.
Qed.

Hint Resolve inject_frame_info_trans.

(** * Injection of frame_adt  *)

Definition frame_inject (f: meminj) (f1 f2: frame_adt) :=
  Forall
    (fun bfi =>
       forall b2 delta,
         f (fst bfi) = Some (b2, delta) ->
         exists fi',
           In (b2, fi') (frame_adt_blocks f2) /\
           inject_frame_info delta (snd bfi) fi'
    )
    (frame_adt_blocks f1).

Lemma self_frame_inject f a:
  (forall b, f b = None \/ f b = Some (b,0)%Z) ->
  frame_inject f a a.
Proof.
  intros SELF.
  destruct a.
  apply Forall_forall; intros. destruct x. simpl in *.
  intros.
  destruct (SELF b); try congruence.
  rewrite H1 in H0; inv H0. eauto.
Qed.

Lemma frame_inject_id a:
  frame_inject inject_id a a.
Proof.
  apply self_frame_inject. right; reflexivity.
Qed.

Ltac injincrtac:=
  match goal with
    INCR: inject_incr ?f ?f',
          H: ?f' ?b = Some _,
             NEW: forall _ _ _, ?f _ = None -> ?f' _ = Some _ -> _ |- _ =>
    let b' := fresh "b'" in
    let delta := fresh "delta" in
    let FB := fresh "FB" in
    destruct (f b) as [[b' delta]|] eqn:FB;
    [ generalize (INCR _ _ _ FB); rewrite H;
      let A := fresh in intro A; inv A
    | generalize (NEW _ _ _ FB H)
    ]
  end.

Lemma frame_inject_incr:
  forall f f' f1 f2,
    inject_incr f f' ->
    (forall b b' delta,
        f b = None ->
        f' b = Some (b', delta) ->
        ~ in_frame f1 b) ->
    frame_inject f f1 f2 ->
    frame_inject f' f1 f2.
Proof.
  intros.
  unfold frame_inject in *.
  eapply Forall_impl; eauto.
  simpl. destruct f1. simpl.
  destruct a. simpl.
  intros IN ASSOC b2 delta F'B.
  injincrtac; autospe; eauto.
  intro NIN; contradict NIN.
  unfold in_frame, get_frame_blocks. simpl.
  rewrite in_map_iff. exists (b,f0); split; auto.
Qed.

Lemma frame_inject_in_frame:
  forall f v1 v2 b b' delta,
    frame_inject f v1 v2 ->
    in_frame v1 b ->
    f b = Some (b', delta) ->
    in_frame v2 b'.
Proof.
  unfold frame_inject. intros f v1 v2 b b' delta FI INF FB.
  rewrite Forall_forall in FI.
  red in INF. 
  setoid_rewrite in_map_iff in INF. destruct INF as ((b0 & f0) & EQ & IN). simpl in *; subst.
  specialize (FI _ IN). simpl in FI.
  specialize (FI _ _ FB).
  destruct FI as (fi' & ASSOC & SF).
  red. auto. apply in_map_iff. eexists; split; eauto. reflexivity.
Qed.

Lemma frame_inject_compose:
  forall (f f' : meminj) l1 l2
    (FI12: frame_inject f l1 l2)
    l3
    (FI23: frame_inject f' l2 l3),
    frame_inject (compose_meminj f f') l1 l3.
Proof.
  intros.
  unfold frame_inject in *.
  unfold compose_meminj.
  rewrite Forall_forall in *. intros (b1&fi1) IN b2 delta F.
  repeat destr_in F.
  specialize (FI12 _ IN _ _ Heqo).
  destruct FI12 as (fi2 & INL2 & IFI12).
  simpl in *. 
  specialize (FI23 _ INL2 _ _ Heqo0).
  destruct FI23 as (fi3 & INL3 & IFI23).
  eexists; split; eauto.
Qed.

Lemma in_frame_in_frames:
  forall f tf b,
    in_frame f b ->
    fst tf = Some f ->
    in_frames tf b.
Proof.
  unfold in_frames, get_frames_blocks.
  simpl. intros. rewrite H0. simpl. auto.
Qed.

Definition perm_type :=
  block -> Z -> perm_kind -> permission -> Prop.

(** * Consistency between permissions and frame size  *)

Definition frame_agree_perms (P: perm_type) (f: frame_adt) : Prop :=
  forall b fi o k p,
    In (b,fi) (frame_adt_blocks f) -> 
    P b o k p ->
    (0 <= o < frame_size fi)%Z.

Definition stack_agree_perms m (s: stack) :=
  forall tf,
    In tf s ->
    forall f,
      fst tf = Some f ->
      frame_agree_perms m f.

(** * Finding a frame at a given position  *)

Inductive frame_at_pos (s: stack) n f :=
| frame_at_pos_intro:
    nth_error s n = Some f -> frame_at_pos s n f.

Notation "f '@' s ':' i" := (frame_at_pos s i f) (at level 30, s at next level, i at next level, no associativity).

Lemma frame_at_pos_lt:
  forall s n f,
    f @ s : n ->
    n < length s.
Proof.
  intros s n f FAP; inv FAP.
  apply nth_error_Some. congruence.
Qed.

Lemma in_frame_at_pos:
  forall s f,
    In f s ->
    exists n, f @ s : n.
Proof.
  intros s f IN; apply In_nth_error in IN; destruct IN as (n & NTH).
  exists n; econstructor; eauto.
Qed.

Lemma frame_at_pos_In:
  forall s f n,
    f @ s : n ->
    In f s.
Proof.
  intros s f n FAP; inv FAP. eapply nth_error_In; eauto. 
Qed.

Lemma frame_at_same_pos:
  forall s n f1 f2,
    f1 @ s : n ->
    f2 @ s : n ->
    f1 = f2.
Proof.
  intros s n f1 f2 FAP1 FAP2; inv FAP1; inv FAP2; congruence.
Qed.

(** * Stack injection  *)

Definition frameinj := list nat.

Section TAKEDROP.
  Context {A: Type}.

  Fixpoint take (n: nat) (l: list A) : option (list A) :=
    match n with
    | O => Some nil
    | S m => match l with
            | h::t =>
               match take m t with
                 Some r => Some (h::r)
               | None => None
               end
            | _ => None
            end
    end.

  Fixpoint drop (n: nat) (l: list A) : list A :=
    match n with
    | O => l
    | S m => drop m (tl l)
    end.

  Lemma take_drop:
    forall n l t,
      take n l = Some t ->
      l = t ++ drop n l.
  Proof.
    induction n; simpl; intros; eauto. inv H. reflexivity.
    repeat destr_in H. simpl. f_equal. eauto.
  Qed.

  Lemma take_succeeds:
    forall n l,
      n <= length l ->
      exists t, take n l = Some t.
  Proof.
    induction n; simpl; intros; eauto.
    destr; simpl in *. omega.
    edestruct (IHn l0) as (t & EQ). omega.
    rewrite EQ. eauto.
  Qed.

  Lemma take_succeeds_inv:
    forall n l t,
      take n l = Some t ->
      n <= length l.
  Proof.
    induction n; simpl; intros; eauto. omega.
    repeat destr_in H.
    apply IHn in Heqo. simpl. omega.
  Qed.

  Lemma drop_length:
    forall n l,
      n <= length l ->
      length (drop n l) = length l - n.
  Proof.
    induction n; simpl; intros; eauto. omega.
    destruct l; simpl in *; try omega.
    rewrite IHn; omega.
  Qed.

  Lemma take_length:
    forall n l t,
      take n l = Some t ->
      length t = n.
  Proof.
    induction n; simpl; intros; eauto. inv H; auto.
    repeat destr_in H. simpl. erewrite IHn; eauto.
  Qed.

  Variable P: A -> Prop.

  Lemma take_forall:
    forall n l t,
      Forall P l ->
      take n l = Some t ->
      Forall P t.
  Proof.
    intros.
    rewrite (take_drop _ _ _ H0) in H.
    rewrite Forall_forall in H.
    rewrite Forall_forall. intros; apply H. rewrite in_app. auto.
  Qed.

  Lemma drop_forall:
    forall n l,
      Forall P l ->
      Forall P (drop n l).
  Proof.
    induction n; simpl; intros; eauto.
    apply IHn. inv H; simpl; auto.
  Qed.

End TAKEDROP.

Definition sum_list (l: list nat) : nat :=
  fold_right Peano.plus O l.

Fixpoint compose_frameinj (g g': frameinj): option frameinj :=
  match g' with
  | nil => Some nil
  | n::g' => match take n g with
            | Some t =>
              match compose_frameinj (drop n g) g' with
                Some r => Some (sum_list t :: r)
              | None => None
              end
            | None => None
            end
  end.

Lemma compose_frameinj_succeeds:
  forall g2 g1,
    sum_list g2 = length g1 ->
    exists g3, compose_frameinj g1 g2 = Some g3.
Proof.
  induction g2; simpl; intros; eauto.
  edestruct (take_succeeds a g1) as (t & EQ). omega. rewrite EQ.
  edestruct IHg2 as (g3 & EQ'). 2: rewrite EQ'.
  rewrite drop_length; omega. eauto.
Qed.

(** * Monotonicity of frame injections  *)

Definition flat_frameinj thr : frameinj := list_repeat thr 1.

Definition get_stack_top_blocks (s: stack) : list block :=
  match s with
    nil => nil
  | tf::r => get_frames_blocks tf
  end.

Definition is_stack_top s (b: block) :=
  In b (get_stack_top_blocks s).

Lemma stack_top_frame_at_position:
  forall s b,
    is_stack_top s b ->
    exists f, f @ s : 0 /\ in_frames f b.
Proof.
  destruct s; simpl; intros. easy.
  red in H. simpl in H.
  exists t; split.
  econstructor. simpl. auto.
  auto.
Qed.

Lemma frame_at_position_stack_top:
  forall s f b,
    f @ s : O ->
    in_frames f b ->
    is_stack_top s b.
Proof.
  destruct s; simpl; intros. inv H. simpl in H1. congruence.
  inv H. simpl in H1.
  inv H1. simpl; auto.
Qed.

Lemma is_stack_top_in_stack:
  forall s b,
    is_stack_top s b -> in_stack s b.
Proof.
  intros s b IS.
  destruct s; simpl in *. easy. red in IS; simpl in IS.
  rewrite in_stack_cons; left. eauto.
Qed.

(** * Specifying tailcalled frames.  *)
(** A tframe is a non-empty list of frames (a::l). It must be the case that all
    blocks in l have no permission.
 *)

Definition wf_tframe (m: perm_type) (tf: tframe_adt) : Prop :=
  forall b,
    forall f,
      In f (snd tf) ->
      in_frame f b ->
      forall o k p,
        ~ m b o k p.

Definition wf_stack (m: perm_type) (s: stack) : Prop :=
  Forall (wf_tframe m) s.

Section INJ.
   Definition has_perm (m: perm_type) (j: meminj) (f: tframe_adt) : Prop :=
     exists b o k p, j b <> None /\ in_frames f b /\ m b o k p.

   Definition has_perm_frame (m: perm_type) (j: meminj) (f: frame_adt) : Prop :=
     exists b o k p, j b <> None /\ in_frame f b /\ m b o k p.

   Definition tframe_inject (f: meminj) (P: perm_type) (tf1 tf2: tframe_adt): Prop :=
     forall f1,
       fst tf1 = Some f1 ->
       has_perm_frame P f f1 ->
       exists f2, fst tf2 = Some f2 /\ frame_inject f f1 f2.

   Lemma self_tframe_inject f P a:
     (forall b, f b = None \/ f b = Some (b,0)%Z) ->
     tframe_inject f P a a.
   Proof.
     intros SELF.
     red; intros. exists f1; split; auto.
     apply self_frame_inject; auto.
   Qed.

   Lemma tframe_inject_id P a:
     tframe_inject inject_id P a a.
   Proof.
     apply self_tframe_inject. right. reflexivity.
   Qed.

   Lemma tframe_inject_incr:
     forall P f f' f1 f2,
       inject_incr f f' ->
       (forall b b' delta,
           f b = None ->
           f' b = Some (b', delta) ->
           ~ in_frames f1 b) ->
       tframe_inject f P f1 f2 ->
       tframe_inject f' P f1 f2.
   Proof.
     intros P f f' f1 f2 INCR NEW TF ff1 IN1 (b & o & k & p & Fnone & IFR & PERM).
     edestruct TF as (f0 & IN & FI); eauto.
     - red.
       repeat eexists; eauto.
       destruct (f' b) eqn:?; try congruence. destruct p0.
       intro. eapply NEW in Heqo0; eauto. exfalso; apply Heqo0.
       eapply in_frame_in_frames; eauto.
     - eexists; split; eauto.
       eapply frame_inject_incr; eauto.
       intros b0 b' delta NONE SOME IFR0; eapply NEW; eauto.
       eapply in_frame_in_frames; eauto.
   Qed.

   Lemma tframe_inject_compose:
     forall (f f' : meminj) P P' l1 l2
       (FI12: tframe_inject f P l1 l2)
       l3
       (FI23: tframe_inject f' P' l2 l3)
       (PERMS: forall b1 b2 delta o k p,
           f b1 = Some (b2, delta) ->
           P b1 o k p ->
           P' b2 (o + delta)%Z k p),
       tframe_inject (compose_meminj f f') P l1 l3.
   Proof.
     intros f f' P P' l1 l2 FI12 l3 FI23 PERMS
            f1 INf1 (b & o & k & p & JB & IFR & PERM).
     unfold compose_meminj in JB; repeat destr_in JB. subst.
     edestruct FI12 as (f2 & INl2 & FI12'); eauto.
     repeat eexists; eauto. congruence.
     edestruct FI23 as (f3 & INl3 & FI23'); eauto.
     repeat eexists; eauto. congruence.
     eapply frame_inject_in_frame; eauto.
     eexists; split; eauto.
     eapply frame_inject_compose; eauto.
   Qed.

   Inductive stack_inject (f: meminj) (m: perm_type) : frameinj -> stack -> stack -> Prop :=
   | stack_inject_intro:
       stack_inject f m nil nil nil
   | stack_inject_cons
       n g s1 hs1 ts1 tf ts2
       (TAKE: take (S n) s1 = Some hs1)
       (DROP: drop (S n) s1 = ts1)
       (SIA_REC: stack_inject f m g ts1 ts2)
       (FI: Forall (fun f1 => tframe_inject f m f1 tf) hs1):
     stack_inject f m (S n::g) s1 (tf::ts2).

   Lemma stack_inject_length_l:
     forall f m g s1 s2,
       stack_inject f m g s1 s2 ->
       sum_list g = length s1.
   Proof.
     induction 1; simpl; intros; eauto.
     rewrite (take_drop _ _ _ TAKE). subst.
     rewrite IHstack_inject. rewrite app_length.
     f_equal. symmetry.
     erewrite take_length by eauto. omega.
   Qed.

   Lemma stack_inject_length_r:
     forall f m g s1 s2,
       stack_inject f m g s1 s2 ->
       length g = length s2.
   Proof.
     induction 1; simpl; intros; eauto.
   Qed.

  Close Scope nat_scope.

  Lemma stack_inject_flat:
    forall s P f (F: forall b, f b = None \/ f b = Some (b, 0)),
     stack_inject f P (flat_frameinj (length s)) s s.
  Proof.
    induction s; simpl; intros.
    constructor.
    simpl. econstructor. reflexivity. reflexivity. simpl. eauto.
    repeat constructor.
    apply self_tframe_inject; auto.
  Qed.

  Open Scope nat_scope.

  Lemma concat_In:
    forall {A} (l: list (list A)) b,
      In b (concat l) <->
      exists x, In b x /\ In x l.
  Proof.
    induction l; simpl; intros; eauto.
    split. easy. intros (x & AA & B); auto.
    rewrite in_app, IHl.
    split.
    intros [B|(x & B & C)]; eauto.
    intros (x & B & [C|C]); subst; eauto.
  Qed.

  Lemma in_stack'_app:
    forall s1 s2 b,
      in_stack' (s1 ++ s2) b <-> in_stack' s1 b \/ in_stack' s2 b.
  Proof.
    induction s1; simpl; intros; eauto.
    tauto.
    rewrite IHs1. tauto.
  Qed.

  Lemma in_frame'_in_frame:
    forall b1 bi1 fr1,
      in_frame' fr1 (b1, bi1) -> in_frame fr1 b1.
  Proof.
    intros. red in H. eapply in_map with (f:= fst) in H. auto.
  Qed.

  Lemma wf_stack_drop:
    forall P n s,
      wf_stack P s ->
      wf_stack P (drop n s).
  Proof.
    induction n; simpl; intros; eauto.
    apply IHn.
    inv H; simpl. constructor. auto.
  Qed.

  Lemma stack_inject_compat:
    forall f g P s1 s2,
      stack_inject f P g s1 s2 ->
    forall b1 b2 delta bi1,
      f b1 = Some (b2, delta) ->
      in_stack' s1 (b1, bi1) ->
      (exists o k p, P b1 o k p) ->
      exists bi2,
        in_stack' s2 (b2, bi2) /\ inject_frame_info delta bi1 bi2.
  Proof.
    intros f g P s1 s2 SI.
    revert SI.
    induction 1; simpl; intros b1 b2 delta bi1 FB INS PERM.
    - easy.
    - subst.
      destruct PERM as (o & k & p & PERM).
      rewrite (take_drop _ _ _ TAKE) in INS.
      rewrite in_stack'_app in INS.
      destruct INS as [INS|INS].
      + rewrite in_stack'_rew in INS.
        destruct INS as (tf1 & INFRS & INS).
        rewrite Forall_forall in FI. specialize (FI _ INS).
        red in FI.
        rewrite in_frames'_rew in INFRS. destruct INFRS as (fr & INFR & INFRS).
        specialize (FI _ INFRS).
        trim FI. red. exists b1, o, k, p; repeat apply conj; auto. congruence.
        eapply in_frame'_in_frame; eauto.
        destruct FI as (f2 & INTF & FI).
        red in FI. rewrite Forall_forall in FI.
        specialize (FI _ INFR). simpl in FI.
        specialize (FI _ _ FB).
        destruct FI as (bi2 & INfr2 & IFI).
        exists bi2; split; auto. left; rewrite in_frames'_rew.
        eexists; split; eauto.
      + edestruct IHSI as (bi2 & INS2 & IFI); eauto.
  Qed.

  Lemma stack_top_in_frames:
    forall s b,
      is_stack_top s b ->
      exists f,
        in_frames f b /\ In f s.
  Proof.
    unfold is_stack_top; destruct s; simpl; intros. easy.
    exists t; split; auto.
  Qed.

  Lemma in_frames_in_stack:
    forall s f b,
      In f s ->
      in_frames f b ->
      in_stack s b.
  Proof.
    induction s; simpl; intros; eauto.
    rewrite in_stack_cons.
    destruct H. subst. auto.
    eapply IHs in H; eauto.
  Qed.

  Lemma tframe_inject_in_frames:
    forall f m v1 v2 b b' delta o k p,
      tframe_inject f m v1 v2 -> m b o k p -> in_frames v1 b -> f b = Some (b', delta) -> in_frames v2 b'.
  Proof.
    intros f m v1 v2 b b' delta o k p TFI PERM IFR FB.
    red in IFR. unfold get_opt_frame_blocks in IFR.
    destr_in IFR; try easy. unfold get_frame_blocks in IFR.
    rewrite in_map_iff in IFR. destruct IFR as (fa & blocks & IN). subst.
    specialize (TFI _ Heqo0).
    trim TFI.
    repeat eexists; eauto. congruence. red. unfold get_frame_blocks.
    apply in_map. auto.
    destruct TFI as (f2 & IN2 & FI12).
    eapply in_frame_in_frames; eauto.
    eapply frame_inject_in_frame; eauto.
    red. apply in_map. auto.
  Qed.

  Lemma stack_inject_is_stack_top:
    forall f g m s1 s2,
      stack_inject f m g s1 s2 ->
      forall b1 b2 delta,
        f b1 = Some (b2, delta) ->
        (exists o k p, m b1 o k p) ->
        is_stack_top s1 b1 ->
        is_stack_top s2 b2.
  Proof.
    intros f g m s1 s2 SI b1 b2 delta FB PERM IST.
    destruct (stack_top_frame_at_position _ _ IST) as (ff & FAP1 & IFR1).
    destruct s1. inv FAP1. simpl in *. congruence.
    inv SI.
    eapply frame_at_position_stack_top; eauto.
    constructor. reflexivity.
    inv FAP1. inv H.
    simpl in TAKE. destr_in TAKE. inv TAKE. inv FI.
    destruct PERM as (o & k & p & PERM).
    eapply tframe_inject_in_frames; eauto.
  Qed.

  Lemma in_stack_in_frames_ex:
    forall s b,
      in_stack s b ->
      exists f, In f s /\ in_frames f b.
  Proof.
    induction s; simpl; intros; eauto. easy.
    rewrite in_stack_cons in H. destruct H.
    exists a; eauto.
    edestruct IHs as (x & A & B); eauto.
  Qed.

  Lemma frame_at_pos_ex:
    forall i s,
      i < length s ->
      exists f,
        f @ s : i.
  Proof.
    intros.
    rewrite <- nth_error_Some in H.
    destruct (nth_error s i) eqn:?; try congruence.
    repeat econstructor; eauto.
  Qed.

  Inductive nodup: stack -> Prop :=
  | nodup_nil:
      nodup nil
  | nodup_cons:
      forall f s,
        nodup s ->
        (forall b, in_frames f b -> ~ in_stack s b) ->
        nodup (f::s).

  Definition nodup' (s: stack) :=
    forall b f1 f2,
      In f1 s ->
      In f2 s ->
      in_frames f1 b ->
      in_frames f2 b ->
      f1 = f2.

  Lemma nodup_nodup': forall l, nodup l -> nodup' l.
  Proof.
    induction l; simpl; intros; eauto.
    red; intros; easy.
    red; intros.
    simpl in *.
    destruct H0.
    - destruct H1. congruence.
      subst.
      inv H.
      exfalso; eapply H6. eauto. eapply in_frames_in_stack. eauto. eauto.
    - destruct H1. 
      subst.
      inv H.
      exfalso; eapply H6. eauto. eapply in_frames_in_stack; eauto.
      inv H. eapply IHl; eauto.
  Qed.

  Lemma in_frames_in_frame_ex:
    forall tf b,
      in_frames tf b ->
      exists f,
        fst tf = Some f /\ in_frame f b.
  Proof.
    intros; rewrite <- in_frames_cons. erewrite <- surjective_pairing; eauto.
  Qed.

  Lemma get_assoc_tframes_in :
    forall l b r,
      get_assoc_tframes l b = Some r ->
      exists f,
        fst l = Some f /\ In (b,r) (frame_adt_blocks f).
  Proof.
    destruct l; simpl. destruct o; simpl; try easy.
    cbn. intros b r. destr. intro H; eapply get_assoc_in in H.
    eauto.
  Qed.

  Lemma get_assoc_stack_In:
    forall s b fi,
      get_assoc_stack s b = Some fi ->
      exists f tf, fst tf = Some f /\ In (b,fi) (frame_adt_blocks f) /\ In tf s.
  Proof.
    induction s; simpl; intros; eauto.
    congruence.
    destr_in H.
    - apply get_assoc_tframes_in in H.
      destruct H as (f & IN1 & IN2). exists f, a; split; eauto.
    - edestruct IHs as (f & tf & AIN & IN1 & IN2); eauto.
      exists f, tf; split; eauto.
  Qed.

  Lemma in_frame_blocks_in_frame:
    forall b fi fr
      (IN : In (b, fi) (frame_adt_blocks fr)),
      in_frame fr b.
  Proof.
    intros; setoid_rewrite in_map_iff; eexists; split; eauto. reflexivity.
  Qed.

  Lemma in_get_assoc_tframes:
    forall tf f b fi
      (NTH : fst tf = Some f)
      (IN : In (b, fi) (frame_adt_blocks f)),
      get_assoc_tframes tf b = Some fi.
  Proof.
    intros. unfold get_assoc_tframes.
    rewrite NTH.
    rewrite pred_dec_true.
    apply in_lnr_get_assoc. destruct f; auto. auto.
    eapply in_frame_blocks_in_frame; eauto.
  Qed.

  Lemma get_assoc_stack_lnr:
    forall s b tf fi f
      (NTH: fst tf = Some f)
      (IN: In (b,fi) (frame_adt_blocks f))
      (ND: nodup s)
      (INS: In tf s),
      get_assoc_stack s b = Some fi.
  Proof.
    induction s; simpl; intros; eauto.
    easy.
    destruct INS; subst.
    - rewrite pred_dec_true.
      eapply in_get_assoc_tframes; eauto.
      eapply in_frame_in_frames; eauto.
      eapply in_frame_blocks_in_frame; eauto.
    - rewrite pred_dec_false.
      eapply IHs; eauto.
      inv ND; auto.
      intro IFR; inv ND.
      apply H3 in IFR.
      apply IFR.
      eapply in_frames_in_stack; eauto.
      eapply in_frame_in_frames; eauto.
      eapply in_frame_blocks_in_frame; eauto.
  Qed.

  Lemma wf_stack_in_frames_in_frame:
    forall s,
      forall f1 b,
        In f1 s ->
        in_frames f1 b ->
        exists vf1,
          fst f1 = Some vf1 /\
          in_frame vf1 b.
  Proof.
    intros s f1 b INS INF.
    destruct f1. destruct o; try easy. cbn in INF.
    eexists; split. reflexivity.
    auto.
  Qed.

  Lemma nodup_block_info:
    forall b bi1 bi2 f,
      In (b,bi1) (frame_adt_blocks f) ->
      In (b,bi2) (frame_adt_blocks f) ->
      bi1 = bi2.
  Proof.
    intros.
    destruct f. simpl in *.
    revert frame_adt_blocks_norepet0 H H0.
    generalize frame_adt_blocks0 as l.
    clear.
    induction l; simpl; intros LNR IN1 IN2; eauto.
    easy.
    inv LNR; trim IHl; eauto.
    destruct IN1,IN2; subst; auto.
    congruence.
    simpl in *.
    elim H1. apply in_map_iff; eexists; split; eauto. reflexivity.
    simpl in *.
    elim H1. apply in_map_iff; eexists; split; eauto. reflexivity.
  Qed.

  Lemma in_stack'_stack_agree_perms:
    forall m2 l2 b2 bi2,
      in_stack' l2 (b2, bi2) ->
      stack_agree_perms m2 l2 ->
      forall o k p, m2 b2 o k p -> (0 <= o < frame_size bi2)%Z.
  Proof.
    intros.
    rewrite in_stack'_rew in H.
    destruct H as (tf & IFR & IN).
    rewrite in_frames'_rew in IFR.
    destruct IFR as (fr & IFR & INTF).
    eapply H0; eauto.
  Qed.

  Lemma in_frame'_norepet:
    forall b bi1 bi2 f,
      in_frame' f (b, bi1) ->
      in_frame' f (b, bi2) ->
      bi1 = bi2.
  Proof.
    unfold in_frame'.
    intros b bi1 bi2 f.
    destruct f. simpl in *.
    revert frame_adt_blocks_norepet0.
    generalize frame_adt_blocks0 as l. clear.
    induction l; simpl; intros; eauto. easy.
    inv frame_adt_blocks_norepet0.
    trim IHl; auto.
    intuition subst; simpl in *.
    congruence.
    exfalso; apply H3. eapply in_map in H. exact H.
    exfalso; apply H3. eapply in_map in H1. exact H1.
  Qed.

  Lemma in_frames'_in_frames:
    forall fr b bi,
      in_frames' fr (b, bi) ->
      in_frames fr b.
  Proof.
    unfold in_frames', in_frames. intros fr b bi EQ. destr_in EQ.
    simpl.
    eapply in_frame'_in_frame; eauto.
  Qed.


  Lemma in_stack'_in_stack:
    forall fr b bi,
      in_stack' fr (b, bi) ->
      in_stack fr b.
  Proof.
    induction fr; simpl; intros; eauto.
    rewrite in_stack_cons. destruct H; eauto using in_frames'_in_frames.
  Qed.

  Lemma in_stack'_norepet:
    forall s
      (ND: nodup s)
      b bi1 bi2,
      in_stack' s (b, bi1) ->
      in_stack' s (b, bi2) ->
      bi1 = bi2.
  Proof.
    induction 1; simpl; intros b bi1 bi2 INS1 INS2; eauto. easy.
    destruct INS1 as [INS1 | INS1], INS2 as [INS2 | INS2]; eauto.
    + rewrite in_frames'_rew in INS1, INS2.
      destruct INS1 as (fr1 & INfr1 & INS1).
      destruct INS2 as (fr2 & INfr2 & INS2).
      assert (fr1 = fr2) by congruence; subst.
      eapply in_frame'_norepet; eauto.
    + edestruct H; eauto using in_frames'_in_frames, in_stack'_in_stack.
    + edestruct H; eauto using in_frames'_in_frames, in_stack'_in_stack.
  Qed.

  Lemma stack_inject_inject_frame_info:
    forall f g m l1 l2,
      stack_inject f m g l1 l2 ->
      nodup l1 ->
      nodup l2 ->
      forall b1 bi1 b2 bi2,
        in_stack' l1 (b1, bi1) ->
        in_stack' l2 (b2, bi2) ->
        forall delta, 
          f b1 = Some (b2, delta) ->
          forall o k p,
            m b1 o k p ->
        inject_frame_info delta bi1 bi2.
  Proof.
    intros f g m l1 l2 SI ND1 ND2 b1 bi1 b2 bi2 INS1 INS2 delta FB o k p PERM IPC.
    edestruct (stack_inject_compat _ _ _ _ _ SI _ _ _ _ FB INS1) as (bi2' & INS2' & IFI).
    do 3 eexists; eauto.
    cut (bi2 = bi2'). intro; subst; auto.
    eapply in_stack'_norepet; eauto.
  Qed.

  Lemma take_sumlist:
    forall n l1 l2,
      take n l1 = Some l2 ->
      sum_list l2 <= sum_list l1.
  Proof.
    induction n; simpl; intros; eauto. inv H. simpl. omega.
    repeat destr_in H. 
    apply IHn in Heqo.
    simpl in *. omega.
  Qed.

  Lemma drop_tl:
    forall {A} n (l: list A),
      tl (drop n l) = drop n (tl l).
  Proof.
    induction n; simpl; intros; eauto.
  Qed.

  Lemma drop_drop:
    forall {A} n1 n2 (l: list A),
      drop n1 (drop n2 l) = drop (n1 + n2) l.
  Proof.
    induction n1; simpl; intros; eauto.
    rewrite <- IHn1. rewrite drop_tl. reflexivity.
  Qed.

  Lemma stack_inject_drop:
    forall f m1 g1 l1 l2
      (SI : stack_inject f m1 g1 l1 l2)
      n (POS: O < n) l (TAKE : take n g1 = Some l),
      stack_inject f m1 (drop n g1) (drop (sum_list l) l1) (drop n l2).
  Proof.
    induction 1; simpl; intros; eauto.
    - destruct n; simpl in *; inv TAKE. simpl. constructor.
    - subst.
      destruct n0; simpl in *. omega. repeat destr_in TAKE0. simpl.
      destruct (lt_dec O n0).
      rewrite plus_comm. rewrite <- drop_drop. eapply IHSI; eauto.
      assert (n0 = O) by omega. subst.
      simpl in *. inv Heqo. simpl. rewrite Nat.add_0_r. auto.
  Qed.

  Lemma take_smaller:
    forall {A} a b (l: list A) l1 l2,
      take (a + b) l = Some l1 ->
      take a l = Some l2 ->
      take a l1 = Some l2.
  Proof.
    induction a; simpl; intros; eauto.
    repeat destr_in H. repeat destr_in H0.
    erewrite IHa; eauto.
  Qed.

  Lemma take_drop_rest:
    forall {A} a b (l: list A) l1,
      take (a + b) l = Some l1 ->
      take b (drop a l) = Some (drop a l1).
  Proof.
    induction a; simpl; intros; eauto.
    repeat destr_in H. simpl. eauto.
  Qed.

  Lemma stack_inject_take:
    forall n
      f m g s1 s2
      (SIA: stack_inject f m g s1 s2)
      g' s1' s2'
      (TG: take n g = Some g')
      (TS1: take (sum_list g') s1 = Some s1')
      (TS2: take n s2 = Some s2'),
      stack_inject f m g' s1' s2'.
  Proof.
    induction n; simpl; intros.
    - inv TG; inv TS2. simpl in *. inv TS1. constructor.
    - repeat destr_in TG. repeat destr_in TS2. inv SIA.
      econstructor; eauto.
      eapply take_smaller; eauto.
      eapply IHn; eauto.
      eapply take_drop_rest; eauto.
  Qed.

  Lemma stack_inject_tframe_inject:
    forall f m g s1 s2 x,
      stack_inject f m g s1 s2 ->
      In x s1 ->
      exists y, In y s2 /\ tframe_inject f m x y.
  Proof.
    induction 1; simpl; intros; eauto. easy.
    subst.
    rewrite (take_drop _ _ _ TAKE) in H0. rewrite in_app in H0.
    destruct H0.
    rewrite Forall_forall in FI. apply FI in H0. eauto.
    destruct IHstack_inject as (y & INs2 & TFI). auto.
    eauto.
  Qed.

  Opaque take drop.

  Lemma stack_inject_compose_aux:
    forall f f' m1 m2 g1 g2 s1 s2 s3 g3
      (COMP : compose_frameinj g1 g2 = Some g3)
      (SI12 : stack_inject f m1 g1 s1 s2)
      (SI23 : stack_inject f' m2 g2 s2 s3)
      (PERMS: forall b1 b2 delta o k p,
          f b1 = Some (b2, delta) ->
          m1 b1 o k p ->
          m2 b2 (o + delta)%Z k p),
      stack_inject (compose_meminj f f') m1 g3 s1 s3.
  Proof.
    intros.
    revert f' m2 g2 s2 s3 SI23 f m1 g1 s1 SI12 g3 COMP PERMS.
    induction 1; intros; eauto.
    - inv COMP. inv SI12. constructor.
    - repeat destr_in COMP.
      repeat destr_in H0. repeat destr_in Heqo. simpl in *.
      destruct (take_succeeds (sum_list l) s0) as (t & EQ).
      erewrite <- stack_inject_length_l by eauto.
      eapply take_sumlist; eauto.
      cut (exists sl, sum_list l = S sl). intros (sl & SL). rewrite SL in *.
      econstructor; eauto.
      eapply IHSI23; eauto. 
      rewrite <- SL.
      eapply stack_inject_drop; eauto. omega.
      rewrite Forall_forall in FI |- *. intros.
      exploit stack_inject_take. apply SI12. eauto. rewrite SL; eauto. eauto. 
      intro SIA.
      edestruct (stack_inject_tframe_inject _ _ _ _ _ x SIA) as (y & INhs1 & TFI). auto.
      eapply tframe_inject_compose; eauto.
      Transparent take drop.
      inv SI12; simpl in *. congruence.
      repeat destr_in H0. simpl. eauto.
  Qed.

  Lemma stack_inject_compose:
    forall (f f' : meminj) g g' m1 l1 l2,
      stack_inject f m1 g l1 l2 ->
      forall m2 l3,
        stack_inject f' m2 g' l2 l3 ->
        nodup l2 ->
        nodup l3 ->
        (forall b1 b2 delta o k p,
            f b1 = Some (b2, delta) ->
            m1 b1 o k p ->
            m2 b2 (o + delta)%Z k p) ->
        stack_agree_perms m2 l2 ->
        forall g3,
        (compose_frameinj g g') = Some g3 ->
        stack_inject (compose_meminj f f') m1 g3 l1 l3.
  Proof.
    intros f f' g g' m1 l1 l2 SI1 m2 l3 SI2 ND2 ND3 PERM FAP g3 COMP.
    eapply stack_inject_compose_aux; eauto.
  Qed.

  Lemma is_stack_top_dec : forall s b,
      {is_stack_top s b} + {~is_stack_top s b}.
  Proof.
    intros. unfold is_stack_top. apply in_dec. 
    apply eq_block.
  Qed.

  Lemma is_stack_top_stack_blocks:
    forall s b,
      is_stack_top s b <-> (exists f r, in_frames f b /\ s = f::r).
  Proof.
    unfold is_stack_top, get_stack_top_blocks.
    intros.
    destruct s eqn:?; intuition.
    - decompose [ex and] H; intuition congruence.
    - repeat eexists. eauto.
    - subst.    
      decompose [ex and] H; intuition. inv H2.
      eauto. 
  Qed.

  Lemma not_in_frames_no_frame_info:
    forall (tf : tframe_adt) (b : block), 
      ~ in_frames tf b -> 
      get_assoc_tframes tf b = None.
  Proof.
    intros.
    destruct (get_assoc_tframes tf b) eqn:GAT; auto.
    apply get_assoc_tframes_in in GAT.
    destruct GAT as (f0 & IN1 & IN2).
    exfalso; apply H.
    eapply in_frame_in_frames; eauto.
    eapply in_frame_blocks_in_frame; eauto.
  Qed.

  Lemma get_frame_info_in_frames:
    forall tf b f, get_assoc_tframes tf b = Some f -> in_frames tf b.
  Proof.
    intros.
    destruct (in_frames_dec tf b); auto.
    rewrite not_in_frames_no_frame_info in H; auto. congruence.
  Qed.

  Lemma get_frame_info_in_stack:
    forall s b f, get_frame_info s b = Some f -> in_stack s b.
  Proof.
    intros.
    destruct (in_stack_dec s b); auto.
    rewrite not_in_stack_get_assoc in H; auto. congruence.
  Qed.

  Inductive option_le_stack {A: Type} (Pns: A -> Prop) (Pss: A -> A -> Prop): option A -> option A -> Prop :=
  | option_le_none_none : option_le_stack Pns Pss None None
  | option_le_some_some a b : Pss a b -> option_le_stack Pns Pss (Some a) (Some b)
  | option_le_none_some a: Pns a -> option_le_stack Pns Pss None (Some a).

  Lemma get_assoc_spec:
    forall s b fi,
      get_assoc_stack s b = Some fi ->
      exists fr tf, In (b,fi) (frame_adt_blocks fr) /\ fst tf = Some fr /\ In tf s.
  Proof.
    intros; edestruct get_assoc_stack_In as (f & tf & AIN & IN1 & IN2); eauto.
  Qed.

  Lemma In_tl:
    forall {A} (l: list A) x,
      In x (tl l) ->
      In x l.
  Proof.
    induction l; simpl; intros; eauto.
  Qed.

  Lemma nodup_tl:
    forall l,
      nodup l ->
      nodup (tl l).
  Proof.
    intros l ND; inv ND; simpl; auto. constructor.
  Qed.

  Lemma in_frame_get_assoc:
    forall a b,
      in_frame a b ->
      exists fi : frame_info, get_assoc positive frame_info peq (frame_adt_blocks a) b = Some fi.
  Proof.
    unfold in_frame, get_frame_blocks.
    intros a.
    generalize (frame_adt_blocks a).
    induction l; simpl; intros; eauto. easy.
    destr. destr. eauto. simpl in *. destruct H. congruence. subst.
    eauto.
  Qed.

  Lemma in_frames_get_assoc_tframes:
    forall s b,
      in_frames s b ->
      exists fi, get_assoc_tframes s b = Some fi.
  Proof.
    unfold in_frames, get_assoc_tframes. intros. destr; try easy.
    rewrite pred_dec_true.
    eapply in_frame_get_assoc; eauto. auto.
  Qed.

  Lemma in_stack_get_assoc_stack:
    forall s b,
      in_stack s b ->
      exists fi, get_assoc_stack s b = Some fi.
  Proof.
    induction s; simpl; intros; eauto. easy.
    rewrite in_stack_cons in H.
    destr.
    eapply in_frames_get_assoc_tframes; eauto.
    eapply IHs; eauto. intuition.
  Qed.

  Lemma get_frame_info_inj_gen:
    forall f g m1 s1 s2 b1 b2 delta
      (SI: stack_inject f m1 g s1 s2)
      (ND1: nodup s1)
      (ND2: nodup s2)
      (FB : f b1 = Some (b2, delta))
      (PERM: exists o k p, m1 b1 o k p),
      option_le_stack (fun fi => True)
                (inject_frame_info delta)
                (get_frame_info s1 b1)
                (get_frame_info s2 b2).
  Proof.
    intros.
    unfold get_frame_info.
    destruct (in_stack_dec s1 b1).
    edestruct in_stack_in_frames_ex as (ff & INS & INF); eauto.
    destruct (get_assoc_stack s1 b1) eqn:STK1.
    - destruct PERM as (o & k & p & PERM).
      eapply (wf_stack_in_frames_in_frame) in INF; eauto.
      destruct INF as (vf1 & VF1 & INF).
      edestruct in_frame_info as (fi2 & INF2); eauto.
      erewrite get_assoc_stack_lnr in STK1; eauto. inv STK1.
      edestruct (stack_inject_compat _ _ _ _ _ SI) as (bi2 & INS2 & IFI); eauto.
      setoid_rewrite in_stack'_rew.
      setoid_rewrite in_frames'_rew.
      exists ff; split; auto. exists vf1; split; eauto.
      revert INS2. setoid_rewrite in_stack'_rew.
      setoid_rewrite in_frames'_rew.
      intros (tf & (fr & INFR & INFRS) & INS2).
      erewrite get_assoc_stack_lnr; eauto.
      constructor. auto.
    - edestruct (in_stack_get_assoc_stack s1 b1); congruence.
    - rewrite not_in_stack_get_assoc; auto.
      destruct (get_assoc_stack s2 b2) eqn:FI2.
      + apply option_le_none_some.
        edestruct get_assoc_spec as (fr & tfr & IN & AIN & INR); eauto.
      + apply option_le_none_none.
  Qed.

  Lemma is_stack_top_inj_gen:
    forall P f g s1 s2 b1 b2 delta
      (MINJ: stack_inject f P g s1 s2)
      (FB: f b1 = Some (b2, delta))
      (PERM: exists o k p, P b1 o k p)
      (IST: is_stack_top s1 b1),
      is_stack_top s2 b2.
  Proof.
    intros.
    eapply stack_inject_is_stack_top; eauto.
  Qed.

Lemma in_stack_tl:
  forall (l: stack)  b,
    in_stack ((tl l)) b ->
    in_stack (l) b.
Proof.
  destruct l; simpl; auto.
  intros; rewrite in_stack_cons; auto.
Qed.

Lemma Forall_tl:
  forall {A} P (l: list A),
    Forall P l ->
    Forall P (tl l).
Proof.
  inversion 1; simpl; auto.
Qed.

Lemma stack_agree_perms_tl:
  forall P (l: stack),
    stack_agree_perms P l ->
    stack_agree_perms P (tl l).
Proof.
  red; intros.
  eapply H; eauto.
  eapply In_tl; eauto.
Qed.

Lemma wf_stack_tl p s:
  wf_stack p s ->
  wf_stack p (tl s).
Proof.
  eapply Forall_tl; eauto.
Qed.

Lemma tframe_inject_invariant:
  forall (m m': perm_type) f f1 f2 thr,
    (forall b ofs k p b' delta,
        f b = Some (b', delta) ->
        Plt b thr ->
        m' b ofs k p -> m b ofs k p) ->
    (forall b, in_frames f1 b -> Plt b thr) ->
    tframe_inject f m f1 f2 ->
    tframe_inject f m' f1 f2.
Proof.
  intros m m' f f1 f2 thr PERMS PLT TFI ff1 INf1 HP.
  specialize (TFI _ INf1).
  trim TFI. destruct HP as (b & o & k & p & FB & IFR & PERM).
  destruct (f b) eqn:?; try congruence. destruct p0.
  repeat eexists; eauto. congruence. eapply PERMS; eauto.
  eapply PLT; eauto. eapply in_frame_in_frames; eauto.
  destruct TFI as (f3 & EQ & FI).
  repeat eexists; eauto.
Qed.

Lemma tframe_inject_invariant_strong:
  forall (m m': perm_type) f f1 f2,
    (forall b ofs k p b' delta,
        f b = Some (b', delta) ->
        m' b ofs k p -> m b ofs k p) ->
    tframe_inject f m f1 f2 ->
    tframe_inject f m' f1 f2.
Proof.
  intros m m' f f1 f2 PERMS TFI ff1 INf1 HP.
  specialize (TFI _ INf1). trim TFI. destruct HP as (b & o & k & p & FB & IFR & PERM).
  destruct (f b) eqn:?; try congruence. destruct p0.
  repeat eexists; eauto. congruence.
  destruct TFI as (f3 & EQ & FI).
  subst. repeat eexists; eauto.
Qed.

Lemma in_take:
  forall {A} n (l: list A) t a,
    take n l = Some t ->
    In a t ->
    In a l.
Proof.
  intros A n l t a TAKE IN.
  rewrite (take_drop _ _ _ TAKE).
  rewrite in_app; auto.
Qed.


(* Either in top of taillcall stage or in past stages *)
Definition in_frames_all (tf: tframe_adt) b : Prop :=
  In b (get_opt_frame_blocks (fst tf)) \/ exists f, In f (snd tf) /\ in_frame f b.

(* In either the top or past stages of some taillframe *)
Fixpoint in_stack_all (s: stack) b : Prop :=
  match s with
    nil => False
  | tf::r => in_frames_all tf b \/ in_stack_all r b
  end.

Lemma in_frames_in_frames_all:
  forall tf b,
    in_frames tf b ->
    in_frames_all tf b.
Proof.
  induction tf; simpl; intros; eauto.
  rewrite in_frames_cons in H. destruct H as (fa & EQ & IFR). red. subst. simpl. left; auto.
Qed.

Lemma in_stack_in_stack_all:
  forall s b,
    in_stack s b ->
    in_stack_all s b.
Proof.
  induction s; simpl; intros; eauto.
  rewrite in_stack_cons in H.
  destruct H; eauto. left.
  eapply in_frames_in_frames_all; eauto.
Qed.

Lemma in_stack_all_drop:
  forall n l b,
    in_stack_all (drop n l) b ->
    in_stack_all l b.
Proof.
  induction n; simpl; intros; eauto.
  eapply IHn in H.
  destruct l; simpl in *; eauto.
Qed.

Lemma in_frames_all_in_stack_all:
  forall f l b,
    in_frames_all f b ->
    In f l ->
    in_stack_all l b.
Proof.
  induction l; simpl; intros; eauto.
  destruct H0; subst; eauto.
Qed.

Lemma tframe_inject_invariant':
  forall (m m': perm_type) f f1 f2 ,
    (forall b ofs k p,
        in_frames_all f1 b ->
        m' b ofs k p -> m b ofs k p) ->
    tframe_inject f m f1 f2 ->
    tframe_inject f m' f1 f2.
Proof.
  intros m m' f f1 f2 PERMS TFI ff1 INf1 HP.
  specialize (TFI _ INf1).
  trim TFI. destruct HP as (b & o & k & p & FB & IFR & PERM).
  destruct (f b) eqn:?; try congruence. destruct p0.
  repeat eexists; eauto. congruence. eapply PERMS; eauto.
  left. rewrite INf1. simpl. auto.
  destruct TFI as (f3 & EQ & FI).
  repeat eexists; eauto.
Qed.

Lemma stack_inject_aux_invariant:
  forall (m m': perm_type) f g s1 s2,
    stack_inject f m g s1 s2 ->
    (forall b ofs k p,
        in_stack_all s1 b ->
        m' b ofs k p -> m b ofs k p) ->
    stack_inject f m' g s1 s2.
Proof.
  induction 1; simpl; intros PERM; econstructor; eauto.
  - eapply IHstack_inject; eauto. subst.
    intros; eapply PERM; eauto using in_stack_all_drop.
  - eapply Forall_impl. 2: apply FI.
    simpl.
    intros; eapply tframe_inject_invariant'. 2: eauto.
    intros; eapply PERM; eauto.
    eapply in_frames_all_in_stack_all; eauto.
    eapply in_take; eauto.
Qed.

Lemma stack_inject_invariant:
  forall (m m': perm_type) f g s1 s2,
    (forall b ofs k p,
        in_stack_all s1 b ->
        m' b ofs k p -> m b ofs k p) -> (* just removed stuff here *)
    stack_inject f m  g s1 s2 ->
    stack_inject f m' g s1 s2.
Proof.
    intros.
    eapply stack_inject_aux_invariant; eauto.
Qed.

  Lemma stack_inject_aux_invariant_strong:
    forall (m m': perm_type) f g s1 s2,
      stack_inject f m g s1 s2 ->
      (forall b ofs k p b' delta,
          f b = Some (b', delta) ->
          m' b ofs k p -> m b ofs k p) ->
      stack_inject f m' g s1 s2.
  Proof.
    induction 1; simpl; intros PERM; econstructor; eauto.
    eapply Forall_impl. 2: apply FI.
    simpl.
    intros; eapply tframe_inject_invariant_strong; eauto.
  Qed.

  (* used in Memory *)
  Lemma stack_inject_invariant_strong:
    forall (m m': perm_type) f g f1 f2,
      (forall b ofs k p b' delta,
          f b = Some (b', delta) ->
          m' b ofs k p -> m b ofs k p) ->
      stack_inject f m  g f1 f2 ->
      stack_inject f m' g f1 f2.
  Proof.
    intros. eapply stack_inject_aux_invariant_strong; eauto.
  Qed.

  Lemma stack_inject_nil:
    forall f p,
      stack_inject f p nil nil nil.
  Proof.
    repeat constructor.
  Qed.

  Lemma stack_inject_length_stack:
    forall j g P s1 s2,
      stack_inject j g P s1 s2 ->
      (length s2 <= length s1)%nat.
  Proof.
    intros j g P s1 s2 SI.
    revert SI. clear.
    revert g s1 s2.
    induction 1; simpl; intros; eauto.
    simpl in *. repeat destr_in TAKE. simpl.
    simpl in *. apply le_n_S. etransitivity. apply IHSI.
    rewrite drop_length. omega.
    eapply take_succeeds_inv; eauto.
  Qed.

  Fixpoint list_nats n :=
    match n with
      O => nil
    | S m => m :: list_nats m
    end.

  Lemma in_list_nats:
    forall n m,
      In m (list_nats n) <-> (m < n)%nat.
  Proof.
    induction n; simpl; split; intros.
    - easy.
    - omega.
    - destruct H; subst. omega. apply IHn in H; omega.
    - destruct (Nat.eq_dec m n); auto. right; rewrite IHn. omega.
  Qed.

  Lemma option_eq_true:
    forall {A} Aeq (o1 o2: option A),
      proj_sumbool (option_eq Aeq o1 o2) = true <-> o1 = o2.
  Proof.
    intros.
    destruct (option_eq Aeq o1 o2); try congruence.
    subst; tauto. split; inversion 1. congruence.
  Qed.

  Fixpoint filteri {A} (f: nat -> A -> bool) (l: list (nat * A)) : list (A) :=
    match l with
      nil => nil
    | (i,a)::r => let r' := filteri f r in
             if f i a then a :: r' else r'
    end.

  Lemma le_add_pos:
    (forall a b,
        0 <= b ->
        a <= a + b)%Z.
  Proof.
    intros; omega.
  Qed.

  Fixpoint pairi {A} (l: list A) i : list (nat * A) :=
    match l with
      nil => nil
    | a::r => (i,a)::(pairi r (S i))
    end.



Definition maxl (l: list Z) : option Z :=
  match l with nil => None | _ => Some (fold_right Z.max Z0 l) end.

Lemma maxl_is_max:
  forall l m,
    maxl l = Some m ->
    Forall (fun n => (n <= m)%Z) l.
Proof.
  destruct l. constructor.
  intros. unfold maxl in H.
  revert H. generalize (z :: l). inversion 1; subst.
  clear.
  induction l0; simpl; intros. constructor.
  constructor; auto.
  apply Z.le_max_l.
  eapply Forall_impl. 2: eauto. intros.
  simpl in H0.
  apply Zmax_bound_r. auto.
Qed.

Lemma maxl_in:
  forall l (F: Forall (fun n => 0 <= n)%Z l) m,
    maxl l = Some m ->
    In m l.
Proof.
  destruct l. inversion 2. unfold maxl. simpl. inversion 2; subst. clear H.
  revert z F.
  induction l; simpl; intros; eauto. inv F. rewrite Z.max_l; auto.
  rewrite Z.max_assoc.
  specialize (IHl (Z.max z a)). trim IHl.
  inv F. inv H2.
  constructor. apply Z.max_le_iff. auto.
  auto.
  destruct IHl. rewrite <- H.
  rewrite Zmax_spec. destr.
  auto.
Qed.

Definition size_frame (f: frame_adt) : Z := 
  align (frame_adt_size f) 8.

Definition opt_size_frame (of: option frame_adt) : Z :=
  match of with
  | Some f => size_frame f
  | None => Z0
  end.

Definition max_l (l: list Z) : Z :=
  fold_right Z.max Z0 l.

Definition size_frames (l: tframe_adt) : Z :=
  Z.max (opt_size_frame (fst l)) (max_l (map size_frame (snd l))).

Lemma size_frames_cons:
  forall a b,
    size_frames ( a , b ) = Z.max (opt_size_frame a) (max_l (map size_frame b)).
Proof.
  reflexivity.
Qed.

Fixpoint size_stack (l: stack) : Z :=
  match l with
    nil => 0
  | fr::r => size_stack r + size_frames fr
  end.

Lemma size_frame_pos:
  forall fr,
    (0 <= size_frame fr)%Z.
Proof.
  unfold size_frame.
  etransitivity.
  2: apply align_le. apply frame_adt_size_pos. omega.
Qed.

Lemma opt_size_frame_pos:
  forall fr,
    (0 <= opt_size_frame fr)%Z.
Proof.
  unfold opt_size_frame. intros. destr. apply size_frame_pos. omega.
Qed.

Lemma size_frames_pos:
  forall tf,
    (0 <= size_frames tf)%Z.
Proof.
  intros. unfold size_frames. 
  apply Z.max_le_iff.
  left.
  apply opt_size_frame_pos.
Qed.

Lemma size_stack_pos:
  forall s,
    (0 <= size_stack s)%Z.
Proof.
  induction s; simpl; intros; eauto. omega.
  generalize (size_frames_pos a); omega.
Qed.

Lemma size_stack_tl:
  forall l,
    (size_stack (tl l) <= size_stack l)%Z.
Proof.
  induction l; simpl; intros. omega.
  generalize (size_frames_pos a); omega.
Qed.
  


  Ltac elim_div :=
    unfold Zdiv, Zmod in *;
    repeat
      match goal with
      |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      |  |-  context[ Zdiv_eucl ?X ?Y ] =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      end; unfold Remainder.
  

  Open Scope Z_scope.
  Lemma align_ge1:
    forall sz al,
      al > 0 ->
      exists b, 0 <= b < al /\
           align sz al = sz + b /\ 
           b = (al - 1 - (sz - 1 - al * ((sz - 1) / al))).
  Proof.
    intros.
    generalize (align_le sz al H).
    destruct (align_divides sz al H).
    rewrite H0.
    intros. 
    unfold align in H0.
    rewrite <- H0.
    replace ((sz+al-1)/al) with (1+ ((sz-1)/al)).
    {
      replace ((1+ ((sz-1)/al))*al) with (al + (sz -1)/al *al).
      {
        rewrite Z.mul_comm.
        replace (al * ((sz - 1) / al)) with
        (al * ((sz - 1) / al) + (sz-1) mod al - (sz-1) mod al) by omega.
        rewrite <- Z.div_mod by omega.
        rewrite Z.mod_eq by omega.
        exists (al - 1 - (sz - 1 - al * ((sz - 1) / al))).
        split; try omega.
        {
          elim_div. assert (al <> 0) by omega. intuition.
        }
      }
      rewrite Z.mul_add_distr_r. omega.
    }
    {
      replace (sz + al - 1) with ((sz -1) + 1*al) by omega.
      rewrite Z_div_plus_full by omega.
      omega.
    }
  Qed.
  
  Lemma align_mono:
    forall al sz sz',
      al > 0 ->
      0 <= sz <= sz' ->
      align sz al <= align sz' al.
  Proof.
    intros.
    generalize (align_ge1 sz al H)
               (align_ge1 sz' al H).
    intros [b [A [B C]]] [c [D [E F]]].
    destruct (zlt (sz'-sz) al); try intuition omega.
    assert (exists d, 0 <= d < al /\ sz' = sz + d).
    {
      clear - H0 H l.
      exists (sz'-sz). intuition try omega.
    }
    destruct H1 as [d [ENC EQ]]. rewrite EQ in *.
    clear EQ.
    rewrite B; rewrite E.
    cut (      al * ((sz - 1) / al) <=
               (   al * ((sz + d - 1) / al))); intros; try omega.  
    apply Z.mul_le_mono_nonneg_l; try  omega.
    apply Z.div_le_mono; try omega.
  Qed.

  Lemma stack_inject_aux_id:
    forall p s,
      stack_inject inject_id p (flat_frameinj (length s)) s s.
  Proof.
    induction s; simpl; intros; econstructor; simpl; eauto.
    repeat constructor.
    eapply tframe_inject_id; eauto.
  Qed.

  Lemma flat_frameinj_pos s:
    Forall (lt 0) (flat_frameinj s).
  Proof.
    induction s; simpl; intros; constructor; auto.
  Qed.

  Lemma stack_inject_id:
    forall p s,
      wf_stack p s ->
      stack_inject inject_id p (flat_frameinj (length s)) s s.
  Proof.
    intros p s WF; auto.
    eapply stack_inject_aux_id; eauto.
  Qed.

(** The following shows how to transport a stack injection when more blocks get
injected. We have an hypothesis about those new blocks. Namely, they are not
part of the source stack, and if the block they're injected to is part of the
stack, then the corresponding locations have the public stack permission. The
typical case when a new block is not in the stack but the target block they
inject to is already in is Inlining, where the parent function clearly already
exists and is already on the stack when the block for the callee is allocated.
Another scenario is generation of single-stack-block Asm, where the unique stack
block is also present and part of the stack when the 'source' blocks get
allocated. *)

  Lemma in_stack_drop:
    forall n s b,
      in_stack (drop n s) b ->
      in_stack s b.
  Proof.
    induction n; simpl; intros; eauto.
    apply IHn in H.
    apply in_stack_tl. auto.
  Qed.

Lemma stack_inject_aux_incr:
  forall f f' g (p: perm_type)  s1 s2,
    stack_inject f p g s1 s2 ->
    inject_incr f f' ->
    (forall b b' delta,
        f b = None ->
        f' b = Some (b', delta) ->
        ~ in_stack s1 b) ->
    stack_inject f' p g s1 s2.
Proof.
  induction 1; simpl; intros INCR NEW; econstructor; eauto.
  subst.
  eapply IHstack_inject; eauto.
  intros b b' delta H0 H1 INS. eapply NEW; eauto using in_stack_drop.
  eapply Forall_impl. 2: apply FI.
  simpl; intros.
  eapply tframe_inject_incr; eauto. subst.
  intros b b' delta H2 H3 IFR.
  eapply NEW; eauto.
  eapply in_frames_in_stack; eauto using in_take.
Qed.

Lemma stack_inject_incr:
  forall f f' g (p: perm_type)  s1 s2,
    inject_incr f f' ->
    (forall b b' delta,
        f b = None ->
        f' b = Some (b', delta) ->
        ~ in_stack s1 b) ->
    stack_inject f  p g s1 s2 ->
    stack_inject f' p g s1 s2.
Proof.
  intros f f' g p s1 s2 INCR NEW SI.
  eapply stack_inject_aux_incr; eauto.
Qed.

Lemma norepet_1:
  forall {A:Type} (a:A),
    list_norepet (a::nil).
Proof.
  repeat constructor. easy.
Qed.

Definition make_singleton_frame_adt (b: block) (sz: Z) (machsz: Z) :=
  {|
    frame_adt_blocks := (b, default_frame_info sz)::nil;
    frame_adt_size := Z.max 0 machsz;
    frame_adt_blocks_norepet := norepet_1 _;
    frame_adt_size_pos := Z.le_max_l _ _
  |}.

(*
Definition make_singleton_frame_adt' (b: block) fi (sz: Z) :=
  {|
    frame_adt_blocks := (b,fi)::nil;
    frame_adt_size := Z.max 0 sz;
    frame_adt_blocks_norepet := norepet_1 _;
    frame_adt_size_pos := Z.le_max_l _ _
  |}.
*)

  Lemma val_inject_ext:
    forall j1 j2 v1 v2,
      Val.inject j1 v1 v2 ->
      (forall x, j1 x = j2 x) ->
      Val.inject j2 v1 v2.
  Proof.
    intros j1 j2 v1 v2 INJ EXT.
    inv INJ; econstructor; eauto.
    rewrite <- EXT; eauto.
  Qed.

  Lemma memval_inject_ext:
    forall j1 j2 m1 m2,
      memval_inject j1 m1 m2 ->
      (forall x, j1 x = j2 x) ->
      memval_inject j2 m1 m2.
  Proof.
    intros j1 j2 m1 m2 INJ EXT.
    inv INJ; constructor; auto.
    eapply val_inject_ext; eauto.
  Qed.

Lemma frame_inject_ext:
  forall j1 j2 f1 f2,
    frame_inject j1 f1 f2 ->
    (forall b, j1 b = j2 b) ->
    frame_inject j2 f1 f2.
Proof.
  intros j1 j2 f1 f2 FI EXT.
  red in FI |- *.
  rewrite Forall_forall in *.
  intros x IN b2 delta J2.
  rewrite <- EXT in J2. eauto.
Qed.

Lemma has_perm_frame_ext:
  forall j j' P f,
    (forall b, j b = j' b) ->
    has_perm_frame P j f ->
    has_perm_frame P j' f.
Proof.
  intros j j' P f EXT (b & o & k & p0 & FSOME & INFR1 & PERM).
  repeat eexists; eauto. rewrite EXT in FSOME; auto.
Qed.

Lemma tframe_inject_ext:
  forall j1 j2 p f1 f2,
    tframe_inject j1 p f1 f2 ->
    (forall b, j1 b = j2 b) ->
    tframe_inject j2 p f1 f2.
Proof.
  intros j1 j2 p f1 f2 FI EXT ff1 INf1 HP.
  eapply has_perm_frame_ext in HP. 2: symmetry; eauto.
  edestruct FI as (f3 & IN1 & FI12); eauto.
  repeat eexists; eauto. eapply frame_inject_ext; eauto.
Qed.

  Lemma stack_inject_aux_ext':
    forall j1 j2 g P m1 m2,
      stack_inject j1 P g m1 m2 ->
      (forall b, j1 b = j2 b) ->
      stack_inject j2 P g m1 m2.
  Proof.
    induction 1; simpl; intros; econstructor; eauto.
    eapply Forall_impl. 2: apply FI.
    simpl; intros.
    eapply tframe_inject_ext; eauto.
  Qed.

  Lemma stack_inject_ext':
    forall j1 j2 g P m1 m2,
      stack_inject j1 P g m1 m2 ->
      (forall b, j1 b = j2 b) ->
      stack_inject j2 P g m1 m2.
  Proof.
    intros j1 j2 g P m1 m2 INJ EXT.
    eapply stack_inject_aux_ext'; eauto.
  Qed.


  Lemma frameinj_push_flat:
    forall m,
      flat_frameinj (Datatypes.S m) = 1%nat :: flat_frameinj m.
  Proof.
    reflexivity.
  Qed.

Lemma frame_at_pos_cons:
  forall l i f a,
    frame_at_pos l i f ->
    frame_at_pos (a::l) (S i) f.
Proof.
  intros l i f a H; inv H; econstructor.
  simpl.
  auto.
Qed.

Lemma frame_at_pos_last:
  forall l a f,
    frame_at_pos (a::l) 0 f ->
    f = a.
Proof.
  intros l a f H. inv H. simpl in H0. congruence.
Qed.

Lemma frame_at_pos_same_frame:
  forall s i1 i2 f b,
    frame_at_pos s i1 f ->
    frame_at_pos s i2 f ->
    in_frames f b ->
    nodup s ->
    i1 = i2.
Proof.
  induction s; simpl; intros; eauto.
  - inv H.  rewrite nth_error_nil in H3. easy.
  - inv H; inv H0.
    destruct (Nat.eq_dec i1 i2); auto.
    exfalso.
    destruct (Nat.eq_dec i1 O).
    + subst. simpl in H3. inv H3.
      destruct i2. congruence. simpl in H. apply nth_error_In in H.
      inv H2. specialize (H5 _ H1). apply H5.
      eapply in_frames_in_stack; eauto.
    + destruct (Nat.eq_dec i2 0).
      * subst.
        simpl in H. inv H.
        destruct i1. congruence. simpl in H3. apply nth_error_In in H3.
        inv H2. specialize (H5 _ H1). apply H5.
        eapply in_frames_in_stack; eauto.
      * destruct i1, i2; try congruence. simpl in *.
        apply n. f_equal. eapply IHs; eauto.
        constructor; auto. constructor; auto.
        apply nodup_tl in H2.
        simpl in *; auto.
Qed.

Local Open Scope nat_scope.



Opaque minus.

Inductive top_tframe_prop (P: tframe_adt -> Prop) : stack -> Prop :=
| top_tframe_prop_intro tf r:
    P tf ->
    top_tframe_prop P (tf::r).

Definition top_tframe_tc (s: stack) : Prop :=
  top_tframe_prop (fun tf => fst tf = None) s.

Lemma check_top_tc s : { top_tframe_tc s } + { ~ top_tframe_tc s }.
Proof.
  unfold top_tframe_tc.
  destruct s eqn:STK. right; intro A; inv A.
  destruct t.
  destruct o.
  right. intro A. inv A. inv H0.
  left; constructor. auto.
Defined.

Lemma stack_inject_push_new_stage_right:
  forall j n g P s1 s2,
    stack_inject j P (n :: g) s1 s2 ->
    top_tframe_tc s1 ->
    (2 <= n)%nat ->
    stack_inject j P (1%nat :: pred n :: g) s1 ((None,nil)::s2).
Proof.
  intros j n g P s1 s2 SI TTNP Gof1.
  inv SI.
  simpl in *. repeat destr_in TAKE.
  econstructor. reflexivity. simpl. eauto.
  destruct n0. omega. econstructor; eauto. inv FI; auto.
  repeat constructor.
  intros ff1 INf1 _. exfalso.
  inv TTNP. congruence.
Qed.

Lemma frame_at_pos_cons_inv:
  forall a s i f,
    frame_at_pos (a::s) i f ->
    O < i ->
    frame_at_pos s (pred i) f.
Proof.
  intros a s i f FAP LT ; inv FAP.
  destruct i. omega.
  simpl in H. simpl. constructor; auto.
Qed.

Lemma stack_inject_unrecord_parallel:
  forall j g m1 s1 s2
    (SI: stack_inject j m1 (1%nat :: g) s1 s2)
    (ND2: nodup s2)
    fr2 l2
    (STK2 : s2 = fr2 :: l2)
    fr1 l1
    (STK1 : s1 = fr1 :: l1),
    stack_inject j m1 g l1 l2.
Proof.
  intros. subst.
  inv SI. simpl in *; auto.
Qed.

Lemma stack_inject_unrecord_parallel_frameinj_flat_on:
  forall j m1 s1 s2
    (SI: stack_inject j m1 (flat_frameinj (length s2)) s1 s2)
    (ND2: nodup s2)
    fr2 l2
    (STK2 : s2 = fr2 :: l2)
    fr1 l1
    (STK1 : s1 = fr1 :: l1),
    stack_inject j m1 (flat_frameinj (length l2)) l1 l2.
Proof.
  intros. subst.
  eapply stack_inject_unrecord_parallel; eauto.
Qed.

Definition same_sizes_frame f1 f2 := frame_adt_size f1 = frame_adt_size f2.

Lemma same_sizes_frame_size_eq:
  forall f1 f2,
    same_sizes_frame f1 f2 ->
    size_frame f1 = size_frame f2.
Proof.
  intros f1 f2 SS; unfold size_frame. rewrite SS. reflexivity.
Qed.

Definition same_sizes_list_frames tf1 tf2 :=
  list_forall2 same_sizes_frame tf1 tf2.

Definition same_sizes_list_frames_size_eq:
  forall tf1 tf2 (SS: same_sizes_list_frames tf1 tf2),
    map size_frame tf1 = map size_frame tf2.
Proof.
  induction 1; simpl; intros; eauto.
  apply same_sizes_frame_size_eq in H. congruence.
Qed.

Definition same_sizes_opt_frame of1 of2 :=
  match of1, of2 with
  | Some f1, Some f2 => same_sizes_frame f1 f2
  | None, None => True
  | _, _ => False
  end.

Lemma same_sizes_opt_frame_size_eq:
  forall f1 f2,
    same_sizes_opt_frame f1 f2 ->
    opt_size_frame f1 = opt_size_frame f2.
Proof.
  intros f1 f2 SS; red in SS.
  repeat destr_in SS. simpl.
  apply same_sizes_frame_size_eq; eauto.
Qed.

Definition same_sizes_tframes (tf1 tf2: tframe_adt) :=
  same_sizes_opt_frame (fst tf1) (fst tf2) /\
  same_sizes_list_frames (snd tf1) (snd tf2).

Lemma same_sizes_tframes_size_eq:
  forall tf1 tf2
    (SS: same_sizes_tframes tf1 tf2),
    size_frames tf2 = size_frames tf1.
Proof.
  intros tf1 tf2 (SS1 & SS2); unfold size_frames.
  apply same_sizes_opt_frame_size_eq in SS1.
  apply same_sizes_list_frames_size_eq in SS2. congruence.
Qed.

Inductive stack_equiv : stack -> stack -> Prop :=
| stack_equiv_nil: stack_equiv nil nil
| stack_equiv_cons s1 s2 tf1 tf2
                   (SE: stack_equiv s1 s2)
                   (LF2: same_sizes_tframes tf1 tf2):
  stack_equiv (tf1::s1) (tf2::s2).

Lemma stack_equiv_fsize:
  forall s1 s2,
    stack_equiv s1 s2 ->
    size_stack s2 = size_stack s1.
Proof.
  induction 1; simpl; intros. reflexivity.
  f_equal; auto. eapply same_sizes_tframes_size_eq; eauto.
Qed.

Lemma stack_equiv_length:
  forall s1 s2, stack_equiv s1 s2 -> length s1 = length s2.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Lemma stack_equiv_tail:
  forall s1 s2,
    stack_equiv s1 s2 ->
    stack_equiv (tl s1) (tl s2).
Proof.
  inversion 1; simpl; auto; constructor; auto.
Qed.

Hint Resolve stack_equiv_tail.

Inductive match_stack : list (option (block * Z)) -> stack -> Prop :=
| match_stack_nil s: match_stack nil s
| match_stack_cons lsp s f r sp bi z
                       (REC: match_stack lsp s)
                       (BLOCKS: frame_adt_blocks f = (sp,bi)::nil)
                       (SIZE: frame_size bi = Z.max 0 z):
    match_stack (Some (sp,z) :: lsp) ( (Some f , r) :: s).

Lemma list_forall2_refl:
  forall (R: frame_adt -> frame_adt -> Prop) (Rrefl: forall x, R x x) s,
  list_forall2 R s s.
Proof.
  induction s; constructor; auto.
Qed.

Lemma stack_equiv_refl:
  forall s,
    stack_equiv s s.
Proof.
  induction s; constructor. auto.
  split; red. repeat destr.
  apply list_forall2_refl. reflexivity.
Qed.
End INJ.

Lemma has_perm_frame_impl:
  forall (P1 P2: perm_type) j f tf,
    has_perm_frame P1 j f ->
    frame_inject j f tf ->
    (forall b1 b2 delta o k p, j b1 = Some (b2, delta) -> P1 b1 o k p -> P2 b2 (o + delta)%Z k p) ->
    has_perm_frame P2 inject_id tf.
Proof.
  intros P1 P2 j f tf (b & o & k & p & NONE & IFR & PERM1) FI PERMS.
  red in FI.
  apply in_frame_info in IFR. destruct IFR as (fi & IFR).
  rewrite Forall_forall in FI; specialize (FI _ IFR).
  simpl in FI.
  destruct (j b) eqn:?; try congruence. destruct p0.
  specialize (FI _ _ eq_refl).
  destruct FI as (fi' & IN' & IFI).
  exists b0, (o + z)%Z, k, p. split. unfold inject_id. congruence.
  split. eapply in_frame'_in_frame; eauto. eauto.
Qed.

Definition stack_top_is_new s :=
  top_tframe_prop (fun tf => tf = (None,nil)) s.

Lemma max_in_le:
  forall l a i,
    In a l ->
    (a <= fold_right Z.max i l)%Z.
Proof.
  induction l; simpl; intros; eauto.
  easy. destruct H; eauto. subst. apply Z.le_max_l.
  apply Z.max_le_iff. right; eauto.
Qed.

Lemma max_sublist:
  forall l1 l2 i,
    (forall x, In x l1 -> In x l2) ->
    (fold_right Z.max i l1 <= fold_right Z.max i l2)%Z.
Proof.
  induction l1; simpl; intros; eauto.
  induction l2; simpl; intros; eauto. omega.
  apply Z.max_le_iff. right. apply IHl2. easy.
  apply Z.max_lub_iff. split.
  apply max_in_le; auto.
  apply IHl1. auto.
Qed.

(* For use in Mach and Asm, the parent_sp pointer is now computed on the stack
   adt rather than on the abstract semantic callstack in Mach or with an extra
   stored pointer in Asm. *)

Definition current_frame_sp (tf: tframe_adt) : val :=
  match fst tf with
  | Some fr =>
    match frame_adt_blocks fr with
    | (b,fi)::nil => Vptr b Integers.Ptrofs.zero
    | _ => Vundef
    end
  | _ => Vnullptr
  end.

Definition current_sp (stk: stack) : val :=
  match stk with
    fr :: _ => current_frame_sp fr
  | _ => Vnullptr
  end.

Definition parent_sp (stk: stack) : val :=
  match stk with
    nil => Vundef
  | _ :: tl => current_sp tl
  end.

Lemma type_parent_sp:
  forall stk,
  Val.has_type (parent_sp stk) Tptr.
Proof.
  unfold parent_sp, current_sp, current_frame_sp. intros.
  repeat destr; try now (simpl; auto).
Qed.

Definition opt_cons {A: Type} (o: option A) (l: list A) : list A :=
  match o with
    None => l
  | Some a => a::l
  end.

Lemma In_opt_cons:
  forall {A} o (l: list A) a,
    In a (opt_cons o l) ->
    o = Some a \/ In a l.
Proof.
  intros. destruct o; simpl in *; eauto. intuition congruence.
Qed.

Lemma size_frames_eq:
  forall f l, size_frames (f, l) = size_frames (None, opt_cons f l).
Proof.
  unfold size_frames; simpl.
  destruct f. simpl. intros.
  rewrite (Z.max_r 0). auto. apply Z.max_le_iff. left; apply size_frame_pos.
  simpl. reflexivity.
Qed.


Lemma map_opt_cons:
  forall {A B} (f: A -> B) o l,
    map f (opt_cons o l) = opt_cons (option_map f o) (map f l).
Proof.
  destruct o; simpl; reflexivity.
Qed.

Lemma max_opt_size_frame_tailcall:
  forall f l,
    Z.max (opt_size_frame f) (max_l l) = max_l (opt_cons (option_map size_frame f) l).
Proof.
  destruct f; simpl; auto.
  intros; apply Z.max_r.
  induction l; simpl; intros; eauto. omega.
  apply Z.max_le_iff. auto.
Qed.

Lemma size_frames_tc:
  forall f,
    size_frames (None, opt_cons (fst f) (snd f)) = size_frames f.
Proof.
  unfold size_frames.
  intros. simpl.
  rewrite map_opt_cons. rewrite <- max_opt_size_frame_tailcall.
  apply Z.max_r.
  rewrite Z.max_le_iff. left. destruct f; simpl. destruct o; simpl.
  apply size_frame_pos. omega.    
Qed.

(* (** SACC: The following property is needed by ValueDomain, to prove mmatch_inj. *)
Definition record_init_sp m :=
  let (m1, b1) := alloc (push_new_stage m) 0 0 in
  record_stack_blocks m1 (make_singleton_frame_adt b1 0 0). 

  Lemma record_init_sp_inject:
    forall j g m1 m1' m2,
      Mem.inject j g m1 m1' ->
      size_stack (stack m1') <= size_stack (stack m1) ->
      record_init_sp m1 = Some m2 ->
      exists m2', record_init_sp m1' = Some m2' /\ inject (fun b => if peq b (nextblock (push_new_stage m1))
                                                           then Some (nextblock (push_new_stage m1'), 0)
                                                           else j b) (1%nat::g) m2 m2'.
  Proof.
    intros j g m1 m1' m2 INJ SZ RIS.
    unfold record_init_sp in *; destr_in RIS.
    exploit Mem.push_new_stage_inject. apply INJ. intro INJ0.
    edestruct Mem.alloc_parallel_inject as (f' & m2' & b2 & ALLOC & INJ1 & INCR & JNEW & JOLD).
    apply INJ0. eauto. reflexivity. reflexivity.
    rewrite ALLOC.
    edestruct record_push_inject_alloc as (m2'' & RSB & INJ'). 7: apply RIS.
    2: apply Heqp. 2: apply ALLOC. all: eauto.
    rewrite push_new_stage_stack. constructor; reflexivity.
    rewrite ! push_new_stage_stack. simpl. auto.
    eexists; split. eauto.
    eapply inject_ext. eauto.
    intros. erewrite <- ! alloc_result by eauto.
    destr. eauto.
  Qed.

  Lemma record_init_sp_extends:
    forall m1 m1' m2,
      Mem.extends m1 m1' ->
      size_stack (stack m1') <= size_stack (stack m1) ->
      record_init_sp m1 = Some m2 ->
      exists m2', record_init_sp m1' = Some m2' /\ extends m2 m2'.
  Proof.
    intros m1 m1' m2 INJ SZ RIS.
    unfold record_init_sp in *; destr_in RIS.
    apply extends_push in INJ.
    edestruct alloc_extends as (m2' & ALLOC & INJ1).
    apply INJ. eauto. reflexivity. reflexivity.
    rewrite ALLOC.
    edestruct record_push_extends_flat_alloc as (m2'' & RSB & INJ'). 4: apply RIS.
    apply Heqp. apply ALLOC. all: eauto.
    rewrite push_new_stage_stack. constructor; reflexivity.
    rewrite ! push_new_stage_stack. simpl. auto.
  Qed.

  Lemma record_init_sp_flat_inject
    : forall (m1 m1' m2 : mem),
      Mem.inject (Mem.flat_inj (Mem.nextblock m1)) (flat_frameinj (length (Mem.stack m1))) m1 m1' ->
      size_stack (Mem.stack m1') <= size_stack (Mem.stack m1) ->
      Mem.record_init_sp m1 = Some m2 ->
      Mem.nextblock m1 = Mem.nextblock m1' ->
      exists m2' : mem,
        Mem.record_init_sp m1' = Some m2' /\
        Mem.inject
          (Mem.flat_inj (Mem.nextblock m2))
          (flat_frameinj (length (Mem.stack m2))) m2 m2'.
  Proof.
    intros m1 m1' m2 INJ SZ RIS EQNB.
    edestruct record_init_sp_inject as (m2' & RIS' & INJ'); eauto.
    eexists; split; eauto.
    unfold record_init_sp in RIS; destr_in RIS.
    erewrite (record_stack_block_nextblock _ _ _ RIS).
    erewrite (nextblock_alloc _ _ _ _ _ Heqp).
    rewrite push_new_stage_nextblock.
    destruct (record_stack_blocks_stack_eq _ _ _ RIS) as (tf & r & EQ1 & EQ2).
    rewrite EQ2. 
    erewrite (alloc_stack_blocks _ _ _ _ _ Heqp) in EQ1.
    rewrite push_new_stage_stack in EQ1. inv EQ1.
    simpl. rewrite frameinj_push_flat.
    eapply inject_ext; eauto.
    simpl; intros. unfold flat_inj.
    rewrite ! push_new_stage_nextblock. rewrite EQNB.
    repeat (destr; subst); xomega.
  Qed.

  Lemma record_init_sp_nextblock:
    forall m1 m2,
      record_init_sp m1 = Some m2 ->
      Ple (nextblock m1) (nextblock m2).
  Proof.
    intros m1 m2 RIS.
    unfold record_init_sp in RIS. destr_in RIS.
    erewrite (record_stack_block_nextblock _ _ _ RIS).
    erewrite (nextblock_alloc _ _ _ _ _ Heqp).
    rewrite push_new_stage_nextblock. xomega.
  Qed.

  Lemma record_init_sp_nextblock_eq:
    forall m1 m2,
      record_init_sp m1 = Some m2 ->
      (nextblock m2) = Pos.succ (nextblock m1).
  Proof.
    intros m1 m2 RIS.
    unfold record_init_sp in RIS. destr_in RIS.
    erewrite (record_stack_block_nextblock _ _ _ RIS).
    erewrite (nextblock_alloc _ _ _ _ _ Heqp).
    rewrite push_new_stage_nextblock. reflexivity.
  Qed.
  
  Lemma record_init_sp_stack:
    forall m1 m2,
      Mem.record_init_sp m1 = Some m2 ->
      Mem.stack m2 = (Some (make_singleton_frame_adt (Mem.nextblock (Mem.push_new_stage m1)) 0 0),nil)::Mem.stack m1.
  Proof.
    unfold Mem.record_init_sp. intros m1 m2 RIS; destr_in RIS.
    destruct (record_stack_blocks_stack_eq _ _ _ RIS) as (tf & r & EQ1 & EQ2).
    rewrite EQ2. 
    erewrite (alloc_stack_blocks _ _ _ _ _ Heqp) in EQ1.
    rewrite push_new_stage_stack in EQ1. inv EQ1.
    exploit Mem.alloc_result; eauto. intros; subst. reflexivity.
  Qed.
  
  Lemma record_init_sp_perm:
    forall m1 m2,
      Mem.record_init_sp m1 = Some m2 ->
      forall b o k p,
        perm m2 b o k p <-> perm m1 b o k p.
  Proof.
    unfold Mem.record_init_sp. intros m1 m2 RIS; destr_in RIS.
    intros.
    split; intro P.
    - eapply push_new_stage_perm.
      eapply record_stack_block_perm in P. 2: eauto.
      eapply perm_alloc_inv in P; eauto.
      destr_in P. omega.
    - eapply record_stack_block_perm'. eauto.
      eapply perm_alloc_1. eauto.
      eapply push_new_stage_perm. auto.
  Qed.
*)

(*   Definition is_ptr (v: val) :=
    match v with Vptr _ _ => Some v | _ => None end.
  
  Definition encoded_ra (l: list memval) : option val :=
    match proj_bytes l with
    | Some bl => Some (Vptrofs (Ptrofs.repr (decode_int bl)))
    | None => is_ptr (Val.load_result Mptr (proj_value (quantity_chunk Mptr) l))
    end.

  Definition loadbytesv chunk m addr :=
    match addr with
      Vptr b o =>
      match Mem.loadbytes m b (Ptrofs.unsigned o) (size_chunk chunk) with
      | Some bytes => encoded_ra bytes
      | None => None
      end
    | _ => None
    end.

  Lemma loadbytesv_inject:
    forall j g chunk m m' v v' ra,
      Mem.inject j g m m' ->
      Val.inject j v v' ->
      loadbytesv chunk m v = Some ra ->
      exists ra', loadbytesv chunk m' v' = Some ra' /\ Val.inject j ra ra'.
  Proof.
    intros j g chunk m m' v v' ra MINJ VINJ L.
    unfold loadbytesv in *.
    destr_in L. inv VINJ.
    destr_in L.
    edestruct Mem.loadbytes_inject as (l' & L' & INJ); eauto.
    erewrite Mem.address_inject; eauto.
    rewrite L'.
    - unfold encoded_ra in L |- *.
      repeat destr_in L.
      erewrite proj_bytes_inject; eauto.
      destr. eapply proj_bytes_not_inject in Heqo0; eauto. 2: congruence.
      erewrite proj_value_undef in H0; eauto.
      contradict H0. unfold Mptr. destr; simpl; congruence.
      generalize (proj_value_inject _ (quantity_chunk Mptr) _ _ INJ). intro VINJ.
      generalize (Val.load_result_inject _ Mptr _ _ VINJ). intro VINJ'.
      unfold is_ptr in H0. destr_in H0. inv H0. inv VINJ'.
      eexists; split. simpl. eauto.
      econstructor; eauto.
    - eapply Mem.loadbytes_range_perm; eauto. generalize (size_chunk_pos chunk); omega.
  Qed.

  Lemma loadbytesv_extends:
    forall chunk m m' v v' ra,
      Mem.extends m m' ->
      Val.lessdef v v' ->
      loadbytesv chunk m v = Some ra ->
      exists ra', loadbytesv chunk m' v' = Some ra' /\ Val.lessdef ra ra'.
  Proof.
    intros chunk m m' v v' ra MEXT VLD L.
    unfold loadbytesv in *.
    destr_in L. inv VLD.
    destr_in L.
    edestruct Mem.loadbytes_extends as (l' & L' & EXT); eauto.
    rewrite L'.
    - unfold encoded_ra in L |- *.
      repeat destr_in L.
      erewrite proj_bytes_inject; eauto.
      destr. eapply proj_bytes_not_inject in Heqo0; eauto. 2: congruence.
      erewrite proj_value_undef in H0; eauto.
      contradict H0. unfold Mptr. destr; simpl; congruence.
      generalize (proj_value_inject _ (quantity_chunk Mptr) _ _ EXT). intro VEXT.
      generalize (Val.load_result_inject _ Mptr _ _ VEXT). intro VEXT'.
      unfold is_ptr in H0. destr_in H0. inv H0. inv VEXT'. inv H2.
      eexists; split. simpl. eauto.
      rewrite Ptrofs.add_zero. econstructor; eauto.
  Qed.

  
  Lemma proj_value_inj_value:
    forall q v l,
      proj_value q l = v ->
      v <> Vundef ->
      inj_value q v = l.
  Proof.
    unfold proj_value.
    intros q v l PROJ NU.
    subst. destr. destr. destr.
    destruct q; simpl in Heqb;
      repeat match goal with
             | H: andb _ _ = true |- _ => rewrite andb_true_iff in H; destruct H
             | H: proj_sumbool (quantity_eq ?q1 ?q2) = true |- _ =>
               destruct (quantity_eq q1 q2); simpl in H; try congruence; subst
             | H: proj_sumbool (Val.eq ?q1 ?q2) = true |- _ =>
               destruct (Val.eq q1 q2); simpl in H; try congruence; subst
             | H: context [match ?a with _ => _ end] |- _ => destruct a eqn:?; simpl in *; intuition try congruence
             end.
  Qed.

  Lemma long_unsigned_ptrofs_repr_eq:
    Archi.ptr64 = true -> forall a, Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr a)) = Ptrofs.unsigned (Ptrofs.repr a).
  Proof.
    intros.
    unfold Ptrofs.to_int64.
    rewrite <- Ptrofs.agree64_repr; auto.
    rewrite Ptrofs.repr_unsigned. auto.
  Qed.

  Lemma int_unsigned_ptrofs_repr_eq:
    Archi.ptr64 = false -> forall a, Int.unsigned (Ptrofs.to_int (Ptrofs.repr a)) = Ptrofs.unsigned (Ptrofs.repr a).
  Proof.
    intros.
    unfold Ptrofs.to_int.
    rewrite <- Ptrofs.agree32_repr; auto.
    rewrite Ptrofs.repr_unsigned. auto.
  Qed.

  Lemma byte_decompose: forall i x, (Byte.unsigned i + x * 256) / 256 = x.
  Proof.
    intros.
    rewrite Z_div_plus_full.
    rewrite Zdiv_small. omega. apply Byte.unsigned_range. omega.
  Qed.

  Lemma ptrofs_wordsize: Ptrofs.zwordsize = 8 * size_chunk Mptr.
  Proof.
    unfold Ptrofs.zwordsize, Ptrofs.wordsize.
    unfold Wordsize_Ptrofs.wordsize. unfold Mptr.
    destr; omega.
  Qed.
  
  Lemma ptrofs_byte_modulus_ptr64:
    Archi.ptr64 = true ->
    Byte.modulus ^ 8 - 1 = Ptrofs.max_unsigned.
  Proof.
    unfold Ptrofs.max_unsigned. rewrite Ptrofs.modulus_power.
    rewrite ptrofs_wordsize.
    intros. unfold Mptr; rewrite H. simpl. reflexivity.
  Qed.

  Lemma ptrofs_byte_modulus_ptr32:
    Archi.ptr64 = false ->
    Byte.modulus ^ 4 - 1 = Ptrofs.max_unsigned.
  Proof.
    unfold Ptrofs.max_unsigned. rewrite Ptrofs.modulus_power.
    rewrite ptrofs_wordsize.
    intros. unfold Mptr; rewrite H. simpl. reflexivity.
  Qed.

  Lemma byte_compose_range:
    forall i x n,
      0 < n ->
      0 <= x < Byte.modulus ^ (n - 1) ->
      0 <= Byte.unsigned i + x * 256 < Byte.modulus ^ n.
  Proof.
    intros i x n POS RNG.
    split.
    generalize (Byte.unsigned_range i). omega.
    generalize (Byte.unsigned_range i). 
    change Byte.modulus with 256 in *. 
    replace n with ((n-1)+1) by omega. rewrite Zpower_exp by omega.
    change (256 ^ 1) with 256.
    assert (0 <= x * 256 < 256 ^ (n - 1) * 256).
    split. omega.
    apply Z.mul_lt_mono_pos_r. omega. omega.
    omega.
  Qed.

  Lemma le_m1_lt:
    forall a b,
      0 <= a < b ->
      0 <= a <= b - 1.
  Proof.
    intros; omega.
  Qed.

  Lemma byte_repr_plus i0 i:
    Byte.repr (Byte.unsigned i0 + i * 256) = i0.
  Proof.
    apply Byte.eqm_repr_eq.
    red. red. exists i.
    change Byte.modulus with 256 in *. omega.
  Qed.
  
  Lemma encode_decode_long:
    forall l,
      length l = 8%nat ->
      Archi.ptr64 = true ->
      encode_int 8 (Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr (decode_int l)))) = l.
  Proof.
    intros.
    repeat match goal with
           | H : length ?l = _ |- _ =>
             destruct l; simpl in H; inv H
           end. simpl.
    unfold encode_int, decode_int.
    unfold rev_if_be. destr.
    - simpl.
      rewrite Z.add_0_r.
      rewrite ! long_unsigned_ptrofs_repr_eq; auto.
      f_equal; rewrite ! Ptrofs.unsigned_repr.
      rewrite ! byte_decompose; apply Byte.repr_unsigned.
      rewrite <- ptrofs_byte_modulus_ptr64; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. apply byte_repr_plus.
      rewrite <- ptrofs_byte_modulus_ptr64; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
    - simpl.
      rewrite Z.add_0_r.
      rewrite ! long_unsigned_ptrofs_repr_eq; auto.
      f_equal; rewrite ! Ptrofs.unsigned_repr.
      apply byte_repr_plus.
      rewrite <- ptrofs_byte_modulus_ptr64; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply Byte.repr_unsigned.
      rewrite <- ptrofs_byte_modulus_ptr64; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
  Qed.

  Lemma encode_decode_int:
    forall l,
      length l = 4%nat ->
      Archi.ptr64 = false ->
      encode_int 4 (Int.unsigned (Ptrofs.to_int (Ptrofs.repr (decode_int l)))) = l.
  Proof.
    intros.
    repeat match goal with
           | H : length ?l = _ |- _ =>
             destruct l; simpl in H; inv H
           end. simpl.
    unfold encode_int, decode_int.
    unfold rev_if_be. destr.
    - simpl.
      rewrite Z.add_0_r.
      rewrite ! int_unsigned_ptrofs_repr_eq; auto.
      f_equal; rewrite ! Ptrofs.unsigned_repr.
      rewrite ! byte_decompose; apply Byte.repr_unsigned.
      rewrite <- ptrofs_byte_modulus_ptr32; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. apply byte_repr_plus.
      rewrite <- ptrofs_byte_modulus_ptr32; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
    - simpl.
      rewrite Z.add_0_r.
      rewrite ! int_unsigned_ptrofs_repr_eq; auto.
      f_equal; rewrite ! Ptrofs.unsigned_repr.
      apply byte_repr_plus.
      rewrite <- ptrofs_byte_modulus_ptr32; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply Byte.repr_unsigned.
      rewrite <- ptrofs_byte_modulus_ptr32; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
  Qed.

*)