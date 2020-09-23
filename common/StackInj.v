Require Import Coqlib Tactics StackADT.

(* Specifying the shape of stack injection functions *)

(* [compat_frameinj_rec l g ns nt]
   [ns] is the stage position in the source stack, [nt] in the target stack.
   [l] is the target call stack.
   [g] is compatible with [l] if the corresponding frames are injected correctly by [g].
   Tailcalled stack frames are injected into the current target stage and we do
   not increment the target stage.
 *)

(* Fixpoint compat_frameinj_rec (l: list nat) (g: frameinj) (ns nt: nat) := *)
(*   match l with *)
(*     nil => forall i j (LE: (ns <= i)%nat) (Gi: g i = Some j), (nt <= j)%nat *)
(*   | n :: l => *)
(*     (forall i, ns <= i < ns + n -> g i = Some nt)%nat /\ compat_frameinj_rec l g (ns + n) (S nt) *)
(*   end. *)

(* Definition compat_frameinj l g := compat_frameinj_rec l g O O. *)

(* Lemma compat_frameinj_rec_above: *)
(*   forall l g ns nt (CFG: compat_frameinj_rec l g ns nt) *)
(*     i j (Gi: g i = Some j) (LE: (ns <= i)%nat), *)
(*     (nt <= j)%nat. *)
(* Proof. *)
(*   induction l; simpl; intros; eauto. *)
(*   destruct CFG as (GNS & GABOVE). *)
(*   destruct (lt_dec i (ns + a)); auto. *)
(*   rewrite GNS in Gi; auto. inv Gi; omega. *)
(*   eapply IHl in GABOVE. 2: apply Gi. omega. omega. *)
(* Qed. *)

Local Open Scope Z_scope.

Inductive sizes : frameinj -> stack -> stack -> Prop :=
| sizes_nil: sizes nil nil nil
| sizes_cons g s1 s2 t1 n t2:
    sizes g (drop (S n) s1) s2 ->
    take (S n) s1 = Some t1 ->
    Exists (fun f1 => size_frames t2 <= size_frames f1) t1 ->
    sizes (S n::g) s1 (t2 :: s2).

Fixpoint sum (l: list Z) :=
  match l with
    nil => 0
  | a::r => a + sum r
  end.

Lemma size_stack_app:
  forall s1 s2,
    size_stack (s1 ++ s2) = size_stack s1 + size_stack s2.
Proof.
  induction s1; simpl; intros; eauto. rewrite IHs1. omega.
Qed.

Opaque minus.

Lemma list_nats_S:
  forall n,
    list_nats (S n) = map S (list_nats n) ++ O :: nil.
Proof.
  induction n; simpl; intros; eauto.
  rewrite <- IHn. simpl. auto.
Qed.

Fixpoint opt_concat {A} (l: list (option (list A))) : option (list A) :=
  match l with
    nil => Some nil
  | None :: l => None
  | Some a::l =>
    match opt_concat l with
    | None => None
    | Some r => Some (a ++ r)
    end
  end.

Fixpoint minl (l: list nat) : option nat :=
  match l with
  | nil => None
  | a::r => match minl r with
             Some b => Some (Nat.min a b)
           | None => Some a
           end
  end.

Lemma lnr_concat:
  forall {A B} (f: A -> list B)
    (LNRf: forall i, list_norepet (f i))
    (DISJ: forall i j, i <> j -> list_disjoint (f i) (f j))
    (l2: list A)
    (LNR2: list_norepet l2),
    list_norepet (concat (map f l2)).
Proof.
  intros A B f LNRf DISJ l2.
  induction 1; simpl. constructor.
  apply list_norepet_app. split; [|split]; auto.
  red; intros.
  rewrite concat_In in H1.
  destruct H1 as (xx & INx & INMAP).
  rewrite in_map_iff in INMAP. destruct INMAP as (a & Fa & INFa).
  subst.
  eapply DISJ. 2: apply H0. 2: apply INx. congruence.
Qed.

Lemma filter_norepet:
  forall {A} f (l: list A),
    list_norepet l ->
    list_norepet (filter f l).
Proof.
  induction 1; simpl; intros; try destr; econstructor; eauto.
  rewrite filter_In. intros (B & C). congruence.
Qed.

Lemma size_frames_le_size_stack:
  forall f s,
    In f s ->
    size_frames f <= size_stack s.
Proof.
  induction s; simpl; intros; eauto. easy.
  destruct H; subst. generalize (size_stack_pos s); omega.
  generalize (size_frames_pos a). trim IHs; auto. omega.
Qed.

Lemma sizes_size_stack:
  forall g s1 s2
    (SZ: sizes g s1 s2),
    size_stack s2 <= size_stack s1.
Proof.
  induction 1; simpl; intros; eauto.
  omega.
  rewrite (take_drop _ _ _ H).
  rewrite size_stack_app.
  cut (size_frames t2 <= size_stack t1). intros; omega.
  rewrite Exists_exists in H0. destruct H0 as (f1 & INf1 & LE).
  etransitivity. apply LE.
  eapply size_frames_le_size_stack; eauto.
Qed.

Lemma frame_at_pos_tl:
  forall f s i,
    f @ s : S i <-> f @ tl s : i.
Proof.
  split. destruct s. inversion 1. rewrite nth_error_nil in H0; inv H0.
  intros.
  apply frame_at_pos_cons_inv in H; auto. omega.
  destruct s; simpl in *; intros. 
  inv H; rewrite nth_error_nil in H0. inv H0.
  apply frame_at_pos_cons. auto.
Qed.

Lemma tl_drop:
  forall {A} n (l: list A),
    drop n (tl l) = drop (S n) l.
Proof.
  reflexivity.
Qed.

Lemma compat_sizes_drop:
  forall n g m1 m2
    (SZ: sizes (S n :: g) m1 m2),
    sizes g (drop (S n) m1) (tl m2).
Proof.
  intros. inv SZ. simpl.
  rewrite tl_drop. auto.
Qed.

Lemma size_stack_drop:
  forall n l,
    size_stack (drop n l) <= size_stack l.
Proof.
  induction n; simpl; intros. reflexivity.
  etransitivity. apply IHn. apply size_stack_tl.
Qed.

Lemma length_tl:
  forall {A} (l: list A),
    length (tl l) = (length l - 1)%nat.
Proof.
  destruct l; simpl; auto. omega.
Qed.