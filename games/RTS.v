Require Import LogicalRelations.
Require Import OptionRel.
Require Import List.
Require Import Axioms.
Require Import PCST.

(** * Receptive transition systems *)

(** We do metatheory in a setting ...
  The whole thing in this file is parametrized by a set of events [E]
  and a set of moves [M]. Events can only ever serve as outputs,
  whereas moves can be used both as outputs and inputs.

  In addition to events and moves, we introduce three special outputs:
  the output [int] indicates internal activity (τ transition);
  the output [div] indicates silent divergence; finally,
  the output [undef] indicates that the program goes wrong. *)

Section RTS.
  Context (E M : Type).

  Inductive output :=
    | event (e : E)
    | move (m : M)
    | int
    | div
    | undef.

  (** A step in the transition system, defined as follows, describes
    how the execution will unfold as a function of incoming moves,
    and what outputs may be emitted with transitions to what states. *)

  Record step {A} :=
    {
      input_step : M -> A;
      output_step : output -> A -> Prop;
    }.

  Arguments step : clear implicits.

  (** A receptive transition system associates such a step to each
    possible state. *)

  Definition rts A :=
    A -> step A.

  
  (** * Simulations *)

  (** Note: we may not want to require input simulation for unsafe
    states. We could push back the safety clause to sim *)

  Record step_sim {A B} (R : rel A B) (x : step A) (y : step B) :=
    Build_step_sim {
      input_step_sim m :
        R (input_step x m) (input_step y m);
      output_step_sim m a :
        output_step x m a ->
        exists b,
          output_step y undef b \/
          output_step y m b /\ R a b;
    }.

  Definition sim {A B} (R : rel A B) (α : rts A) (β : rts B) :=
    forall a b, R a b -> step_sim R (α a) (β b).

  Global Instance step_sim_id A :
    Reflexive (step_sim (@eq A)).
  Proof.
    intros. split; eauto.
  Qed.

  Lemma step_sim_compose A B C (R1 : rel A B) (R2 : rel B C) x y z :
    step_sim R1 x y ->
    step_sim R2 y z ->
    step_sim (rel_compose R1 R2) x z. 
  Proof.
    intros Hxy Hyz. split.
    - intros; eexists; split; eapply input_step_sim; eauto.
    - intros m a Ha. unfold rel_compose.
      edestruct (@output_step_sim A B) as [b [Hb | [Hb Hab]]]; eauto;
      edestruct (@output_step_sim B C) as [c [Hc | [Hc Hbc]]]; eauto 10.
  Qed.

  Lemma output_step_sim_undef {A B} (R : rel A B) x y a :
    step_sim R x y ->
    output_step x undef a ->
    exists b, output_step y undef b.
  Proof.
    intros Hxy Ha.
    edestruct @output_step_sim as [b [Hb | [Hb Hab]]]; eauto.
  Qed.


  (** * Tau transitions *)

  Section TAU.
    Context {A} (α : rts A).

    CoInductive pull_forever (a : A) : Prop :=
      | pull_forever_step a' :
          output_step (α a) int a' ->
          pull_forever a' ->
          pull_forever a
      | pull_forever_undef a' :
          output_step (α a) undef a' ->
          pull_forever a.

    Inductive pull_reachable (a : A) : A -> Prop :=
      | pull_reachable_refl :
          pull_reachable a a
      | pull_reachable_step a' a'' :
          output_step (α a) int a' ->
          pull_reachable a' a'' ->
          pull_reachable a a''.

    Inductive pull_output_step : option A -> output -> option A -> Prop :=
      | pull_finite a a' m a'' :
          pull_reachable a a' ->
          output_step (α a') m a'' ->
          pull_output_step (Some a) m (Some a'')
      | pull_div a :
          pull_forever a ->
          pull_output_step (Some a) div None.

    Definition pull : rts (option A) :=
      fun x =>
        {|
          input_step m :=
            match x with
              | Some a => Some (input_step (α a) m)
              | None => None
            end;
          output_step :=
            pull_output_step x;
        |}.
  End TAU.

  Hint Constructors pull_output_step.
  Hint Constructors option_rel.

  Lemma pull_reachable_sim {A B} R (α : rts A) (β : rts B) a b a' :
    sim R α β ->
    R a b ->
    pull_reachable α a a' ->
    exists b',
      pull_reachable β b b' /\
      ((exists b'', output_step (β b') undef b'') \/ R a' b').
  Proof.
    intros Hαβ Hab Ha'. revert b Hab.
    induction Ha'; intros.
    - eauto using pull_reachable_refl.
    - edestruct @output_step_sim as [b' [Hb' | [Hb' Hab']]]; eauto.
      + eauto using pull_reachable_refl.
      + edestruct IHHa' as (b'' & Hb'' & Hab''); eauto.
        eauto using pull_reachable_step.
  Qed.

  Lemma pull_forever_sim :
    Monotonic (@pull_forever) (forallr R, sim R ++> R ++> impl).
  Proof.
    intros A B R α β Hαβ. cofix IH. intros a b Hab H.
    destruct H.
    - edestruct @output_step_sim as [b' [Hb' | [Hb' Hab']]]; eauto.
      + eapply pull_forever_undef; eauto.
      + eapply pull_forever_step; eauto.
        eapply IH; eauto.
    - edestruct @output_step_sim_undef as [b' Hb']; eauto.
      eapply pull_forever_undef; eauto.
  Qed.

  Global Instance pull_sim :
    Monotonic (@pull) (forallr R, sim R ++> sim (option_rel R)).
  Proof.
    intros A B R α β Hαβ a b Hab.
    split; simpl.
    - intros m.
      destruct Hab; constructor.
      apply input_step_sim; eauto.
    - intros m a' Ha'.
      destruct Ha' as [a a' m a'' Ha' Ha'' | a Ha].
      + inversion Hab; clear Hab; subst. rename y into b.
        edestruct @pull_reachable_sim as (b' & Hb' & [[b'' Hb''] | Hab']); eauto.
        edestruct @output_step_sim as [b'' [Hb'' | [Hb'' Hab'']]]; eauto.
        exists (Some b''). right. split; eauto. rauto.
      + inversion Hab; clear Hab; subst. rename y into b.
        exists None. right. split; constructor.
        eapply pull_forever_sim; eauto.
  Qed.


  (** * Pruning *)

  Definition prune {A} (α : rts A) (P : output -> Prop) : rts A :=
    fun a =>
      {|
        input_step := input_step (α a);
        output_step m a' := output_step (α a) m a' /\ (P m -> m = undef);
      |}.

  Global Instance prune_sim :
    Monotonic (@prune) (forallr R, sim R ++> (- ==> impl) --> sim R).
  Proof.
    intros A B R α β Hαβ P Q HPQ a b Hab.
    split; simpl.
    - intros. eapply @input_step_sim; eauto.
    - intros m a' [Ha' Hm]. repeat red in HPQ.
      edestruct @output_step_sim as [b' [Hb' | [Hb' Hab']]]; eauto 10.
  Qed.

  Lemma prune_idemp {A} (α : rts A) (P : output -> Prop) :
    sim eq (prune (prune α P) P) (prune α P).
  Proof.
    split; simpl; subst; intuition eauto.
  Qed.

  Lemma prune_decr {A} (α : rts A) (P : output -> Prop) :
    sim eq (prune α P) α.
  Proof.
    split; simpl; subst; intuition eauto.
  Qed.


  (** * Resolution operator *)

  Section RES.
    Context {A} (α : rts A) (dom : M -> Prop) (a0 : A).

    Inductive res_output_step (a : A) : output -> A -> Prop :=
      | res_output_pass m a' :
          output_step (α a) m a' ->
          res_output_step a m a'
      | res_output_dom q a' :
          dom q ->
          output_step (α a) (move q) a' ->
          res_output_step a int (input_step (α a0) q).

    Definition res : rts A :=
      fun a =>
        {|
          input_step := input_step (α a);
          output_step := res_output_step a;
        |}.
  End RES.

  Global Instance res_sim :
    Monotonic (@res) (forallr R, sim R ++> - ==> R ++> sim R).
  Proof.
    intros A B R α β Hαβ dom a0 b0 Hab0 a b Hab.
    split; simpl.
    - eapply input_step_sim; eauto.
    - intros m a' Ha'.
      destruct Ha'.
      + edestruct @output_step_sim as (b' & [Hb' | [Hb' Hab']]);
        eauto using res_output_pass.
      + edestruct @output_step_sim as (b' & [Hb' | [Hb' Hab']]);
        eauto using res_output_dom, res_output_pass.
        exists (input_step (β b0) q).
        right. split; eauto using res_output_dom.
        eapply input_step_sim. eauto.
  Qed.

  Lemma res_incr {A} (α : rts A) dom a0 :
    sim eq α (res α dom a0).
  Proof.
    intros a _ [].
    split; simpl; eauto using res_output_pass.
  Qed.

  Lemma res_idemp {A} (α : rts A) dom a0 :
    sim eq (res (res α dom a0) dom a0) (res α dom a0).
  Proof.
    intros a _ []. split; simpl; eauto.
    intros _ _ [m a' Ha' | q a' Hq Ha']; simpl in *; eauto.
    inversion Ha' as [m xa' Hxa' | ]; clear Ha'; subst.
    eauto using res_output_dom.
  Qed.
End RTS.
