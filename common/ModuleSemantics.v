
Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.
Require Import Sets.

(** * Flat composition *)

(** The flat composition of transition systems essentially corresponds
  to the union of strategies: if component [i] handles a given query,
  then the flat composition will handle it in a similar way. However,
  the components cannot call each other. *)

Module SFComp.
  Section FLATCOMP.
    Context (ge: Senv.t).
    Context {li} (L1 L2: semantics li).

    Definition genv: Type := genvtype L1 * genvtype L2.

    Inductive state {A B} :=
      | state_l (s: A) (k: cont li B)
      | state_r (s: B) (k: cont li A).

    Definition liftk {A B} (k1: cont li A) (k2: cont li B): cont li state :=
      fun q =>
        match k1 q, k2 q with
          | Some S1, None => Some (set_map (fun S => state_l S k2) S1)
          | None, Some S2 => Some (set_map (fun S => state_r S k1) S2)
          | Some _, Some _ => Some (fun _ => False)
          | None, None => None
        end.

    Inductive step (ge: genv): state -> trace -> state -> Prop :=
      | step_l s t s' k:
          Smallstep.step L1 (fst ge) s t s' ->
          step ge (state_l s k) t (state_l s' k)
      | step_r s t s' k:
          Smallstep.step L2 (snd ge) s t s' ->
          step ge (state_r s k) t (state_r s' k).

    Definition initial_state: cont li state :=
      liftk
        (initial_state L1)
        (initial_state L2).

    Inductive final_state: state -> reply li -> _ -> Prop :=
      | final_state_l s r k k':
          Smallstep.final_state L1 s r k ->
          final_state (state_l s k') r (liftk k k')
      | final_state_r s r k k':
          Smallstep.final_state L2 s r k ->
          final_state (state_r s k') r (liftk k' k).

    Definition semantics :=
      {|
        Smallstep.genvtype := genv;
        Smallstep.state := state;
        Smallstep.step := step;
        Smallstep.initial_state := initial_state;
        Smallstep.final_state := final_state;
        Smallstep.globalenv := (globalenv L1, globalenv L2);
        Smallstep.symbolenv := ge;
      |}.

    Lemma semantics_determinate:
      determinate L1 ->
      determinate L2 ->
      determinate semantics.
    Proof.
      intros HL1 HL2.
      split.
      - intros s t1 s1 t2 s2 H1 H2.
        destruct H1; inversion H2; clear H2; subst.
        edestruct (sd_determ HL1 s t s' t2 s'0); simpl; eauto using f_equal2.
    Abort.

    End FLATCOMP.
End SFComp.

(** * Resolution operator *)

(** To go from the flat composition to horizontal composition, we
  introduce the following resolution operator. [Res] eliminates
  external calls to internal functions by using the corresponding
  query to immediately reenter the component. Note that this operator
  is only well-behaved for deterministic transition systems: in a
  nondeterministic transition system, a switching final state may
  coexist with other steps. If the switch results in a query that goes
  initially wrong, this behavior would be cancelled out by the
  alternative step. *)

Module SRes.
  Section RESOLVE.
    Context {li} (sw: reply li -> query li) (L: Smallstep.semantics li).

    Inductive step ge : state L -> trace -> state L -> Prop :=
      | step_internal s t s':
          Smallstep.step L ge s t s' ->
          step ge s t s'
      | step_switch s r k s':
          Smallstep.final_state L s r k ->
          resume k (sw r) s' ->
          step ge s E0 s'.

    Inductive final_state : state L -> reply li -> _ -> Prop :=
      final_state_intro s r k :
        Smallstep.final_state L s r k ->
        k (sw r) = None ->
        final_state s r k.

    Definition semantics: Smallstep.semantics li :=
      {|
        Smallstep.state := state L;
        Smallstep.step := step;
        Smallstep.initial_state := initial_state L;
        Smallstep.final_state := final_state;
        Smallstep.globalenv := globalenv L;
        Smallstep.symbolenv := symbolenv L;
      |}.
  End RESOLVE.
End SRes.

(** * Horizontal composition *)

(** Applying the resolution operator to the flat composition of
  some transitions systems gives us horizontal composition. *)

Module SHComp.
  Section HCOMP.
    Context (ge: Senv.t).
    Context {li} (L1 L2: semantics (li -o li)).

    Definition sw (r : reply (li -o li)) : query (li -o li) :=
      match r with
        | inl qA => inr qA
        | inr rB => inl rB
      end.

    Definition semantics :=
      SRes.semantics sw (SFComp.semantics ge L1 L2).
  End HCOMP.
End SHComp.
