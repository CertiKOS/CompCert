
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

Module FComp.
  Section FLATCOMP.
    Context (ge: Senv.t).
    Context {li} (L1 L2: semantics li).

    Definition genv: Type := genvtype L1 * genvtype L2.

    Inductive state {A B} :=
      | running (s: A + B) (k: cont li (A + B))
      | conflict.

    Definition inlk {A B} (k: cont li A) : cont li (A + B) :=
      fun q => option_map (set_map inl) (k q).

    Definition inrk {A B} (k: cont li B) : cont li (A + B) :=
      fun q => option_map (set_map inr) (k q).

    Definition liftk {A B} (k1 k2: cont li (A + B)): cont li state :=
      fun q =>
        match k1 q, k2 q with
          | Some S1, None => Some (set_map (fun S => running S k2) S1)
          | None, Some S2 => Some (set_map (fun S => running S k1) S2)
          | Some _, Some _ => Some (singl conflict)
          | None, None => None
        end.

    Inductive step (ge: genv): state -> trace -> state -> Prop :=
      | step_l s t s' k:
          Smallstep.step L1 (fst ge) s t s' ->
          step ge (running (inl s) k) t (running (inl s') k)
      | step_r s t s' k:
          Smallstep.step L2 (snd ge) s t s' ->
          step ge (running (inr s) k) t (running (inr s') k).

    Definition initial_state: cont li state :=
      liftk
        (inlk (initial_state L1))
        (inrk (initial_state L2)).

    Inductive final_state: state -> reply li -> _ -> Prop :=
      | final_state_l s1 r1 k1 k':
          Smallstep.final_state L1 s1 r1 k1 ->
          final_state (running (inl s1) k') r1 (liftk (inlk k1) k')
      | final_state_r s2 r2 k2 k':
          Smallstep.final_state L2 s2 r2 k2 ->
          final_state (running (inr s2) k') r2 (liftk (inrk k2) k').

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
    End FLATCOMP.
End FComp.

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

Module Res.
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
End Res.

(** * Horizontal composition *)

(** Applying the resolution operator to the flat composition of
  some transitions systems gives us horizontal composition. *)

Module HComp.
  Section HCOMP.
    Context (ge: Senv.t).
    Context {li} (L1 L2: semantics (li -o li)).

    Definition sw (r : reply (li -o li)) : query (li -o li) :=
      match r with
        | inl qA => inr qA
        | inr rB => inl rB
      end.

    Definition semantics :=
      Res.semantics sw (FComp.semantics ge L1 L2).
  End HCOMP.
End HComp.
