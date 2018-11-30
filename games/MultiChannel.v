Require Import LogicalRelations.
Require Import KLR.
Require Import Classical.
Require Import ClassicalChoice.
Require Import DecidableClass.
Require Import ATS.


(** * Side-by-side composition *)

Module Pow.

  (** ** Game *)

  Definition g G I :=
    {|
      question := I * question G;
      answer := I * answer G;
    |}.

  Definition r {G1 G2} (GR : grel G1 G2) (I : Type) :=
    Build_grel (g G1 I) (g G2 I)
      (grel_world GR)
      (k eq * question_rel GR)
      (k eq * answer_rel GR).

  Infix "^" := g : game_scope.
  Infix "^" := r : grel_scope.

  Definition mko {GA GB I} (i : I) (m : omove GA GB) : omove (GA ^ I) (GB ^ I) :=
    match m with
      | inl ma => inl (i, ma)
      | inr mq => inr (i, mq)
    end.

  Definition mkp {GA GB I} (i : I) (m : pmove GA GB) : pmove (GA ^ I) (GB ^ I) :=
    match m with
      | inl mq => inl (i, mq)
      | inr ma => inr (i, ma)
    end.

  (** ** Transition system *)

  Section ATS.
    Context {GA GB I} {S K : I -> Type} (α : forall i, ats GA GB (S i) (K i)).

    Inductive state :=
      st (i : I) (s : S i) (k : forall j, i <> j -> K j).

    Definition cont :=
      forall i : I, K i.

    Inductive step : relation state :=
      step_intro i s s' k :
        ATS.step (α i) s s' ->
        step (st i s k) (st i s' k).

    Inductive suspend : state -> pmove (GA ^ I) (GB ^ I) * cont -> Prop :=
      suspend_intro i s k m ki k' :
        ATS.suspend (α i) s (m, ki) ->
        (forall j Hj, k' j = k j Hj) ->
        k' i = ki ->
        suspend (st i s k) (mkp i m, k').

    Inductive resume : cont -> omove (GA ^ I) (GB ^ I) -> state -> Prop :=
      resume_intro i k m s :
        ATS.resume (α i) (k i) m s ->
        resume k (mko i m) (st i s (fun j _ => k j)).

    Inductive refuse : cont -> question (GB ^ I) -> Prop :=
      refuse_intro i k m :
        ATS.refuse (α i) (k i) m ->
        refuse k (i, m).

    Definition of :=
      ATS.Build_ats (GA ^ I) (GB ^ I) state cont step suspend resume refuse.

  End ATS.

  Arguments state : clear implicits.
  Arguments cont : clear implicits.

  (** ** Monotonicity *)

  (** We can build KLRs for these two kinds of maps. *)

  (*
  Section REL.
    Context {G1 G2} (GR : grel G1 G2) (I : Type).
    Context {A1 A2} (RA : klr GR A1 A2).
    Context {B1 B2} (RB : klr GR B1 B2).

    Definition unfocused_r : klr (GR^I)%grel (unfocused I A1) (unfocused I A2) :=
      fun '(Pow.mkw w i) f1 f2 => forall i, RA (w i) (f1 i) (f2 i).

    Inductive focused_r : klr (GR ^ I)%grel _ _ :=
      focused_r_intro w i b1 b2 f1 f2 :
        RB (w i) b1 b2 ->
        (forall j Hj, RA (w j) (f1 j Hj) (f2 j Hj)) ->
        focused_r (Pow.mkw w i) (foc i b1 f1) (foc i b2 f2).

    Global Instance init_r :
      Monotonic init ([] RA @@ [Pow.getw] ++> unfocused_r).
    Admitted.

    Global Instance focus_r :
      Monotonic focus
        (forallr - @ i,
         |= unfocused_r ++>
            k1 set_le (RA@@[Pow.getw] * ((<> RB@@[Pow.getw]) ++> <> focused_r))).
    Admitted.

    Global Instance update_r :
      Monotonic update
        (|= RB @@ [Pow.getw] ++> focused_r ++>
            k1 set_le (k eq * RB @@ [Pow.getw] * focused_r)).
    Admitted.

    Global Instance unfocus_r :
      Monotonic unfocus
        (|= focused_r ++>
            k1 set_le (k eq * RB@@[Pow.getw] *
                       ((<> RA@@[Pow.getw]) ++> <> unfocused_r))).
    Admitted.
  End REL.
*)

End Pow.

Infix "^" := Pow.g : game_scope.
Infix "^" := Pow.r : grel_scope.
