Require Import LogicalRelations.
Require Import KLR.
Require Import Classical.
Require Import ClassicalChoice.
Require Import DecidableClass.
Require Import RTS.


(** * Multi-channel game *)

Module Pow.

  (** ** Game *)

  Definition g G I :=
    {|
      move := I * move G;
    |}.

  Infix "^" := g : game_scope.

  (** ** Simulations *)

  Section GREL.
    Context {G1 G2} (GR : grel G1 G2) (I : Type).

    Inductive world :=
      mkw (w : I -> GR) (i : I).

    Inductive acc : relation world :=
      mkw_acc w i w' i' :
        (forall j, j <> i' -> w' j = w j) ->
        w i' ~> w' i' ->
        acc (mkw w i) (mkw w' i').

    Inductive mrel : klr world (move (G1 ^ I)) (move (G2 ^ I)) :=
      mrel_intro w i m1 m2 :
        move_rel GR (w i) m1 m2 ->
        mrel (mkw w i) (i, m1) (i, m2).
          
    Definition r :=
      {|
        gworld := world;
        gacc := acc;
        ginitw := fun '(mkw w i) => forall j, ginitw GR (w j);
        move_rel := mrel;
      |}.
  End GREL.

  Arguments mkw {G1 G2 GR I}.
  Arguments acc {G1 G2 GR I}.

  Definition getw {G1 G2 GR I} : @r G1 G2 GR I -> GR :=
    fun '(mkw f i) => f i.

End Pow.

Infix "^" := Pow.g : game_scope.
Infix "^" := Pow.r : grel_scope.


(** * Relational maps *)

(** A common pattern when defining operators which operate over
  multiple components is that we keep keep a vector with an entry for
  each component. When the system is suspended, all entries will be
  continuations. When the system is running, most entries will still
  be continuations, but the entry for the currently running component
  will be a state instead.

  This file defines a data structure which facilitates keeping track
  of such composite states, and establishing simulations between
  them. *)

(** A type of maps with relational update operations. *)

Module RMap.

  (** ** Definition *)

  (** We continuously switch between two kinds of map. The "unfocused"
    maps are used for continuations and are simple functions. *)

  Definition unfocused I A :=
    I -> A.

  (** The "focused" map are focused on a specific index, which takes a
    value from a different type. This is used for running states. *)

  Inductive focused I A B :=
    foc (i : I) (b : B) (f : forall j, i <> j -> A).

  Arguments foc {I A B}.

  (** ** Operations *)

  (** The map is initialized in an unfocused state with a constant
    value. *)

  Definition init {I A} (a : A) : unfocused I A :=
    (fun _ => a).

  (** The first operation will focus it on a specific component and
    update the value. *)
  
  Inductive focus {I A B} i: unfocused I A -> A * (B -> focused I A B) -> Prop :=
    focus_intro f :
      focus i f (f i, fun b => foc i b (fun j _ => f j)).

  (** A focused map can be updated as follows. *)

  Inductive update {I A B} (b' : B) : focused I A B -> I * B * focused I A B -> Prop :=
    update_intro i b f :
      update b' (foc i b f) (i, b, foc i b' f).

  (** Later, we can unfocus the map again by providing a replacement
    value for [f i] *)

  Inductive unfocus {I A B}: focused I A B -> I * B * (A -> unfocused I A) -> Prop :=
    unfocus_intro i b f f' :
      (forall a j Hj, f' a j = f j Hj) ->
      (forall a, f' a i = a) ->
      unfocus (foc i b f) (i, b, f').

  (** ** Monotonicity *)

  (** We can build KLRs for these two kinds of maps. *)

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

End RMap.


(** * Multi-component transition systems *)

Module MC.

  (** ** Definition *)

  Section RTS.
    Context {G : game} {I S : Type}.

    Definition state :=
      RMap.focused I (RTS.cont G S) S.
    
    (** *** Continuations *)

    Inductive liftk (k: RMap.unfocused I (RTS.cont G S)): RTS.cont (G^I) state :=
      liftk_intro i ki q r f :
        RMap.focus i k (ki, f) ->
        ki q r ->
        liftk k (i, q) (RTS.resumption_map f r).

    (** *** Steps *)

    Inductive step (α : I -> rts G S) : rts (G ^ I) state :=
      | step_internal i si si' s s' :
          RMap.update si' s (i, si, s') ->
          α i si (RTS.internal si') ->
          step α s (RTS.internal s')
      | step_interacts i p si ki s f :
          RMap.unfocus s (i, si, f) ->
          α i si (RTS.interacts p ki) ->
          step α s (RTS.interacts (G := G ^ I) (i, p) (liftk (f ki)))
      | step_diverges s i si f :
          RMap.unfocus s (i, si, f) ->
          α i si RTS.diverges ->
          step α s RTS.diverges
      | step_goes_wrong s i si f :
          RMap.unfocus s (i, si, f) ->
          α i si RTS.goes_wrong ->
          step α s RTS.goes_wrong.

  End RTS.

  Arguments state : clear implicits.

  (** ** Simulations *)

  Global Instance liftk_sim :
    Monotonic
      (@liftk)
      (forallr GR, forallr - @ I, forallr R : klr _,
         |= RMap.unfocused_r GR I (RTS.cont_le GR R) ++>
            RTS.cont_le (GR ^ I) (RMap.focused_r GR I (RTS.cont_le GR R) R)).
  Proof.
  Admitted.

  Global Instance step_sim :
    Monotonic
      (@step)
      (forallr GR, forallr - @ I, forallr R : klr _,
         (- ==> RTS.sim GR R) ++>
         RTS.sim (GR ^ I) (RMap.focused_r GR I (RTS.cont_le GR R) R)).
  Proof.
  Admitted.

End MC.
