Require Import LogicalRelations.
Require Import KLR.


(** * Games *)

(** ** Definition *)

Structure game :=
  {
    move : Type;
  }.

Inductive act (G : game) :=
  | ext (m : move G) :> act G
  | tau : act G.

Delimit Scope game_scope with game.
Bind Scope game_scope with game.

(** ** Abstraction relations *)

Record grel (G1 G2 : game) :=
  {
    gworld :> Type;
    gacc : relation gworld;
    ginitw : gworld -> Prop;
    move_rel : klr gworld (move G1) (move G2);
  }.

Arguments gworld {_ _}.
Arguments gacc {_ _}.
Arguments ginitw {_ _}.
Arguments move_rel {_ _}.

Delimit Scope grel_scope with grel.
Bind Scope grel_scope with grel.

Global Instance grel_kf {G1 G2} (GR : grel G1 G2) : KripkeFrame (gworld GR) :=
  {
    acc := gacc GR;
    winit := ginitw GR;
  }.

(** ** Identity and composition *)

Definition grel_id {G} : grel G G :=
  {|
    gworld := unit;
    gacc := ⊤;
    ginitw w := True;
    move_rel w := eq;
  |}.

Definition grel_compose {GA GB GC} (GRAB : grel GA GB) (GRBC : grel GB GC) :=
  {|
    gworld := gworld GRAB * gworld GRBC;
    gacc := gacc GRAB * gacc GRBC;
    ginitw := fun '(wab, wbc) => ginitw GRAB wab /\ ginitw GRBC wbc;
    move_rel :=
      fun '(wab, wbc) =>
        rel_compose (move_rel GRAB wab) (move_rel GRBC wbc);
  |}.


(** * Arrow game *)

Module Arrow.

  (** ** Definition *)

  Definition g (GA GB : game) : game :=
    {|
      move := move GA + move GB;
    |}.

  (** ** Abstraction relation *)

  Section GARROW_ABREL.
    Context {GA1 GA2} (GRA : grel GA1 GA2).
    Context {GB1 GB2} (GRB : grel GB1 GB2).

    Inductive world :=
      gw (wA : gworld GRA) (wB : gworld GRB) (c : bool).

    Inductive acc : relation world :=
      | acc_l wA wB c wA' : wA ~> wA' -> acc (gw wA wB c) (gw wA' wB false)
      | acc_r wA wB c wB' : wB ~> wB' -> acc (gw wA wB c) (gw wA wB' true).

    Inductive rel : klr world (move (g GA1 GB1)) (move (g GA2 GB2)) :=
      | rel_l wA wB a1 a2 :
          move_rel GRA wA a1 a2 ->
          rel (gw wA wB false) (inl a1) (inl a2)
      | rel_r wA wB b1 b2 :
          move_rel GRB wB b1 b2 ->
          rel (gw wA wB true) (inr b1) (inr b2).

    Definition r : grel (g GA1 GB1) (g GA2 GB2) :=
      {|
        gworld := world;
        gacc := acc;
        ginitw := fun '(gw wa wb c) => ginitw GRA wa /\ ginitw GRB wb;
        move_rel := rel;
      |}.
  End GARROW_ABREL.

End Arrow.

Infix "-o" := Arrow.g (at level 55, right associativity) : game_scope.
Infix "-o" := Arrow.r : grel_scope.
