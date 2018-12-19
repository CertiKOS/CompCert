Require Import LogicalRelations.
Require Import KLR.
Require Import List.


(** * Elementary games *)

(** ** Definition *)

Structure game :=
  {
    question : Type;
    answer : Type;
  }.

Delimit Scope game_scope with game.
Bind Scope game_scope with game.

(** ** Refinement conventions *)

Record grel (G1 G2 : game) :=
  {
    grel_world :> Type;
    question_rel : klr grel_world (question G1) (question G2);
    answer_rel : klr grel_world (answer G1) (answer G2);
  }.

Arguments grel_world {_ _}.
Arguments question_rel {_ _}.
Arguments answer_rel {_ _}.

Delimit Scope grel_scope with grel.
Bind Scope grel_scope with grel.

Definition grel_id {G} : grel G G :=
  {|
    grel_world := unit;
    question_rel w := eq;
    answer_rel w := eq;
  |}.

Definition grel_compose {GA GB GC} (GRAB : grel GA GB) (GRBC : grel GB GC) :=
  {|
    grel_world := grel_world GRAB * grel_world GRBC;
    question_rel :=
     fun '(wab, wbc) =>
        rel_compose (question_rel GRAB wab) (question_rel GRBC wbc);
    answer_rel :=
     fun '(wab, wbc) =>
        rel_compose (answer_rel GRAB wab) (answer_rel GRBC wbc);
  |}.


(** * Arrow game *)

(** ** Moves and actions *)

Definition oqmove (GA GB : game) := question GB.
Definition pqmove (GA GB : game) := question GA.
Definition oamove (GA GB : game) := answer GA.
Definition pamove (GA GB : game) := answer GB.

Inductive omove {GA GB : game} :=
  | oa (m : oamove GA GB) :> omove
  | oq (m : oqmove GA GB) :> omove.

Arguments omove : clear implicits.

Inductive pmove {GA GB : game} :=
  | pq (m : pqmove GA GB) :> pmove
  | pa (m : pamove GA GB) :> pmove.

Arguments pmove : clear implicits.

Inductive move {GA GB : game} : Type :=
  | om (m : omove GA GB) :> move
  | pm (m : pmove GA GB) :> move.

Arguments move : clear implicits.

Inductive action {GA GB : game} : Type :=
  | ext (m : move GA GB) :> action
  | tau : action
  | refused : action
  | crash : action.

Arguments action : clear implicits.

(** ** Plays *)

(** A play is a list of actions. *)

Definition play GA GB :=
  list (action GA GB).

Inductive player : Type := O | P.
Definition vstate : Type := player * bool.

(** Valid plays alternate between O and P moves, with P able to delay
  its moves with [tau], or immediately reject O questions. *)

Inductive valid {GA GB : game} : vstate -> vstate -> play GA GB -> Prop :=
  | vnil (q : vstate) :
      valid q q nil
  | vo (m : omove GA GB) (s : play GA GB) (q : vstate) :
      valid (P, true) q s ->
      valid (O, true) q (ext (om m) :: s)
  | vp (b : bool) (m : pmove GA GB) (s : play GA GB) (q : vstate) :
      valid (O, true) q s ->
      valid (P, b) q (ext (pm m) :: s)
  | vtau (b : bool) (s : play GA GB) (q : vstate) :
      valid (P, false) q s ->
      valid (P, b) q (tau :: s)
  | vref :
      valid (P, true) (O, false) (refused :: nil).

(** ** Frames *)

(** In addition, the Kripke frame we use to formulate simulations for
  the game [A -> B] enforces a stack discipline, where every answer
  corresponds to the most recent pending question. *)

Section REL.
  Context {GA1 GA2} (GRA : grel GA1 GA2).
  Context {GB1 GB2} (GRB : grel GB1 GB2).

  Inductive qmove_rel : klr (GRA + GRB) (move GA1 GB1) (move GA2 GB2) :=
    | qmove_rel_pq w m1 m2 :
        question_rel GRA w m1 m2 ->
        qmove_rel (inl w) (pq m1) (pq m2)
    | qmove_rel_oq w m1 m2 :
        question_rel GRB w m1 m2 ->
        qmove_rel (inr w) (oq m1) (oq m2).

  Inductive amove_rel : klr (GRA + GRB) (move GA1 GB1) (move GA2 GB2) :=
    | amove_rel_pa w m1 m2 :
        answer_rel GRA w m1 m2 ->
        amove_rel (inl w) (oa m1) (oa m2)
    | amove_rel_oa w m1 m2 :
        answer_rel GRB w m1 m2 ->
        amove_rel (inr w) (pa m1) (pa m2).

  Definition gworld :=
    list (GRA + GRB).

  Inductive gacc : move GA1 GB1 * move GA2 GB2 -> relation gworld :=
    | gacc_question w ws m1 m2 :
        qmove_rel w m1 m2 ->
        gacc (m1, m2) ws (w::ws)
    | gacc_answer w ws m1 m2 :
        amove_rel w m1 m2 ->
        gacc (m1, m2) (w::ws) ws.

  Inductive play_rel : klr gworld (play GA1 GB1) (play GA2 GB2) :=
    | pnil_rel :
        play_rel nil nil nil
    | pext_rel ws s1 s2 ws' m1 m2 :
        play_rel ws s1 s2 ->
        gacc (m1, m2) ws ws' ->
        play_rel ws' (s1 ++ ext m1 :: nil) (s2 ++ ext m2 :: nil)
    | ptau_rel ws s1 s2 :
        play_rel ws s1 s2 ->
        play_rel ws (s1 ++ tau :: nil) (s2 ++ tau :: nil)
    | prefused_rel ws s1 s2 :
        play_rel ws s1 s2 ->
        play_rel ws (s1 ++ refused :: nil) (s2 ++ refused :: nil).

  (** These predicate are useful for strengthening simulation
    relations to ensure the worlds are well-formed. *)

  Inductive oworld : gworld -> Prop :=
    | oworld_nil : oworld nil
    | oworld_cons w ws : pworld ws -> oworld (inl w :: ws)
  with pworld : gworld -> Prop :=
    | pworld_cons w ws : oworld ws -> pworld (inr w :: ws).

  (** We provide various instances of [KripkeFrame] which apply [gacc]
    to different kinds of moves. *)

  Global Instance move_frame: KripkeFrame (move GA1 GB1 * move GA2 GB2) _ :=
    {
      acc := gacc;
    }.

  Global Instance pmove_frame: KripkeFrame (pmove GA1 GB1 * pmove GA2 GB2) _ :=
    {
      acc := fun '(m1, m2) => gacc (pm m1, pm m2);
    }.

  Global Instance omove_frame: KripkeFrame (omove GA1 GB1 * omove GA2 GB2) _ :=
    {
      acc := fun '(m1, m2) => gacc (om m1, om m2);
    }.

  Global Instance oqmove_frame: KripkeFrame (oqmove GA1 GB1 * oqmove GA2 GB2) _:=
    {
      acc := fun '(m1, m2) => gacc (om (oq m1), (om (oq m2)));
    }.
End REL.
