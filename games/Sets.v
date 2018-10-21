Require Import LogicalRelations.

Notation set U := (U -> Prop).

Definition subset {U} : relation (set U) :=
  - ==> impl.

Definition set_rel {A B} (R : rel A B) : rel (set A) (set B) :=
  set_le R /\ set_ge R.

Definition set_union {U} (s : set (set U)) : set U :=
  fun x => exists sx, s sx /\ sx x.

Lemma set_union_ub {U} (s : set (set U)) (sx : set U) :
  s sx -> subset sx (set_union s).
Proof.
  firstorder.
Qed.

Lemma set_union_lub {U} (s : set (set U)) (sy : set U) :
  (forall sx, s sx -> subset sx sy) ->
  subset (set_union s) sy.
Proof.
  firstorder.
Qed.

Definition set_inter {U} (s : set (set U)) : set U :=
  fun x => forall sx, s sx -> sx x.

Inductive set_map {A B} (f : A -> B) (sA : set A) : set B :=
  set_map_intro a :
    sA a -> set_map f sA (f a).

Hint Constructors set_map.

Global Instance set_map_le :
  Monotonic
    (@set_map)
    (forallr RA, forallr RB, (RA ++> RB) ++> set_le RA ++> set_le RB).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg sA1 sA2 HsA b1 Hb1.
  destruct Hb1 as [a1]. edestruct HsA as (a2 & Ha2 & Ha); eauto.
Qed.

Global Instance set_map_ge :
  Monotonic
    (@set_map)
    (forallr RA, forallr RB, (RA ++> RB) ++> set_ge RA ++> set_ge RB).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg sA1 sA2 HsA b2 Hb2.
  destruct Hb2 as [a2]. edestruct HsA as (a1 & Ha1 & Ha); eauto.
Qed.

Inductive set_bind {A B} (f : A -> set B) (sa: set A) : set B :=
  set_bind_intro a b :
    sa a -> f a b -> set_bind f sa b.

Hint Constructors set_bind.

Global Instance set_bind_le :
  Monotonic
    (@set_bind)
    (forallr RA, forallr RB, (RA ++> set_le RB) ++> set_le RA ++> set_le RB).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg sa sb Hs.
  intros _ [a1 b1 Ha1 Hb1].
  edestruct Hs as (a2 & Ha2 & Ha); eauto.
  edestruct Hfg as (b2 & Hb2 & Hb); eauto.
Qed.

Definition set_bind_all {A B} (f : A -> set B) (sA : set A) : set B :=
  set_union (set_map f sA).

Definition set_bind_ex {A B} (f : A -> set B) (sA : set A) : set B :=
  set_inter (set_map f sA).

(** The empty set *)

Definition empty {A} : set A :=
  fun _ => False.

Lemma empty_le {A B} (R : rel A B) sb :
  Related empty sb (set_le R).
Proof.
  destruct 1.
Qed.

Hint Extern 0 (Related empty _ (set_le _)) =>
  eapply empty_le : typeclass_instances.

Lemma empty_ge {A B} (R : rel A B) sa :
  Related sa empty (set_ge R).
Proof.
  destruct 1.
Qed.

Hint Extern 0 (Related _ empty (set_ge _)) =>
  eapply empty_ge : typeclass_instances.

(** This definition is identical to [eq]. *)

Inductive singl {A} (a : A) : set A :=
  singl_intro : singl a a.

Hint Constructors singl.

Global Instance singl_le :
  Monotonic (@singl) (forallr R, R ++> set_le R).
Proof.
  intros A B R a b Hab _ [ ]. eauto.
Qed.


