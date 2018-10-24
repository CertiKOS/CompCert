Require Import LogicalRelations.
Require Import Sets.
Require Import ClassicalChoice.


(** * The oracle monad *)

(** ** Definition *)

(** The oracle monad is used to model a computation with input
  non-determinism. A computation consists of the type of oracles,
  representing the possible behaviors of the environment, as well
  as a function from oracles to values specifying the result of the
  computation for each possible environment behavior. *)

Record ndi A :=
  ndc {
    oracle : Type;
    result : oracle -> A;
  }.

Arguments ndc {_ _} _.
Arguments oracle {_} _.
Arguments result {_} _.

Bind Scope ndi_scope with ndi.
Delimit Scope ndi_scope with ndi.

(** For the 'return' operation, the oracle is trivial and the only
  possible result is the specified value. *)

Definition nret {A} (a : A) : ndi A :=
  {|
    result := fun _ : unit => a;
  |}.

Notation "[ a ]" := (nret a).

(** For the 'bind' operation, an oracle is a dependent pair consisting
  of an oracle for the first computation, together with an oracle for
  the resulting second computation. *)

Definition nbind {A B} (f : A -> ndi B) (na : ndi A) : ndi B :=
  {|
    result := fun '(existT _ i j) => result (f (result na i)) j;
  |}.

Notation "x <- X ; Y" := (nbind (fun x => Y%ndi) X%ndi)
  (at level 100, right associativity) : ndi_scope.

(** ** Relator *)

(** A computation [na] refines a computation [nb] if for any oracle
  of [nb], there is an oracle of [na] that yields a related result. *)

Definition ndi_ref {A B} (R : rel A B) : rel (ndi A) (ndi B) :=
  fun na nb =>
    forall j, exists i, R (result na i) (result nb j).

Global Instance nret_ref :
  Monotonic (@nret) (forallr R, R ++> ndi_ref R).
Proof.
  firstorder.
Qed.

Global Instance nbind_ref :
  Monotonic
    (@nbind)
    (forallr RA, forallr RB, (RA ++> ndi_ref RB) ++> ndi_ref RA ++> ndi_ref RB).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg na1 na2 Hna [i2 j2].
  destruct (Hna i2) as (i1 & Hnb). apply Hfg in Hnb.
  destruct (Hnb j2) as (j1 & Hb). exists (existT _ i1 j1).
  assumption.
Qed.

(** ** Nondeterministic input *)

(** The following operation models a computation which reads an input
  of a given type from the environment. *)

Definition any (T : Type) :=
  {|
    result := fun (x : T) => x;
  |}.

Global Instance any_ref :
  Monotonic (@any) (forallr -, ndi_ref eq).
Proof.
  intros T i. simpl. eauto.
Qed.

(** As a special case, we can ask the environment for a proof; this
  models a "rely" condition. *)

Definition rely (P : Prop) :=
  any P.

Global Instance rely_ref :
  Monotonic (@rely) (forallr HPQ @ P Q : flip impl, ndi_ref ⊤).
Proof.
  intros P Q HPQ HQ. exists (HPQ HQ). constructor.
Qed.

(** ** Using oracle computations *)

(** When a computation produces a [Prop], we can interpret it as a
  "guarantee" condition and assert that it holds no matter what the
  environment does. *)

Definition guarantee (nP : ndi Prop) :=
  forall i, result nP i.

Global Instance guarantee_ref :
  Monotonic (@guarantee) (ndi_ref impl ++> impl).
Proof.
  intros P Q HPQ HP i.
  specialize (HPQ i) as [j HQ].
  eauto.
Qed.

(** When a computation produces a set, we can obtain a set of
  computations producing values, where each computation in the set has
  "pre-chosen" which value to pick from the set for any possible
  oracle. *)

Inductive nchoice {A} (ns : ndi (set A)) : set (ndi A) :=
  nchoice_intro (F : oracle ns -> A) :
    (forall i, result ns i (F i)) ->
    nchoice ns (ndc F).

Global Instance nchoice_ref :
  Monotonic (@nchoice) (forallr R, ndi_ref (set_le R) ++> set_le (ndi_ref R)).
Proof.
  intros A B R nsa nsb Hns na [Fa HFa].
  apply choice in Hns as [f Hf].
  destruct (choice (fun j bj => result nsb j bj /\ R (Fa (f j)) bj)) as [Fb HFb].
  {
    firstorder.
  }
  exists (ndc Fb). split.
  - constructor. intro. edestruct HFb; eauto.
  - intro. simpl. edestruct HFb; eauto.
Qed.

(** When using [nchoice], this notation can be used for clarity for
  the set-valued computation *)

Notation "{ a | P }" := (nret (fun a => P)) : ndi_scope.


(** * Eliminating input nondeterminism *)

(** ** Simulation relation *)

(** To get rid of the oracle, we use simulation arguments to show that
  all possible results of a computation with input nondeterminism are
  related to a given outcome. The following relation asserts that this
  is the case. *)

Definition nref {A B} (R : rel A B) (a : A) (nb : ndi B) : Prop :=
  forall i, R a (result nb i).

(** ** Monad operations *)

Lemma nret_nref {A B} (R : rel A B) (a : A) (b : B) :
  R a b -> nref R a (nret b).
Proof.
  firstorder.
Qed.

Lemma nbind_nref {A1 A2 B1 B2} (RA : rel A1 A2) (RB : rel B1 B2) f nf a na :
  (forall a1 a2, RA a1 a2 -> nref RB (f a1) (nf a2)) ->
  nref RA a na ->
  nref RB (f a) (nbind nf na).
Proof.
  intros Hf Ha [i j]. simpl. firstorder.
Qed.

(** ** Nondeterministic input *)

Lemma any_nref {X A B} (R : rel A B) (a : A) (fnb : X -> ndi B) :
  (forall x, nref R a (fnb x)) ->
  nref R a (x <- any X ; fnb x).
Proof.
  intros H [i j]. simpl. firstorder.
Qed.

Lemma rely_nref {A B} (R : rel A B) (P : Prop) (a : A) (nb : ndi B) :
  (P -> nref R a nb) ->
  nref R a (_ <- rely P ; nb).
Proof.
  intros H [HP j]. simpl. firstorder.
Qed.  

(** ** Running computations *)

Lemma guarantee_nref P nP :
  nref impl P nP -> P -> guarantee nP.
Proof.
  firstorder.
Qed.

Lemma nchoice_nref {A B} (R : rel A B) (sa : set A) (nsb : ndi (set B)) :
  nref (set_le R) sa nsb ->
  set_le (nref R) sa (nchoice nsb).
Proof.
  intros H a Ha.
  destruct (choice (fun i bi => result nsb i bi /\ R a bi)) as [Fb HFb].
  {
    firstorder.
  }
  exists (ndc Fb). split.
  - constructor. intro. edestruct HFb; eauto.
  - intro. simpl. edestruct HFb; eauto.
Qed.
