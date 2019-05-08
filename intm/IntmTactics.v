Require Import LogicalRelations.
Require Import Axioms.
Require Import IntmDef.

Module Behavior.
  Import IntmDef.Behavior.

  (** ** Joins distribute over bind *)

  Lemma bind_join {M N A B} (x y : t M N A) (f : A -> t M N B) :
    bind f (join x y) = join (bind f x) (bind f y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma bind_sup {M N A B I} (x : I -> t M N A) (f : A -> t M N B) :
    bind f (sup x) = sup (fun i => bind f (x i)).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma bind_trace_plus {M N A B} (f g : A -> t M N B) s t :
    bind_trace (fun a => f a \/ g a)%beh s t ->
    bind_trace f s t \/ bind_trace g s t.
  Proof.
    induction 1; firstorder.
  Qed.

  Lemma bind_trace_sum {M N A B I} (f : I -> A -> t M N B) s t :
    inhabited I ->
    bind_trace (fun a => sup (fun i => f i a)) s t ->
    exists i, bind_trace (f i) s t.
  Proof.
    intros [i].
    induction 1; try solve [exists i; firstorder].
    - destruct H. eauto.
    - destruct IHbind_trace. eauto.
  Qed.

  Lemma bind_plus {M N A B} (x : t M N A) (f g : A -> t M N B) :
    bind (fun a => join (f a) (g a)) x = join (bind f x) (bind g x).
  Proof.
    apply antisymmetry.
    - intros t (s & Hs & Hst).
      apply bind_trace_plus in Hst as [Hst | Hst]; firstorder.
    - eapply join_lub; repeat rstep; firstorder.
  Qed.

  Lemma bind_sum {M N A B I} (f : I -> A -> t M N B) (x : t M N A) :
    inhabited I ->
    bind (fun a => sup (fun i => f i a)) x = sup (fun i => bind (f i) x).
  Proof.
    intros HI.
    apply antisymmetry.
    - intros t (s & Hs & Hst).
      apply bind_trace_sum in Hst as [i Hst]; firstorder.
    - eapply sup_lub; intro. repeat rstep. firstorder.
  Qed.

  Lemma bind_bot_l {M N A B} (f : A -> t M N B) :
    bot >>= f = bot.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma bind_bot_r {M N A} (x : t M N A) :
    ref (x >>= fun _ => bot) x.
  Proof.
    (* rewrite <- (bind_ret x) at 2. rstep. *)
    intros t (s & Hs & Hst). revert Hs.
    cut (prefix t s); eauto using closed.
    induction Hst; eauto.
    inversion H.
  Qed.

  Lemma top_bind {M N A B} (f : A -> beh M N B) :
    top >>= f = top.
  Proof.
    apply antisymmetry; try firstorder.
    intros t _. exists undef. firstorder.
  Qed.

  Hint Rewrite @bind_join @bind_sup @bind_plus @bind_bot_l @top_bind : monad.
  Hint Rewrite @bind_sum using repeat constructor : monad.

End Behavior.

Ltac mnorm :=
  (rewrite_strat bottomup hints monad);
  try mnorm.

Create HintDb monad discriminated.

Hint Resolve (antisymmetry (A := beh _ _ _)) : monad.

Ltac monad :=
  try mnorm; eauto 100 with monad.

(** This helps levrage functional extensionality to rewrite under [bind]. *)

Global Instance subrel_bind_pointwise_extfun M N A B :
  subrelation
    (@eq ((A -> beh M N B) -> beh M N A -> beh M N B))
    (pointwise_relation A eq ==> eq ==> eq)%signature.
Proof.
  intros bind _ [ ] f g Hfg x _ [ ].
  f_equal; eauto using functional_extensionality.
Qed.
