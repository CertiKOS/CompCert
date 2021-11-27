Require Import Integers.
Require Import Values.
Require Import AST.
Require Import ZArith.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.

Set Implicit Arguments.


(** * Parametric language for the CompCert memory model *)

(** I sketch out a model for "memory computations" in the style of
  algebraic effects. The memory state is implicit and computations
  proceed inward. Runtime values ([val]) cannot be accessed directly
  but instead are stored in an environment indexed by [nat] names.
  The computation eventually yields a result of type [X]. *)

Inductive mlang X : Type :=
  | mret : X -> mlang X
  | mpush : eventval -> mlang X -> mlang X
  | mread : nat -> (eventval -> mlang X) -> mlang X
  | mload : memory_chunk -> nat -> mlang X -> mlang X
  | mstore : memory_chunk -> nat -> nat -> mlang X -> mlang X.

(** For example, the following computation reads an integer from the
  global [i]. First, we use [mpush] to extend the environment with a
  global pointer (we get [0 |-> ptr]). Then we use [mload] to
  access that address in memory; the result will extend the
  environment so that we get [0 |-> n; 1 |-> ptr].
  Finally we read the result from the top of the stack, which yields a
  memory-independent value [v] which we return. *)

Definition readglob i : mlang eventval :=
  (mpush (EVptr_global i Ptrofs.zero)
    (mload Mint32 0
      (mread 0
        (fun v => mret v)))).


(** * Evaluating computations *)

(** Memory computations of this form can be evaluated in a combination
  of the state monad and the maybe monad, namely:

      M X := mem * (nat -> val) -> option (mem * (nat -> val) * X)

  This is done informally below but could be made more explicit.

  We use the following helper function to extend the environment with
  a new runtime value. *)

Definition push (v : val) (e : nat -> val) (n : nat) : val :=
  match n with
    | 0 => v
    | S n => e n
  end.

(** With that the evaluation function is fairly straightforward. *)

Fixpoint meval {X} se (t : mlang X) (m : mem) (e : nat -> val) : option (mem * (nat->val) * X) :=
  match t with
  | mret x => Some (m, e, x)
  | mpush c t =>
    match c with
    | EVint n => meval se t m (push (Vint n) e)
    | EVlong n => meval se t m (push (Vlong n) e)
    | EVfloat n => meval se t m (push (Vfloat n) e)
    | EVsingle n => meval se t m (push (Vsingle n) e)
    | EVptr_global i ofs =>
      match Genv.find_symbol se i with
      | Some b => meval se t m (push (Vptr b ofs) e)
      | None => None
      end
    end
  | mread n t =>
    match e n with
    | Vundef => None
    | Vint n => meval se (t (EVint n)) m e
    | Vlong n => meval se (t (EVlong n)) m e
    | Vfloat n => meval se (t (EVfloat n)) m e
    | Vsingle n => meval se (t (EVsingle n)) m e
    | Vptr b ofs =>
      match Genv.invert_symbol se b with
      | Some i => meval se (t (EVptr_global i ofs)) m e
      | None => None
      end
    end
  | mload chunk addr t =>
    match Mem.loadv chunk m (e addr) with
    | Some v => meval se t m (push v e)
    | None => None
    end
  | mstore chunk addr n t =>
    match Mem.storev chunk m (e addr) (e n) with
    | Some m' => meval se t m' e
    | None => None
    end
  end.


(** * Parametricity *)

(** It is then quite easy to show that the language is parametric with
  respect to CKLRs, in the following sense. *)

Require Import CKLR.

Instance push_rel f:
  Monotonic (@push)
    (Val.inject f ++> (- ==> Val.inject f) ++> - ==> Val.inject f).
Proof.
  unfold push. rauto.
Qed.

Instance meval_cklr R:
  Monotonic
    (@meval)
    (forallr -,
     |= match_stbls R ==> - ==> 
        match_mem R ++> (- ==> Val.inject @@ [mi R])%klr ++>
        k1 option_le (<> match_mem R * (- ==> Val.inject @@ [mi R]) * k eq)).
Proof.
  intros X w se1 se2 Hse t. revert w Hse.
  induction t; intros w Hse m1 m2 Hm e1 e2 He; cbn.
  - (* mret *)
    rauto.
  - (* mpush *)
    specialize (IHt w Hse).
    repeat rstep.
    destruct (Genv.find_symbol se1 i) as [b1 | ] eqn:Hb1; try rauto.
    eapply Genv.find_symbol_match in Hb1 as (b2 & Hb & Hb2).
    2: eapply match_stbls_proj; eauto.
    rewrite Hb2.
    repeat rstep.
    eapply block_sameofs_ptrbits_inject; auto.
  - (* mread *)
    repeat rstep; try (eapply H; eauto).
    destruct (Genv.invert_symbol se1 b1) as [i | ] eqn:Hb1; try rauto.
    apply Genv.invert_find_symbol in Hb1.
    eapply Genv.find_symbol_match in Hb1 as (b2' & Hb & Hb2).
    2: eapply match_stbls_proj; eauto.
    inversion H0; clear H0; subst.
    assert (b2' = b2) by congruence; subst.
    assert (delta = 0) by congruence; subst.
    rewrite Ptrofs.add_zero.
    apply Genv.find_invert_symbol in Hb2. rewrite Hb2.
    eapply H; rauto.
  - (* mload *)
    specialize (IHt w Hse).
    rauto.
  - (* mstore *)
    repeat rstep.
    edestruct H1 as (w' & Hw' & Hm').
    specialize (IHt w' rauto).
    rauto.
Qed.


(** * Possible extensions *)

(** The language above illustrates the basic principle but is
  obviously quite limited. To make it more realistic, we would first
  and formost need to incorporate many more primitive operations.

  Another limitation is the very basic management of the environment
  containing the real-time values. For simplicity, I used a
  deBruijn-style approach where each new name is 0 and shift the
  existing names, but that is not very user-friendly. Nominal
  approaches could be helpful here; I am not sure how that would
  overlap or not with the nominal memory model itself. It seems this
  problem is related to managing game-semantic pointers and maybe
  nominal game semantics could be a starting point.

  Support for quoting could be important in practical applications:
  given an expression of property involving CompCert memory operations,
  can we write a tactic that puts it in the form [meval se t m0 e0]?

  I have not attempted to give an equational theory for [mlang] but
  this could be an interesting approach for reasoning about memory
  effects. We could define an equivalence relation on [mlang], and
  show that equivalent programs evaluate to the equivalent outcomes.
  This could be incorporated into the relational property of [meval].
  For full generality, this should be an inequational theory,
  expressed as a relator, parameterized by a relation over [X].

  Finally, the algebraic structure of the whole thing is mostly
  implicit. Below I try a different presentation in terms of effect
  signatures and algebra. *)


(** * Presentation in terms of algebra *)

(** In the presentation above, we defined the term model directly.
  Below I give an alternative presentation where the effect/monadic
  structure is more explicit.

  The end-result is the same, but with a presentation constructed
  around effect signatures we could connect to interaction trees and
  the kind of strategy models we like, for example. *)

(** ** Signature and terms *)

(** To make the algebraic structure explicit, we can separate the
  definition of [mlang] into and effect signature and the associated
  free monad / term model / strategy model. *)

Variant msig : Type -> Type :=
  | epush : eventval -> msig unit
  | eread : nat -> msig eventval
  | eload : memory_chunk -> nat -> msig unit
  | estore : memory_chunk -> nat -> nat -> msig unit.

Inductive mterm X :=
  | eret : X -> mterm X
  | econs {N} : msig N -> (N -> mterm X) -> mterm X.

(** ** Interpretation *)

(** First, I define explicitly the monad we use to interpret computations. *)

Definition state : Type :=
  mem * (nat -> val).

Definition mexec X :=
  Genv.symtbl * state -> option (state * X).

Definition ret {X} (x : X) : mexec X :=
  fun '(se, s) => Some (s, x).

Definition bind {X Y} (f : X -> mexec Y) : mexec X -> mexec Y :=
  fun a '(se, s) =>
    match a (se, s) with
      | Some (s', x) => f x (se, s')
      | None => None
    end.

(** Then I give a monadic interpretation for each primitive *)

Definition minterp {N} (t : msig N) : mexec N :=
  fun '(se, (m, e)) =>
    match t with
    | epush c =>
      match c with
      | EVint n => Some (m, push (Vint n) e, tt)
      | EVlong n => Some (m, push (Vlong n) e, tt)
      | EVfloat n => Some (m, push (Vfloat n) e, tt)
      | EVsingle n => Some (m, push (Vsingle n) e, tt)
      | EVptr_global i ofs =>
        match Genv.find_symbol se i with
        | Some b => Some (m, push (Vptr b ofs) e, tt)
        | None => None
        end
      end
    | eread n =>
      match e n with
      | Vundef => None
      | Vint n => Some (m, e, EVint n)
      | Vlong n => Some (m, e, EVlong n)
      | Vfloat n => Some (m, e, EVfloat n)
      | Vsingle n => Some (m, e, EVsingle n)
      | Vptr b ofs =>
        match Genv.invert_symbol se b with
        | Some i => Some (m, e, EVptr_global i ofs)
        | None => None
        end
      end
    | eload chunk addr =>
      match Mem.loadv chunk m (e addr) with
      | Some v => Some (m, push v e, tt)
      | None => None
      end
    | estore chunk addr n =>
      match Mem.storev chunk m (e addr) (e n) with
      | Some m' => Some (m', e, tt)
      | None => None
      end
    end.

(** Finally here is how to interpret terms *)

Fixpoint mfold {X} (t : mterm X) : mexec X :=
  match t with
    | eret x => ret x
    | econs N m k => bind (fun n => mfold (k n)) (minterp m)
  end.
