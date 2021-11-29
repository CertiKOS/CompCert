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
  We can only observe corresponding [eventval]s using [mpush] and [mpeek].
  The computation eventually yields a result of type [X]. *)

Inductive mlang X : Type :=

  (* terminating computations *)
  | mret : X -> mlang X

  (* accessing the runtime values environment *)
  | mpush : eventval -> mlang X -> mlang X
  | mpeek : nat -> (eventval -> mlang X) -> mlang X
  | mshift : nat -> ptrofs -> mlang X -> mlang X

  (* actual memory operations *)
  | malloc : Z -> mlang X -> mlang X
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
      (mpeek 0
        (fun v => mret v)))).


(** * Evaluating computations *)

(** Memory computations of this form can be evaluated in a combination
  of the state monad and the maybe monad, namely:

      M X := mem * (nat -> val) -> option (mem * (nat -> val) * X)

  This is done informally below but can be made more explicit
  (see the end of this file). *)

(** We use the following helper functions to extend the environment with
  new runtime values and handle the conversion between [val] and the
  external, memory-invariant representation [eventval]. *)

Definition push (v : val) (e : nat -> val) (n : nat) : val :=
  match n with
  | 0 => v
  | S n => e n
  end.

Definition eval2val (se : Genv.symtbl) (v : eventval) : option val :=
  match v with
  | EVint n => Some (Vint n)
  | EVlong n => Some (Vlong n)
  | EVfloat n => Some (Vfloat n)
  | EVsingle n => Some (Vsingle n)
  | EVptr_global i ofs =>
    match Genv.find_symbol se i with
    | Some b => Some (Vptr b ofs)
    | None => None
    end
  end.

Definition val2eval (se : Genv.symtbl) (v : val) : option eventval :=
  match v with
  | Vundef => None
  | Vint n => Some (EVint n)
  | Vlong n => Some (EVlong n)
  | Vfloat n => Some (EVfloat n)
  | Vsingle n => Some (EVsingle n)
  | Vptr b ofs =>
    match Genv.invert_symbol se b with
    | Some i => Some (EVptr_global i ofs)
    | None => None
    end
  end.

(** With that the evaluation function is fairly straightforward. *)

Fixpoint meval {X} se (t : mlang X) (m : mem) (e : nat -> val) : option (mem * (nat->val) * X) :=
  match t with
  | mret x => Some (m, e, x)
  | mpush c t =>
    match eval2val se c with
    | Some v => meval se t m (push v e)
    | None => None
    end
  | mpeek n t =>
    match val2eval se (e n) with
    | Some v => meval se (t v) m e
    | None => None
    end
  | mshift n ofs t =>
    meval se t m (push (Val.offset_ptr (e n) ofs) e)
  | malloc size t =>
    let '(m, b) := Mem.alloc m 0 size in
    meval se t m (push (Vptr b Ptrofs.zero) e)
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

Instance push_rel R:
  Monotonic (@push) (R ++> (- ==> R) ++> (- ==> R)).
Proof.
  unfold push. rauto.
Qed.

Instance eval2val_cklr R:
  Monotonic (@eval2val)
    (|= match_stbls R ++> - ==> k1 option_le (Val.inject @@ [mi R])).
Proof.
  intros w se1 se2 Hse v. unfold eval2val.
  repeat rstep.
  destruct (Genv.find_symbol se1 i) as [b1 | ] eqn:Hb1; try rauto.
  eapply Genv.find_symbol_match in Hb1 as (b2 & Hb & Hb2).
  2: eapply match_stbls_proj; eauto.
  rewrite Hb2.
  repeat rstep.
  eapply block_sameofs_ptrbits_inject; auto.
Qed.

Instance val2eval_cklr R:
  Monotonic (@val2eval)
    (|= match_stbls R ++> Val.inject @@ [mi R] ++> k1 option_le (k eq)).
Proof.
  intros w se1 se2 Hse v1 v2 Hv. unfold val2eval.
  repeat rstep.
  destruct (Genv.invert_symbol se1 b1) as [i | ] eqn:Hb1; try rauto.
  apply Genv.invert_find_symbol in Hb1.
  eapply Genv.find_symbol_match in Hb1 as (b2' & Hb & Hb2).
  2: eapply match_stbls_proj; eauto.
  inversion H; clear H; subst.
  assert (b2' = b2) by congruence; subst.
  assert (delta = 0) by congruence; subst.
  rewrite Ptrofs.add_zero.
  apply Genv.find_invert_symbol in Hb2. rewrite Hb2.
  rauto.
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
    rauto.
  - (* mpeek *)
    repeat rstep. red in H2. subst.
    specialize (H y w rauto).
    rauto.
  - (* mshift *)
    specialize (IHt w Hse).
    rauto.
  - (* malloc *)
    repeat rstep. destruct m, n, H1. destruct H0. cbn in *.
    specialize (IHt x rauto m m0 rauto).
    specialize (IHt (push (Vptr b Ptrofs.zero) e1)).
    specialize (IHt (push (Vptr b0 Ptrofs.zero) e2)).
    specialize (IHt rauto).
    rauto.
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
  deBruijn-style approach where each new name is 0 and shifts the
  existing names, but that is not very user-friendly. Nominal
  approaches could be helpful here; I am not sure how that would
  overlap or not with the nominal memory model itself. It seems this
  problem is related to managing game-semantic pointers and maybe
  nominal game semantics could be a starting point.

  Support for quoting could be important in practical applications:
  given an expression or property involving CompCert memory operations,
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
  | epeek : nat -> msig eventval
  | eshift : nat -> ptrofs -> msig unit
  | ealloc : Z -> msig unit
  | eload : memory_chunk -> nat -> msig unit
  | estore : memory_chunk -> nat -> nat -> msig unit.

Inductive mterm X :=
  | eret : X -> mterm X
  | econs {N} : msig N -> (N -> mterm X) -> mterm X.

(** The fact that the structure is more explicit makes it possible to
  define a monad-style notation for computations. *)

Notation "v <- x ; M" := (econs x (fun v => M))
  (at level 65, x at next level, right associativity).

Notation "x ; M" := (econs x (fun _ => M))
  (at level 65, right associativity).

(** Here is the example from earlier. *)

Definition readglob' i : mterm eventval :=
  epush (EVptr_global i Ptrofs.zero);
  eload Mint32 0;
  v <- epeek 0;
  eret v.

(** Here is a more sophisticated example: add a new head to the linked
  list based at global [i]. *)

Definition pushglob i n : mterm unit :=
  epush (EVptr_global i Ptrofs.zero);
  epush (EVint n);
  eload Mptr 1;
  ealloc (size_chunk Mptr + size_chunk Mint32);
  eshift 0 (Ptrofs.repr (size_chunk Mptr));

  (* at this point the stack is:
        4 |-> &i
        3 |-> n
        2 |-> address of previous head cell
        1 |-> address of new head cell's pointer
        0 |-> address of new head cell's value
   *)
  estore Mint32 0 3;  (* store new value *)
  estore Mptr 1 2;  (* store pointer to previous head *)
  estore Mptr 4 1;  (* update head pointer *)
  eret tt.

(** Here is a computation for retreiving the k'th value *)

Definition peekglob i k : mterm eventval :=
  epush (EVptr_global i Ptrofs.zero);
  eload Mptr 0;
  (fix scan k :=
     eload Mptr 0;
     match k with
       | O =>
         eshift 0 (Ptrofs.repr (size_chunk Mptr));
         eload Mint32 0;
         v <- epeek 0;
         eret v
       | S k =>
         scan k
     end) k.

(** ** Interpretation *)

(** First, I define explicitly the reader/state/maybe monad [mexec]
  which we use to interpret computations. *)

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
      match eval2val se c with
      | Some v => Some (m, push v e, tt)
      | None => None
      end
    | epeek n =>
      match val2eval se (e n) with
      | Some v => Some (m, e, v)
      | None => None
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
