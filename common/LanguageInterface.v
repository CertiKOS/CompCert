Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import CKLR.
Require Import Classical.       (* inj_pair2 *)
Require Import Linking.

Ltac subst_dep :=
  subst;
  lazymatch goal with
    | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
      apply inj_pair2 in H; subst_dep
    | _ =>
      idtac
  end.

(** * Semantic interface of languages *)

Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
    entry: query -> val;
  }.

Arguments entry {_}.

(** ** Basic interfaces *)

(** The null language interface defined below is used as the outgoing
  interface for closed semantics. *)

Definition li_null :=
  {|
    query := Empty_set;
    reply := Empty_set;
    entry q := match q with end;
  |}.

(** The whole-program interface is used as the incoming interface for
  closed semantics and characterizes whole-program execution: the
  query [tt : unit] invokes the [main()] function and the reply of
  type [int] gives the program's exit status. *)

Definition li_wp :=
  {|
    query := unit;
    reply := Integers.int;
    entry q := Vundef;
  |}.

(** * Calling conventions *)

(** ** Definition *)

Inductive skel_info_order: Genv.skel_info -> Genv.skel_info -> Prop :=
  | skel_info_order_compose info1 info2 info1' info2':
        skel_info_order info1 info1' ->
        skel_info_order info2 info2' ->
        skel_info_order (Genv.Compose info1 info2)
                        (Genv.Compose info1' info2').

Record callconv {li1 li2} :=
  mk_callconv {
    ccworld : Type;
    valid_skel (skel_info: Genv.skel_info)
      (sk1 sk2: AST.program unit unit): Prop;
    match_senv (skel_info: Genv.skel_info):
        ccworld -> Genv.symtbl -> Genv.symtbl -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;

    match_senv_valid:
        forall sk1 sk2 w se1 se2 skel_info,
          valid_skel skel_info sk1 sk2 ->
          match_senv skel_info w se1 se2 ->
          Genv.valid_for sk1 se1 ->
          Genv.valid_for sk2 se2;
    match_senv_order:
        forall se1 se2 w skel_info skel_info',
          match_senv skel_info w se1 se2 ->
          skel_info_order skel_info' skel_info ->
          match_senv skel_info' w se1 se2;
    valid_skel_link:
        forall skel_info1 skel_info2 sk1l sk1r sk2l sk2r sk1,
          valid_skel skel_info1 sk1l sk2l ->
          valid_skel skel_info2 sk1r sk2r ->
          link sk1l sk1r = Some sk1 ->
          exists skel_info sk2,
            link sk2l sk2r = Some sk2 /\
            valid_skel skel_info sk1 sk2 /\
            skel_info_order skel_info1 skel_info /\
            skel_info_order skel_info2 skel_info;
  }.

Arguments callconv: clear implicits.
Delimit Scope cc_scope with cc.
Bind Scope cc_scope with callconv.
Local Obligation Tactic := cbn; eauto.

(** ** Identity *)

Inductive valid_skel_id:
    Genv.skel_info -> AST.program unit unit -> AST.program unit unit -> Prop :=
| valid_skel_id_intro sk:
    valid_skel_id (Genv.Skel_info (AST.has_symbol sk) (AST.has_symbol sk)) sk sk.

Program Definition cc_id {li}: callconv li li :=
  {|
    ccworld := unit;
    valid_skel := valid_skel_id;
    match_senv w _ se1 se2 := se1 = se2;
    match_query w := eq;
    match_reply w := eq;
  |}.
Next Obligation.
  intros. inv H. eauto.
Qed.
Next Obligation.
  intros. inv H. inv H0.
  exists (Genv.Skel_info (AST.has_symbol sk1) (AST.has_symbol sk1)), sk1.
  intuition eauto.
  constructor.
  admit.
Admitted.

Notation "1" := cc_id : cc_scope.

(** ** Composition *)

Inductive valid_skel_compose {li1 li2 li3} (cc12: callconv li1 li2)
  (cc23: callconv li2 li3):
    Genv.skel_info -> AST.program unit unit -> AST.program unit unit -> Prop :=
  | Valid_skel_compose_intro info1 info2 sk1 sk2 sk3:
      valid_skel cc12 info1 sk1 sk2 ->
      valid_skel cc23 info2 sk2 sk3 ->
      valid_skel_compose cc12 cc23 (Genv.Compose info1 info2) sk1 sk3.

Inductive match_senv_compose {li1 li2 li3} (cc12: callconv li1 li2)
  (cc23: callconv li2 li3):
    Genv.skel_info -> (Genv.symtbl * ccworld cc12 * ccworld cc23) ->
    Genv.symtbl -> Genv.symtbl -> Prop :=
  | Match_senv_compose_intro info1 info2 w12 w23 se1 se2 se3:
      match_senv cc12 info1 w12 se1 se2 ->
      match_senv cc23 info2 w23 se2 se3 ->
      match_senv_compose cc12 cc23 (Genv.Compose info1 info2)
        (se2, w12, w23) se1 se3.

Program Definition cc_compose {li1 li2 li3} (cc12: callconv li1 li2) (cc23: callconv li2 li3) :=
  {|
    ccworld := Genv.symtbl * ccworld cc12 * ccworld cc23;
    valid_skel := valid_skel_compose cc12 cc23;
    match_senv := match_senv_compose cc12 cc23;
    match_query '(se2, w12, w23) q1 q3 :=
      exists q2,
        match_query cc12 w12 q1 q2 /\
        match_query cc23 w23 q2 q3;
    match_reply '(se2, w12, w23) r1 r3 :=
      exists r2,
        match_reply cc12 w12 r1 r2 /\
        match_reply cc23 w23 r2 r3;
  |}.
Next Obligation.
  intros. inv H. inv H0.
  eapply match_senv_valid; eauto.
  eapply match_senv_valid; eauto.
Qed.

Next Obligation.
  intros. rename se2 into se3.
  destruct w as [[se2 w12] w23].
  inv H. inv H0.
  constructor; eapply match_senv_order; eauto.
Qed.

Next Obligation.
  intros. inv H. inv H0.
  exploit @valid_skel_link. 3: eauto. 1-2: eauto.
  intros (i & k & Hi & Hk & Ho1 & Ho2).
  exploit @valid_skel_link. 3: apply Hi. 1-2: eauto.
  intros (i' & k' & Hi' & Hk' & Ho1' & Ho2').
  eexists (Genv.Compose i i'), k'.
  intuition eauto; econstructor; eauto.
Qed.

Infix "@" := cc_compose (at level 30, right associativity) : cc_scope.

(** * C-like languages *)

(** ** Interface *)

Record c_query :=
  cq {
    cq_vf: val;
    cq_sg: signature;
    cq_args: list val;
    cq_mem: mem;
  }.

Record c_reply :=
  cr {
    cr_retval: val;
    cr_mem: mem;
  }.

Canonical Structure li_c :=
  {|
    query := c_query;
    reply := c_reply;
    entry := cq_vf;
  |}.

(** ** Simulation conventions *)

(** Every CKLR defines as simulation convention for the C language
  interface in the following way. This is used in particular to show
  that key languages (Clight and RTL) self-simulate under any CKLR.
  In [some other place], we show that instances for the [inj] and
  [injp] CKLRs are equivalent to the corresponding simulation
  conventions used to verify the compiler. *)

Inductive cc_c_query R (w: world R): relation c_query :=
  | cc_c_query_intro vf1 vf2 sg vargs1 vargs2 m1 m2:
      Val.inject (mi R w) vf1 vf2 ->
      Val.inject_list (mi R w) vargs1 vargs2 ->
      match_mem R w m1 m2 ->
      vf1 <> Vundef ->
      cc_c_query R w (cq vf1 sg vargs1 m1) (cq vf2 sg vargs2 m2).

Inductive cc_c_reply R (w: world R): relation c_reply :=
  | cc_c_reply_intro vres1 vres2 m1' m2':
      Val.inject (mi R w) vres1 vres2 ->
      match_mem R w m1' m2' ->
      cc_c_reply R w (cr vres1 m1') (cr vres2 m2').

(* TODO: for most passes we use [valid_skel_id], but for Unusedglob, we need
   something more general *)

(* Program Definition cc_c (R: cklr): callconv li_c li_c := *)
(*   {| *)
(*     ccworld := world R; *)
(*     valid_skel := valid_skel_id; *)
(*     match_senv w removed se1 se2 := *)
(*       match_stbls R w se1 se2 /\ Genv.valid_stbls' sk1 sk2 se1 se2; *)
(*     match_query := cc_c_query R; *)
(*     match_reply := (<> cc_c_reply R)%klr; *)
(*   |}. *)
