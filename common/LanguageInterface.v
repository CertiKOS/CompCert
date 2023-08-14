Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import CKLR.

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

Record callconv {li1 li2} :=
  mk_callconv {
    ccworld : Type;
    match_senv: ccworld -> forall se1 se2, Genv.symtbl_path se1 se2 -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;

    (* match_senv_local: *)
    (* forall sk1 sk2 w path se1 se2, *)
    (*   match_senv sk1 sk2 w path se1 se2 -> *)
    (*   Genv.valid_stbls sk1 sk2 se1 se2; *)
  }.

Arguments callconv: clear implicits.
Arguments match_senv {_ _} _ _ {_ _} _.
Delimit Scope cc_scope with cc.
Bind Scope cc_scope with callconv.
Local Obligation Tactic := cbn; eauto.

(** ** Identity *)

(* Inductive match_senv_id sk1 sk2: *)
(*     skel_path sk1 sk2 -> Genv.symtbl -> Genv.symtbl -> Prop := *)
(* | Match_senv_id_intro se (H: sk2 = sk1): *)
(*     match_senv_id sk1 sk2 (Edge (same_skel_le _ _ H)) se se. *)

Program Definition cc_id {li}: callconv li li :=
  {|
    ccworld := unit;
    match_senv w se1 se2 _ := se1 = se2;
    match_query w := eq;
    match_reply w := eq;
  |}.
(* Next Obligation. *)
(*   intros. apply H. *)
(* Qed. *)

Notation "1" := cc_id : cc_scope.

(** ** Composition *)

Inductive match_senv_compose
  {li1 li2 li3} (cc12: callconv li1 li2) (cc23: callconv li2 li3) {se1 se3}:
    Genv.symtbl * ccworld cc12 * ccworld cc23 ->
    Genv.symtbl_path se1 se3 -> Prop :=
| Match_senv_compose_compose w12 w23 se2
    (symtbl_path12: Genv.symtbl_path se1 se2) (symtbl_path23: Genv.symtbl_path se2 se3)
    (SE12: match_senv cc12 w12 symtbl_path12)
    (SE23: match_senv cc23 w23 symtbl_path23):
    match_senv_compose cc12 cc23 (se2, w12, w23)
      (Genv.Compose symtbl_path12 symtbl_path23)
| Match_senv_compose_direct w12 w23 se2
    (symtbl_path12: Genv.symtbl_path se1 se2) (symtbl_path23: Genv.symtbl_path se2 se3)
    (SE12: match_senv cc12 w12 symtbl_path12)
    (SE23: match_senv cc23 w23 symtbl_path23):
    match_senv_compose cc12 cc23 (se2, w12, w23) (Genv.Direct (fun _ _ => True) _ _ I).

Program Definition cc_compose {li1 li2 li3} (cc12: callconv li1 li2) (cc23: callconv li2 li3) :=
  {|
    ccworld := Genv.symtbl * ccworld cc12 * ccworld cc23;
    match_senv w se1 se3 se_path := match_senv_compose cc12 cc23 w se_path;
    match_query '(se2, w12, w23) q1 q3 :=
      exists q2,
        match_query cc12 w12 q1 q2 /\
        match_query cc23 w23 q2 q3;
    match_reply '(se2, w12, w23) r1 r3 :=
      exists r2,
        match_reply cc12 w12 r1 r2 /\
        match_reply cc23 w23 r2 r3;
  |}.
(* Next Obligation. *)
(*   intros. rename sk2 into sk3. rename se2 into se3. *)
(*   destruct w as [[se2 w12] w23]. inv H. *)
(*   apply match_senv_local in SE12. *)
(*   apply match_senv_local in SE23. *)
(*   eapply Genv.valid_stbls_compose; eauto. *)
(* Qed. *)

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

Program Definition cc_c (R: cklr): callconv li_c li_c :=
  {|
    ccworld := world R;
    match_senv w se1 se2 _se_path := match_stbls R w se1 se2;
    match_query := cc_c_query R;
    match_reply := (<> cc_c_reply R)%klr;
  |}.
