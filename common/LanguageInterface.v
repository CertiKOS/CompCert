Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import CKLR.
Require Import Classical.       (* inj_pair2 *)
Require Import Linking.         (* link *)
Require Import SkelInfo.
Require Import Maps.

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
    valid_skel: skel_info -> skel -> skel -> Prop;
    match_senv: skel_info -> ccworld -> Genv.symtbl -> Genv.symtbl -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;

    match_senv_symbol_address:
      forall w skel_info se1 se2, match_senv skel_info w se1 se2 ->
      forall q1 q2, match_query w q1 q2 ->
      forall i, Genv.symbol_address se1 i Ptrofs.zero = entry q1 <->
           Genv.symbol_address se2 i Ptrofs.zero = entry q2;
    match_query_defined:
      forall w q1 q2,
        match_query w q1 q2 ->
        entry q1 <> Vundef <-> entry q2 <> Vundef;
    match_senv_valid:
        forall sk1 sk2 w se1 se2 skel_info,
          valid_skel skel_info sk1 sk2 ->
          match_senv skel_info w se1 se2 ->
          Genv.valid_for sk1 se1 ->
          Genv.valid_for sk2 se2;
    match_senv_order:
        forall se1 se2 w skel_info skel_info',
          match_senv skel_info w se1 se2 ->
          skel_info_le skel_info' skel_info ->
          match_senv skel_info' w se1 se2;
    valid_skel_link:
        forall skel_info1 skel_info2 sk1l sk1r sk2l sk2r sk1,
          valid_skel skel_info1 sk1l sk2l ->
          valid_skel skel_info2 sk1r sk2r ->
          link sk1l sk1r = Some sk1 ->
          exists skel_info sk2,
            link sk2l sk2r = Some sk2 /\
            valid_skel skel_info sk1 sk2 /\
            skel_info_le skel_info1 skel_info /\
            skel_info_le skel_info2 skel_info;
  }.

Arguments callconv: clear implicits.
Delimit Scope cc_scope with cc.
Bind Scope cc_scope with callconv.
Local Obligation Tactic := cbn; eauto.

(** ** Identity *)

Inductive valid_skel_id: skel_info -> skel -> skel -> Prop :=
| valid_skel_id_intro sk:
    valid_skel_id
      (Atom (fun id => AST.has_symbol sk id) (fun _ => False)) sk sk.

Program Definition cc_id {li}: callconv li li :=
  {|
    ccworld := unit;
    valid_skel := valid_skel_id;
    match_senv w _ se1 se2 := se1 = se2;
    match_query w := eq;
    match_reply w := eq;
  |}.
Next Obligation. intros. subst. reflexivity. Qed.
Next Obligation. intros. subst. reflexivity. Qed.
Next Obligation. intros. inv H. eauto. Qed.
Next Obligation.
  intros. inv H. inv H0. exists (atom_skel_info sk1), sk1.
  intuition eauto. constructor.
  1-2: apply linkorder_skel_info_le; apply link_linkorder in H1 as [? ?]; eauto.
Qed.

Notation "1" := cc_id : cc_scope.

(** ** Composition *)

Inductive valid_skel_compose {li1 li2 li3} (cc12: callconv li1 li2)
  (cc23: callconv li2 li3): skel_info -> skel -> skel -> Prop :=
  | Valid_skel_compose_intro info1 info2 sk1 sk2 sk3:
      valid_skel cc12 info1 sk1 sk2 ->
      valid_skel cc23 info2 sk2 sk3 ->
      valid_skel_compose cc12 cc23 (Compose info1 info2) sk1 sk3.

Inductive match_senv_compose {li1 li2 li3} (cc12: callconv li1 li2)
  (cc23: callconv li2 li3):
    skel_info -> (Genv.symtbl * ccworld cc12 * ccworld cc23) ->
    Genv.symtbl -> Genv.symtbl -> Prop :=
  | Match_senv_compose_intro info1 info2 w12 w23 se1 se2 se3:
      match_senv cc12 info1 w12 se1 se2 ->
      match_senv cc23 info2 w23 se2 se3 ->
      match_senv_compose cc12 cc23 (Compose info1 info2)
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
  intros. rename se2 into se3. rename q2 into q3.
  destruct w as [[se2 w12] w23].
  destruct H0 as (q2 & Hq1 & Hq2).
  inv H. etransitivity; eapply match_senv_symbol_address; eauto.
Qed.

Next Obligation.
  intros. destruct w as [[se2 w12] w23].
  destruct H as (q & Hq & Hq').
  etransitivity; eapply match_query_defined; eauto.
Qed.

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
  eexists (Compose i i'), k'.
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

Program Definition cc_c (R: cklr): callconv li_c li_c :=
  {|
    ccworld := world R;
    valid_skel := valid_skel_id;
    match_senv _skel_info w se1 se2 := match_stbls R w se1 se2;
    match_query := cc_c_query R;
    match_reply := (<> cc_c_reply R)%klr;
  |}.

Lemma symbol_address_match (f: meminj) i vf1 vf2 se1 se2:
  Genv.match_stbls f se1 se2 ->
  Val.inject f vf1 vf2 ->
  vf1 <> Vundef ->
  Genv.symbol_address se1 i Ptrofs.zero = vf1 <->
  Genv.symbol_address se2 i Ptrofs.zero = vf2.
Proof.
  unfold Genv.symbol_address. split.
  - destruct Genv.find_symbol eqn: Hx.
    + edestruct @Genv.find_symbol_match as (b' & fb & Hb); eauto.
      rewrite Hb. intros. subst. inv H0. rewrite fb in H4. inv H4.
      f_equal.
    + intros. exfalso. apply H1. easy.
  - intros. destruct Genv.find_symbol eqn: Hx.
    + subst vf2. inv H0; try congruence.
      unfold Genv.find_symbol in Hx.
      rewrite <- Genv.mge_symb in Hx; eauto.
      exploit Genv.genv_symb_range. apply Hx. intros Hplt.
      unfold Genv.find_symbol. rewrite Hx.
      edestruct Genv.mge_dom as (bx & Hbx); eauto.
      rewrite Hbx in H5. inv H5.
      replace (Ptrofs.repr 0) with Ptrofs.zero in H6 by reflexivity.
      rewrite Ptrofs.add_zero in H6. congruence.
    + subst. inv H0. exfalso. apply H1. auto.
Qed.

Next Obligation.
  intros until i. eapply match_stbls_proj in H. inv H0. cbn.
  eapply symbol_address_match; eauto.
Qed.

Next Obligation.
  intros. inv H. split; eauto.
  intros. cbn. inv H0; easy.
Qed.

Next Obligation.
  intros. eapply match_stbls_proj in H0. inv H.
  erewrite <- Genv.valid_for_match; eauto.
Qed.

Next Obligation.
  intros. inv H. inv H0.
  exists (atom_skel_info sk1), sk1.
  repeat split; eauto.
  1-2: apply linkorder_skel_info_le; apply link_linkorder in H1 as [? ?]; eauto.
Qed.


Record inj_world :=
  injw {
    injw_meminj :> meminj;
    injw_next_l: block;
    injw_next_r: block;
  }.

Variant inj_incr: relation inj_world :=
  inj_incr_intro f f' nb1 nb2 nb1' nb2':
    inject_incr f f' ->
    (forall b1 b2 delta, f b1 = None -> f' b1 = Some (b2, delta) ->
     Pos.le nb1 b1 /\ Pos.le nb2 b2) ->
    Pos.le nb1 nb1' ->
    Pos.le nb2 nb2' ->
    inj_incr (injw f nb1 nb2) (injw f' nb1' nb2').

Record inj_stbls' (w: inj_world) (kept removed: ident -> Prop) (se1 se2: Genv.symtbl): Prop :=
  {
    inj_stbls_match: match_stbls_static kept removed (injw_meminj w) se1 se2;
    inj_stbls_next_l: Pos.le (Genv.genv_next se1) (injw_next_l w);
    inj_stbls_next_r: Pos.le (Genv.genv_next se2) (injw_next_r w);
  }.

Variant inj_mem: klr inj_world mem mem :=
  inj_mem_intro f m1 m2:
    Mem.inject f m1 m2 ->
    inj_mem (injw f (Mem.nextblock m1) (Mem.nextblock m2)) m1 m2.

(* only consider static symbols? *)
Inductive ug_valid_skel: skel_info -> skel -> skel -> Prop :=
  Ug_valid_skel_intro sk1 sk2:
    skel_le sk2 sk1 -> skel_prop sk1 ->
    ug_valid_skel
      (Atom (AST.has_symbol sk2)
         (fun id => ~ AST.has_symbol sk2 id /\ AST.has_symbol sk1 id)) sk1 sk2.

Inductive ug_match_senv: skel_info -> inj_world -> Genv.symtbl -> Genv.symtbl -> Prop :=
  Ug_match_senv_intro w kept removed se1 se2:
    inj_stbls' w kept removed se1 se2 ->
    ug_match_senv (Atom kept removed) w se1 se2.

Inductive ug_match_query (w: inj_world): relation c_query :=
  | ug_match_query_intro vf1 vf2 sg vargs1 vargs2 m1 m2:
      Val.inject (injw_meminj w) vf1 vf2 ->
      Val.inject_list (injw_meminj w) vargs1 vargs2 ->
      inj_mem w m1 m2 ->
      vf1 <> Vundef ->
      ug_match_query w (cq vf1 sg vargs1 m1) (cq vf2 sg vargs2 m2).

Inductive ug_match_reply (w: inj_world): relation c_reply :=
  | ug_match_reply_intro vres1 vres2 m1' m2':
      Val.inject (injw_meminj w) vres1 vres2 ->
      inj_mem w m1' m2' ->
      ug_match_reply w (cr vres1 m1') (cr vres2 m2').

Instance inj_cklr_kf: KripkeFrame unit inj_world.
split. intro. exact inj_incr.
Defined.

Program Definition cc_ug: callconv li_c li_c :=
  {|
    ccworld := inj_world;
    valid_skel := ug_valid_skel;
    match_senv := ug_match_senv;
    match_query := ug_match_query;
    match_reply := (<> ug_match_reply)%klr;
  |}.

Lemma symbol_address_match' (f: meminj) i vf1 vf2 se1 se2:
  match_stbls' f se1 se2 ->
  Val.inject f vf1 vf2 ->
  vf1 <> Vundef ->
  Genv.symbol_address se1 i Ptrofs.zero = vf1 <->
  Genv.symbol_address se2 i Ptrofs.zero = vf2.
Proof.
  unfold Genv.symbol_address. split.
  - destruct Genv.find_symbol eqn: Hx.
    + intros <-. inv H0.
      edestruct mge_symb' with (id:=i) as (Ha & Hb); eauto.
      exploit mge_delta; eauto. eapply Genv.genv_symb_range; eauto.
      intros ->.
      exploit Ha; eauto. intros Hc. setoid_rewrite Hc.
      rewrite Ptrofs.add_zero. reflexivity.
    + intros <-. easy.
  - destruct Genv.find_symbol eqn: Hx.
    + intros <-. inv H0; try congruence.
      edestruct mge_symb' with (id:=i) as (Ha & Hb); eauto.
      setoid_rewrite Hb; eauto.
      specialize (Hb Hx).
      exploit mge_delta; eauto. eapply Genv.genv_symb_range; eauto.
      intros ->. f_equal. rewrite H6.
      replace (Ptrofs.repr 0) with Ptrofs.zero by reflexivity.
      apply Ptrofs.add_zero.
    + intros <-. inv H0. easy.
Qed.

Next Obligation.
  intros. inv H. inv H1. inv H0. cbn.
  eapply symbol_address_match'; eauto. apply inj_stbls_match0.
Qed.

Next Obligation.
  intros. inv H. split; eauto.
  intros. cbn. inv H0; easy.
Qed.

Next Obligation.
  intros. inv H. inv H0. inv H8. destruct inj_stbls_match0.
  intros id g Hg.
  destruct H2 as [Hle1 Hle2 Hle3 Hle4].
  exploit Hle1; eauto. intros Hg1.
  edestruct H1 as (b1 & g' & Hb1 & Hg' & Hgg'); eauto.
  edestruct symbols_kept as (bx & Hbx).
  unfold has_symbol. unfold prog_defs_names.
  apply in_map. apply in_prog_defmap. apply Hg. cbn in *.
  exploit mge_img'; eauto. eapply Genv.genv_symb_range; eauto.
  intros (b1' & Hf).
  exploit mge_symb'; eauto. intros (Hsymb1 & Hsymb2).
  exploit mge_info'; eauto. intros Hinfo.
  exploit Hsymb2. apply Hbx. intros Hb1'.
  setoid_rewrite Hb1 in Hb1'. inv Hb1'.
  exists bx, g'. repeat split; eauto.
  setoid_rewrite <- Hinfo. apply Hg'.
Qed.

Next Obligation.
  intros. inv H. inv H1. inv H0. destruct inj_stbls_match0.
  constructor. split; eauto. split; eauto.
Qed.

Local Opaque PTree_Properties.of_list.

Lemma has_symbol_link1 sk1 sk2 sk id:
  link sk1 sk2 = Some sk ->
  has_symbol sk1 id -> has_symbol sk id.
Proof.
  intros Hlink Hid.
  apply link_prog_inv in Hlink as (? & Hdef & ?). subst sk.
  apply prog_defmap_dom in Hid as (g & Hg).
  apply in_map_iff; cbn.
  destruct ((prog_defmap sk2) ! id) eqn: Hg'.
  - specialize (Hdef _ _ _ Hg Hg') as (? & ? & (g' & Hgg)).
    exists (id, g'). split; eauto.
    apply PTree.elements_correct.
    rewrite PTree.gcombine by reflexivity.
    rewrite Hg. rewrite Hg'. apply Hgg.
  - exists (id, g). split; eauto.
    apply PTree.elements_correct.
    rewrite PTree.gcombine by reflexivity.
    rewrite Hg. rewrite Hg'. reflexivity.
Qed.

Lemma has_symbol_link2 sk1 sk2 sk id:
  link sk1 sk2 = Some sk ->
  has_symbol sk2 id -> has_symbol sk id.
Proof.
  intros Hlink Hid.
  apply link_prog_inv in Hlink as (? & Hdef & ?). subst sk.
  apply prog_defmap_dom in Hid as (g & Hg).
  apply in_map_iff; cbn.
  destruct ((prog_defmap sk1) ! id) eqn: Hg'.
  - specialize (Hdef _ _ _ Hg' Hg) as (? & ? & (g' & Hgg)).
    exists (id, g'). split; eauto.
    apply PTree.elements_correct.
    rewrite PTree.gcombine by reflexivity.
    rewrite Hg. rewrite Hg'. apply Hgg.
  - exists (id, g). split; eauto.
    apply PTree.elements_correct.
    rewrite PTree.gcombine by reflexivity.
    rewrite Hg. rewrite Hg'. reflexivity.
Qed.

Next Obligation.
  intros. inv H. inv H0.
  exploit (link_prog_succeeds sk2l sk2r).
  - apply link_prog_inv in H1 as (Hmain & ?).
    destruct H, H2. congruence.
  - intros * Hl Hr.
    exploit defmap_le. apply H2. eauto. intros Hid1.
    exploit defmap_le. apply H. eauto. intros Hid2.
    apply link_prog_inv in H1 as (? & Hdef & ?).
    specialize (Hdef _ _ _ Hid1 Hid2) as (Hg1 & Hg2 & (g & Hg3)).
    repeat split.
    + rewrite <- (public_same H2); eauto.
    + rewrite <- (public_same H); eauto.
    + rewrite Hg3. easy.
  - intros Hlink.
    eexists _, _. split; eauto.
    split. econstructor. 3: split; constructor.
    + apply link_prog_inv in H1 as (? & Hdef & ?). subst sk1.
      constructor.
      * intros * Hg. rewrite prog_defmap_elements in Hg |- *.
        rewrite PTree.gcombine in Hg |- * by reflexivity.
        destruct ((prog_defmap sk2l) ! id) eqn: Hg1;
          destruct ((prog_defmap sk2r) ! id) eqn: Hg2; cbn in *.
        -- eapply defmap_le in Hg1; eauto.
           eapply defmap_le in Hg2; eauto.
           rewrite Hg1. rewrite Hg2. eauto.
        -- eapply defmap_le in Hg1; eauto. inv Hg.
           destruct ((prog_defmap sk1r) ! id) eqn: Hg3.
           ++ exfalso.
              specialize (Hdef _ _ _ Hg1 Hg3) as (Hpub1 & Hpub2 & ?).
              eapply defmap_public in Hg3; eauto. congruence.
           ++ rewrite Hg1. eauto.
        -- eapply defmap_le in Hg2; eauto. inv Hg.
           destruct ((prog_defmap sk1l) ! id) eqn: Hg3.
           ++ exfalso.
              specialize (Hdef _ _ _ Hg3 Hg2) as (Hpub1 & Hpub2 & ?).
              eapply defmap_public in Hg3; eauto. congruence.
           ++ rewrite Hg2. eauto.
        -- inv Hg.
      * intros * Hg Hpub. rewrite prog_defmap_elements in Hg |- *.
        cbn in *.
        rewrite PTree.gcombine in Hg |- * by reflexivity.
        destruct ((prog_defmap sk1l) ! id) eqn: Hg1;
          destruct ((prog_defmap sk1r) ! id) eqn: Hg2; cbn in *.
        -- specialize (Hdef _ _ _ Hg1 Hg2) as (Hpub1 & Hpub2 & ?).
           eapply defmap_public in Hg1; eauto.
           eapply defmap_public in Hg2; eauto.
           rewrite Hg1. rewrite Hg2. eauto.
        -- inv Hg.
           destruct ((prog_defmap sk2r) ! id) eqn: Hg3.
           ++ exfalso.
              eapply defmap_le in Hg3; eauto. congruence.
           ++ apply in_app_or in Hpub as [Hpub|Hpub].
              ** eapply defmap_public in Hg1; eauto.
                 rewrite Hg1. reflexivity.
              ** exfalso.
                 eapply public_defined in Hpub; eauto.
                 apply prog_defmap_dom in Hpub as (g' & Hg').
                 congruence.
        -- inv Hg.
           destruct ((prog_defmap sk2l) ! id) eqn: Hg3.
           ++ exfalso.
              eapply defmap_le in Hg3; eauto. congruence.
           ++ apply in_app_or in Hpub as [Hpub|Hpub].
              ** exfalso.
                 eapply public_defined in Hpub; eauto.
                 apply prog_defmap_dom in Hpub as (g' & Hg').
                 congruence.
              ** eapply defmap_public in Hg2; eauto.
        -- inv Hg.
      * cbn. destruct H2, H. congruence.
      * cbn. apply H2.
    + exploit link_prog_inv. apply H1. intros (? & ? & ->).
      split; cbn -[has_symbol].
      * intros id Hpub.
        apply in_app_or in Hpub as [Hpub|Hpub]; eauto.
        -- eapply has_symbol_link1; eauto.
           eapply public_defined; eauto.
        -- eapply has_symbol_link2; eauto.
           eapply public_defined; eauto.
      * destruct H3. apply in_or_app.
        left. apply main_public.
    + intros id Hid. eapply has_symbol_link1; eauto.
    + intros id (Hid1 & Hid2). split.
      * intros Hid3.
        apply prog_defmap_dom in Hid2 as (g & Hg).
        apply prog_defmap_dom in Hid3 as (g' & Hg').
        rewrite prog_defmap_elements in Hg'.
        rewrite PTree.gcombine in Hg' by reflexivity.
        destruct ((prog_defmap sk2l) ! id) eqn: Hg1.
        -- apply Hid1. apply in_map_iff.
           exists (id, g0). split; eauto.
           apply in_prog_defmap. eauto.
        -- destruct ((prog_defmap sk2r) ! id) eqn: Hg2.
           ++ eapply defmap_le in Hg2; eauto.
              apply link_prog_inv in H1 as (? & Hdef & ?).
              specialize (Hdef _ _ _ Hg Hg2).
              eapply defmap_public in Hg; eauto. 2: apply Hdef.
              apply Hid1. apply in_map_iff.
              exists (id, g). split; eauto.
              apply in_prog_defmap. eauto.
           ++ inv Hg'.
      * eapply has_symbol_link1; eauto.
    + intros id Hid. eapply has_symbol_link2; eauto.
    + admit.
Admitted.
