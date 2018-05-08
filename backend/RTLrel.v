Require Import Coqlib Mapsrel.
Require Import AST Integers Valuesrel Eventsrel CKLR Globalenvsrel Smallstep.
Require Import Op Registersrel.
Require Export RTL.

Notation regset_inject f := (RegmapRel.r (Val.inject f)).

Global Instance init_regs_inject f:
  Monotonic (@init_regs) (Val.inject_list f ++> - ==> regset_inject f).
Proof.
  intros vl1 vl2 Hvl rl. revert vl1 vl2 Hvl.
  induction rl; simpl; intros.
  - rauto.
  - repeat rstep. eauto.
Qed.

Inductive stackframe_inject f: relation stackframe :=
  Stackframe_inject:
    Monotonic
      (@Stackframe)
      (-==> -==> Val.inject f ++> -==> regset_inject f ++> stackframe_inject f).

Global Existing Instance Stackframe_inject.

Global Instance stackframe_inject_incr:
  Monotonic (@stackframe_inject) (inject_incr ++> subrel).
Proof.
  intros f1 f2 Hf sf1 sf2 Hsf.
  destruct Hsf. rauto.
Qed.

Inductive state_rel R w: relation state :=
  | State_rel:
      Monotonic
        (@State)
        (list_rel (stackframe_inject (mi R w)) ++>
         - ==> Val.inject (mi R w) ++> - ==> regset_inject (mi R w) ++>
         match_mem R w ++> state_rel R w)
  | Callstate_rel:
      Monotonic
        (@Callstate)
        (list_rel (stackframe_inject (mi R w)) ++>
         block_inject (mi R w) ==> Val.inject_list (mi R w) ++>
         match_mem R w ++> state_rel R w)
  | Returnstate_rel:
      Monotonic
        (@Returnstate)
        (list_rel (stackframe_inject (mi R w)) ++>
         Val.inject (mi R w) ++>
         match_mem R w ++> state_rel R w).

Global Existing Instance State_rel.
Global Existing Instance Callstate_rel.
Global Existing Instance Returnstate_rel.

Global Instance eval_addressing32_rel R w:
  Monotonic
    (@eval_addressing32)
    (forallr -, forallr -, psat (genv_valid R w) ==>
     Val.inject (mi R w) ++> - ==>
     Val.inject_list (mi R w) ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold eval_addressing32. rauto.
Qed.

Global Instance eval_addressing64_rel R w:
  Monotonic
    (@eval_addressing64)
    (forallr -, forallr -, psat (genv_valid R w) ==>
     Val.inject (mi R w) ++> - ==>
     Val.inject_list (mi R w) ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold eval_addressing64. rauto.
Qed.

Global Instance eval_addressing_rel R w:
  Monotonic
    (@eval_addressing)
    (forallr -, forallr -, psat (genv_valid R w) ==>
     Val.inject (mi R w) ++> - ==>
     Val.inject_list (mi R w) ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold eval_addressing. rauto.
Qed.

Global Instance eval_condition_rel R w:
  Monotonic
    (@eval_condition)
    (- ==> Val.inject_list (mi R w) ++> match_mem R w ++> option_le eq).
Proof.
  unfold eval_condition.
  repeat rstep; congruence.
Qed.

Global Instance eval_operation_rel R w:
  Monotonic
    (@eval_operation)
    (forallr -, forallr -, psat (genv_valid R w) ==>
     Val.inject (mi R w) ++> - ==>
     Val.inject_list (mi R w) ++> match_mem R w ++>
     option_le (Val.inject (mi R w))).
Proof.
  intros F V ge1 ge2 Hge sp1 sp2 Hsp op vl1 vl2 Hvl m1 m2 Hm.
  unfold eval_operation. destruct op; try rauto.
Qed.

Global Instance map_inject_list {A} R f:
  Monotonic (@map A val) ((R ++> Val.inject f) ++> list_rel R ++> Val.inject_list f).
Proof.
  intros f1 f2 Hf x y Hxy.
  induction Hxy; simpl; constructor; rauto.
Qed.

Global Instance map_inject_list_params:
  Params (@map) 2.


(** The [option] equivalent of [R ++> impl]. *)

Definition option_impl {A B} (R: rel A B) x y :=
  forall a b, R a b -> x = Some a -> y = Some b.

Global Instance option_impl_subrel A B:
  Monotonic (@option_impl A B) (subrel --> subrel).
Proof.
  firstorder.
Qed.

Global Instance option_impl_subrel_params:
  Params (@option_impl) 3.

Global Instance option_impl_bot {A B} (R: rel A B) y:
  Related None y (option_impl R).
Proof.
  discriminate.
Qed.

Global Instance option_impl_transport {A B} (R: rel A B) x y a b:
  Transport (option_impl R * R) (x, a) (y, b) (x = Some a) (y = Some b).
Proof.
  firstorder.
Qed.

Global Instance block_of_inject f:
  Monotonic (@block_of) (Val.inject f ++> option_impl (block_inject_sameofs f)).
Proof.
  unfold block_of. repeat rstep.
  intros a1 a2 Ha H1.
  red in Ha. inv H0.
  destruct Ptrofs.eq_dec; try discriminate. inv H1. rewrite Ha in H3. inv H3.
  rewrite Ptrofs.add_zero. destruct Ptrofs.eq_dec; congruence.
Qed.

Global Instance find_block_inject R w:
  Monotonic
    (@find_block)
    (psat (genv_valid R w) ++> - ==> regset_inject (mi R w) ++>
     option_impl (block_inject_sameofs (mi R w))).
Proof.
  intros ge _ [Hge] ros rs1 rs2 Hrs b1 b2 Hb H.
  unfold find_block in H |- *.
  destruct ros; eauto.
  revert H. eapply block_of_inject; eauto.
  cut (b1 = b2); try congruence.
  eapply genv_valid_find_symbol in H; eauto.
  red in Hb, H. congruence.
Qed.

Global Instance genv_valid_funct_ptr_rexists {F V} R w (ge: Genv.t F V) f b:
  RExists
    (genv_valid R w ge /\ Genv.find_funct_ptr ge b = Some f)
    (block_inject_sameofs (mi R w)) b b.
Proof.
  intros [Hge H].
  eapply genv_valid_funct_ptr; eauto.
Qed.

Global Instance step_rel R:
  Monotonic
    (@step)
    ([] (fun w => psat (genv_valid R w)) ++> state_rel R ++> - ==>
     k1 set_le (<> state_rel R)).
Proof.
  intros w ge ge' Hge s1 s2 Hs t s1' H1.
  pose proof Hge as Hge'. destruct Hge as [Hge].
  deconstruct H1 ltac:(fun x => pose (c := x)); inv Hs.
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
  - transport_hyps. eexists. split; [ eapply c; eauto; fail | ].
    exists w'. split; rauto.
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
  - admit. (* need stack to inject w/ 0 delta *)
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | ].
    exists w'. split; rauto.
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
  - transport_hyps; eexists; split; [ eapply c; eauto | rauto ].
    + specialize (H9 arg). destruct H9; congruence.
  - admit. (* need stack to inject w/ 0 delta *)
  - edestruct cklr_alloc as (w' & Hw' & Halloc); eauto.
    transport e0. clear Halloc.
    assert (Hfb: block_inject_sameofs (mi R w) fb fb) by rauto.
    assert (y0 = fb).
    {
      destruct H6 as [? ?].
      red in Hfb.
      congruence.
    }
    subst.
    eexists; split. eapply c; eauto; fail.
    exists w'; split. rauto.
    repeat rstep.
    clear - H7 Hw'.
    induction H7; constructor; rauto.
  - assert (Hfb: block_inject_sameofs (mi R w) fb fb) by rauto.
    assert (y0 = fb).
    {
      destruct H6 as [? ?].
      red in Hfb.
      congruence.
    }
    subst.
    transport_hyps.
    eexists; split. eapply c; eauto; fail.
    exists w'; split; rauto.
  - inv H3. inv H2.
    transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
Admitted. (* need stack inj w/ 0 delta *)

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @step : typeclass_instances.

Global Instance semantics_rel R:
  Monotonic (@RTL.semantics) (- ==> forward_simulation (cc_c R) (cc_c R)).
Proof.
  intros p.
  set (ms := fun w s1 s2 => klr_diam (state_rel R) w s1 s2 /\
                            genv_valid R w (Genv.globalenv p)).
  eapply forward_simulation_step with ms.
  - reflexivity.
  - intros w [fb1 sg1 vargs1 m1] [fb2 sg vargs2 m2] [Hfb Hsg Hvargs Hm Hw].
    intros s1 Hs1. inv Hs1. simpl in *. subst.
    assert (genv_valid R w (Genv.globalenv p)) by assumption.
    exists (Callstate nil fb2 vargs2 m2). split.
    + econstructor; eauto.
      eapply find_funct_ptr_transport; eauto.
    + split; eauto; rauto.
  - intros w s1 s2 q1 AE1 [(w' & Hw' & Hs) Hge] HAE1.
    destruct HAE1 as [s1 q1 Hq1].
    destruct Hq1. inv Hs.
    eexists w', (cq _ _ y1 _), _. split.
    + econstructor; simpl; eauto.
      clear - H7; induction H7; constructor; eauto.
      eapply inject_incr_trans; eauto. rauto.
    + split.
      * constructor. econstructor.
        rewrite Hw' in Hge.
        eapply find_funct_ptr_transport; eauto.
      * intros r1 [vres2 m2'] s1' (w'' & Hw'' & Hvres & Hm') HAE. inv HAE.
        simpl in *. eexists. split.
        -- constructor.
        -- constructor; eauto.
           exists w''. split; rauto.
  - intros w s1 s2 r1 [(w' & Hw' & Hs) Hge] Hr1. inv Hr1. inv Hs. inv H2.
    eexists (_, _). simpl. split.
    + rauto.
    + constructor.
  - intros w s1 t s1' Hstep1 s2 [(w' & Hw' & Hs) Hge].
    assert (psat (genv_valid R w') (Genv.globalenv p) (Genv.globalenv p))
      by (constructor; revert Hge; rauto).
    simpl in *.
    transport Hstep1.
    eexists. split; eauto. split; eauto. rauto.
Qed.
