(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** RTL function inlining: semantic preservation *)

Require Import Coqlib Wfsimpl Maps Errors Integers.
Require Import AST Linking Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL.
Require Import Inlining Inliningspec.
(*SACC:*)Require Import StackInj.

Definition match_prog (prog tprog: program) :=
  match_program (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(*SACC:*)
Section STACK_WRAPPER.

(*SACC:*)
Variable fn_stack_requirements: ident -> Z.

Section INLINING.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cu f', Genv.find_funct tge v = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu f', Genv.find_funct_ptr tge b = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma sig_function_translated:
  forall cu f f', transf_fundef (funenv_program cu) f = OK f' -> funsig f' = funsig f.
Proof.
  intros. destruct f; Errors.monadInv H.
  exploit transf_function_spec; eauto. intros SP; inv SP. auto.
  auto.
Qed.

(** ** Properties of contexts and relocations *)

Remark sreg_below_diff:
  forall ctx r r', Plt r' ctx.(dreg) -> sreg ctx r <> r'.
Proof.
  intros. zify. unfold sreg; rewrite shiftpos_eq. xomega.
Qed.

Remark context_below_diff:
  forall ctx1 ctx2 r1 r2,
  context_below ctx1 ctx2 -> Ple r1 ctx1.(mreg) -> sreg ctx1 r1 <> sreg ctx2 r2.
Proof.
  intros. red in H. zify. unfold sreg; rewrite ! shiftpos_eq. xomega.
Qed.

Remark context_below_lt:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Plt (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Plt; zify. unfold sreg; rewrite shiftpos_eq.
  xomega.
Qed.

(*
Remark context_below_le:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Ple (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Ple; zify. unfold sreg; rewrite shiftpos_eq.
  xomega.
Qed.
*)

(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> Val.inject F rs#r rs'#(sreg ctx r))
/\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ Val.inject F v rs'#(sreg ctx r)).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; xomega.
Qed.

Lemma agree_val_reg_gen:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_reg_charact F ctx rs' rs#r r.
Proof.
  intros. destruct H as [A B].
  destruct (Plt_Ple_dec (mreg ctx) r).
  left. rewrite B; auto.
  right. auto.
Qed.

Lemma agree_val_regs_gen:
  forall F ctx rs rs' rl,
  agree_regs F ctx rs rs' -> list_forall2 (val_reg_charact F ctx rs') rs##rl rl.
Proof.
  induction rl; intros; constructor; auto. apply agree_val_reg_gen; auto.
Qed.

Lemma agree_val_reg:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> Val.inject F rs#r rs'#(sreg ctx r).
Proof.
  intros. exploit agree_val_reg_gen; eauto. instantiate (1 := r). intros [[A B] | [A B]].
  rewrite B; auto.
  auto.
Qed.

Lemma agree_val_regs:
  forall F ctx rs rs' rl, agree_regs F ctx rs rs' -> Val.inject_list F rs##rl rs'##(sregs ctx rl).
Proof.
  induction rl; intros; simpl. constructor. constructor; auto. apply agree_val_reg; auto.
Qed.

Lemma agree_set_reg:
  forall F ctx rs rs' r v v',
  agree_regs F ctx rs rs' ->
  Val.inject F v v' ->
  Ple r ctx.(mreg) ->
  agree_regs F ctx (rs#r <- v) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gso. auto. xomega.
Qed.

Lemma agree_set_reg_undef:
  forall F ctx rs rs' r v',
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_set_reg_undef':
  forall F ctx rs rs' r,
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) rs'.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. auto. auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_regs_invariant:
  forall F ctx rs rs1 rs2,
  agree_regs F ctx rs rs1 ->
  (forall r, Ple ctx.(dreg) r -> Plt r (ctx.(dreg) + ctx.(mreg)) -> rs2#r = rs1#r) ->
  agree_regs F ctx rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto.
  apply shiftpos_above.
  eapply Plt_le_trans. apply shiftpos_below. xomega.
  apply H1; auto.
Qed.

Lemma agree_regs_incr:
  forall F ctx rs1 rs2 F',
  agree_regs F ctx rs1 rs2 ->
  inject_incr F F' ->
  agree_regs F' ctx rs1 rs2.
Proof.
  intros. destruct H. split; intros. eauto. auto.
Qed.

Remark agree_regs_init:
  forall F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto.
Qed.

Lemma agree_regs_init_regs:
  forall F ctx rl vl vl',
  Val.inject_list F vl vl' ->
  (forall r, In r rl -> Ple r ctx.(mreg)) ->
  agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl)).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto.
Qed.

(** ** Executing sequences of moves *)

Lemma tr_moves_init_regs:
  forall F stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
  forall rdsts rsrcs vl pc1 pc2 rs1,
  tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
  (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
  list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
  exists rs2,
    star (step (*SACC:*)fn_stack_requirements) tge (State stk f sp pc1 rs1 m)
               E0 (State stk f sp pc2 rs2 m)
  /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
  /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
(* rdsts = nil *)
  inv H0. exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
(* rdsts = a :: rdsts *)
  inv H2. inv H0.
  exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. eapply star_right. eauto. eapply exec_Iop; eauto. traceEq.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply sym_not_equal. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp: block) (ofs: Z) : Prop :=
  Mem.perm m' sp ofs Cur Freeable /\
  (forall b delta, F b = Some(sp, delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(*SACC:*)
Lemma loc_private_push_l:
  forall j m m' b o,
    loc_private j m m' b o ->
    loc_private j (Mem.push_new_stage m) m' b o.
Proof.
  red; intros. setoid_rewrite Mem.push_new_stage_perm. auto.
Qed.

(** Likewise, for a range of locations. *)

Definition range_private (F: meminj) (m m': mem) (sp: block) (lo hi: Z) : Prop :=
  forall ofs, lo <= ofs < hi -> loc_private F m m' sp ofs.

Lemma range_private_invariant:
  forall F m m' sp lo hi F1 m1 m1',
  range_private F m m' sp lo hi ->
  (forall b delta ofs,
      F1 b = Some(sp, delta) ->
      Mem.perm m1 b ofs Max Nonempty ->
      lo <= ofs + delta < hi ->
      F b = Some(sp, delta) /\ Mem.perm m b ofs Max Nonempty) ->
  (forall ofs, Mem.perm m' sp ofs Cur Freeable -> Mem.perm m1' sp ofs Cur Freeable) ->
  range_private F1 m1 m1' sp lo hi.
Proof.
  intros; red; intros. exploit H; eauto. intros [A B]. split; auto.
  intros; red; intros. exploit H0; eauto. omega. intros [P Q].
  eelim B; eauto.
Qed.

Lemma range_private_perms:
  forall F m m' sp lo hi,
  range_private F m m' sp lo hi ->
  Mem.range_perm m' sp lo hi Cur Freeable.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

Lemma range_private_alloc_left:
  forall F m m' sp' base hi sz m1 sp F1,
  range_private F m m' sp' base hi ->
  Mem.alloc m 0 sz = (m1, sp) ->
  F1 sp = Some(sp', base) ->
  (forall b, b <> sp -> F1 b = F b) ->
  range_private F1 m1 m' sp' (base + Zmax sz 0) hi.
Proof.
  intros; red; intros.
  exploit (H ofs). generalize (Zmax2 sz 0). omega. intros [A B].
  split; auto. intros; red; intros.
  exploit Mem.perm_alloc_inv; eauto.
  destruct (eq_block b sp); intros.
  subst b. rewrite H1 in H4; inv H4.
  rewrite Zmax_spec in H3. destruct (zlt 0 sz); omega.
  rewrite H2 in H4; auto. eelim B; eauto.
Qed.

Lemma range_private_free_left:
  forall F (*SACC:*)g m m' sp base sz hi b m1,
  range_private F m m' sp (base + Zmax sz 0) hi ->
  Mem.free m b 0 sz = Some m1 ->
  F b = Some(sp, base) ->
  Mem.inject F (*SACC:*)g m m' ->
  range_private F m1 m' sp base hi.
Proof.
  intros; red; intros.
  destruct (zlt ofs (base + Zmax sz 0)) as [z|z].
  red; split.
  replace ofs with ((ofs - base) + base) by omega.
  eapply Mem.perm_inject; eauto.
  eapply Mem.free_range_perm; eauto.
  rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  intros; red; intros. destruct (eq_block b b0).
  subst b0. rewrite H1 in H4; inv H4.
  eelim Mem.perm_free_2; eauto. rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  exploit Mem.mi_no_overlap; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm. eauto.
  instantiate (1 := ofs - base). rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  eapply Mem.perm_free_3; eauto.
  intros [A | A]. congruence. omega.

  exploit (H ofs). omega. intros [A B]. split. auto.
  intros; red; intros. eelim B; eauto. eapply Mem.perm_free_3; eauto.
Qed.

Lemma range_private_extcall:
  forall F F' (*SACC:*)g m1 m2 m1' m2' sp base hi,
  range_private F m1 m1' sp base hi ->
  (forall b ofs p,
     Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  Mem.unchanged_on (loc_out_of_reach F m1) m1' m2' ->
  Mem.inject F (*SACC:*)g m1 m1' ->
  inject_incr F F' ->
  inject_separated F F' m1 m1' ->
  Mem.valid_block m1' sp ->
  range_private F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR SEP VB.
  red; intros. exploit RP; eauto. intros [A B].
  split. eapply Mem.perm_unchanged_on; eauto.
  intros. red in SEP. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ.
  red; intros; eelim B; eauto. eapply PERM; eauto.
  red. destruct (plt b (Mem.nextblock m1)); auto.
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. tauto.
Qed.

(** ** Relating global environments *)

Inductive match_globalenvs (F: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> F b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, F b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Lemma find_function_agree:
  forall ros rs fd F ctx rs' bound,
  find_function ge ros rs = Some fd ->
  agree_regs F ctx rs rs' ->
  match_globalenvs F bound ->
  exists cu fd',
  find_function tge (sros ctx ros) rs' = Some fd' /\ transf_fundef (funenv_program cu) fd = OK fd' /\ linkorder cu prog.
Proof.
  intros. destruct ros as [r | id]; simpl in *.
- (* register *)
  assert (EQ: rs'#(sreg ctx r) = rs#r).
  { exploit Genv.find_funct_inv; eauto. intros [b EQ].
    assert (A: Val.inject F rs#r rs'#(sreg ctx r)). eapply agree_val_reg; eauto.
    rewrite EQ in A; inv A.
    inv H1. rewrite DOMAIN in H5. inv H5. auto.
    apply FUNCTIONS with fd.
    rewrite EQ in H; rewrite Genv.find_funct_find_funct_ptr in H. auto.
  }
  rewrite EQ. eapply functions_translated; eauto.
- (* symbol *)
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  eapply function_ptr_translated; eauto.
Qed.

Lemma find_inlined_function:
  forall fenv id rs fd f,
  fenv_compat prog fenv ->
  find_function ge (inr id) rs = Some fd ->
  fenv!id = Some f ->
  fd = Internal f.
Proof.
  intros.
  apply H in H1. apply Genv.find_def_symbol in H1. destruct H1 as (b & A & B).
  simpl in H0. unfold ge, fundef in H0. rewrite A in H0.
  rewrite <- Genv.find_funct_ptr_iff in B.
  congruence.
Qed. 

(** Translation of builtin arguments. *)

Lemma tr_builtin_arg:
  forall F (*SACC:*)g bound ctx rs rs' sp sp' m m',
  match_globalenvs F bound ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F (*SACC:*)g m m' ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' (sbuiltinarg ctx a) v'
          /\ Val.inject F v v'.
Proof.
  intros until m'; intros MG AG SP MI. induction 1; simpl.
- exists rs'#(sreg ctx x); split. constructor. eapply agree_val_reg; eauto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto.
  instantiate (1 := Vptr sp' (Ptrofs.add ofs (Ptrofs.repr (dstk ctx)))).
  simpl. econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
  intros (v' & A & B). exists v'; split; auto. constructor. simpl. rewrite Ptrofs.add_zero_l; auto.
- econstructor; split. constructor. simpl. econstructor; eauto. rewrite ! Ptrofs.add_zero_l; auto.
- assert (Val.inject F (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs)).
  { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    inv MG. econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B).
  exists v'; eauto with barg.
- econstructor; split. constructor.
  unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  inv MG. econstructor. eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1 & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2 & A2 & B2).
  econstructor; split. eauto with barg. apply Val.longofwords_inject; auto.
Qed.

Lemma tr_builtin_args:
  forall F (*SACC:*)g bound ctx rs rs' sp sp' m m',
  match_globalenvs F bound ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F (*SACC:*)g m m' ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' (map (sbuiltinarg ctx) al) vl'
          /\ Val.inject_list F vl vl'.
Proof.
  induction 5; simpl.
- exists (@nil val); split; constructor.
- exploit tr_builtin_arg; eauto. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D).
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** ** Relating stacks *)

(*SACC:* The intended meaning of the list of nats is to represent the number of source
frames that correspond to a given target frame *)
Inductive match_stacks (F: meminj) (m m': mem):
             (*SACC:*)list nat -> list stackframe -> list stackframe -> block -> Prop :=
  | match_stacks_nil: forall bound1 bound
        (MG: match_globalenvs F bound1)
        (BELOW: Ple bound1 bound),
      match_stacks F m m' nil nil (*SACC:*)nil bound
  | match_stacks_cons: forall res f sp pc rs stk f' sp' rs' stk' bound fenv ctx (*SACC:*)n (*SACC:*)l
        (MS: match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs < f'.(fn_stacksize))
(*SACC:*)(SSZ3: forall ofs, Mem.perm m sp ofs Max Nonempty -> 0 <= ofs < f.(fn_stacksize))
        (RES: Ple res ctx.(mreg))
        (BELOW: Plt sp' bound)
(*SACC:*)(BELOW': Plt sp (Mem.nextblock m)),
      match_stacks F m m'
          (*SACC:*)(S n :: l)
                   (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' :: stk')
                   bound
  | match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx (*SACC:*)n (*SACC:*)l
        (MS: match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs < f'.(fn_stacksize)) (*SACC: makes strict inequality*)
        (RET: ctx.(retinfo) = Some (rpc, res))
        (BELOW: Plt sp' bound),
      match_stacks F m m'
          (*SACC:*)(n :: l)
                   stk
                   (Stackframe res f' (Vptr sp' Ptrofs.zero) rpc rs' :: stk')
                   bound

with match_stacks_inside (F: meminj) (m m': mem):
        (*SACC:*)nat -> (*SACC:*)list nat -> list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx sp' rs' (*SACC:*)l
        (MS: match_stacks F m m' (*SACC:*)l stk stk' sp')
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 0),
      match_stacks_inside F m m' (*SACC:*)0 (*SACC:*)l stk stk' f' ctx sp' rs'
  | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' (*SACC:*)n (*SACC:*)l
        (MS: match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx' sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
        (AG: agree_regs F ctx' rs rs')
        (SP: F sp = Some(sp', ctx'.(dstk)))
        (PAD: range_private F m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_below ctx' ctx)
        (SBELOW: context_stack_call ctx' ctx)
(*SACC:*)(SSZ3: forall ofs, Mem.perm m sp ofs Max Nonempty -> 0 <= ofs < f.(fn_stacksize))
(*SACC:*)(BELOW': Plt sp (Mem.nextblock m)),
      match_stacks_inside F m m' (*SACC:*)(S n) (*SACC:*)l (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
                                 stk' f' ctx sp' rs'.

(** Properties of match_stacks *)

Section MATCH_STACKS.

Variable F: meminj.
Variables m m': mem.

Lemma match_stacks_globalenvs:
  forall stk stk' bound (*SACC:*)l,
  match_stacks F m m' (*SACC:*)l stk stk' bound -> exists b, match_globalenvs F b
with match_stacks_inside_globalenvs:
  forall stk stk' (*SACC:*)n (*SACC:*)l f ctx sp rs',
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f ctx sp rs' -> exists b, match_globalenvs F b.
Proof.
  induction 1; eauto.
  induction 1; eauto.
Qed.

Lemma match_globalenvs_preserves_globals:
  forall b, match_globalenvs F b -> meminj_preserves_globals ge F.
Proof.
  intros. inv H. red. split. eauto. split. eauto.
  intros. symmetry. eapply IMAGE; eauto.
Qed.

Lemma match_stacks_inside_globals:
  forall (*SACC:*)n (*SACC:*)l stk stk' f ctx sp rs',
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f ctx sp rs' -> meminj_preserves_globals ge F.
Proof.
  intros. exploit match_stacks_inside_globalenvs; eauto. intros [b A].
  eapply match_globalenvs_preserves_globals; eauto.
Qed.

Lemma match_stacks_bound:
  forall (*SACC:*)l stk stk' bound bound1,
  match_stacks F m m' (*SACC:*)l stk stk' bound ->
  Ple bound bound1 ->
  match_stacks F m m' (*SACC:*)l stk stk' bound1.
Proof.
  intros. inv H.
  apply match_stacks_nil with bound0. auto. eapply Ple_trans; eauto.
  eapply match_stacks_cons; eauto. eapply Plt_le_trans; eauto.
  eapply match_stacks_untailcall; eauto. eapply Plt_le_trans; eauto.
Qed.

Variable F1: meminj.
Variables m1 m1': mem.
Hypothesis INCR: inject_incr F F1.

Lemma match_stacks_invariant:
  forall (*SACC:*)l stk stk' bound, match_stacks F m m' (*SACC:*)l  stk stk' bound ->
  forall (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> Plt b2 bound -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Plt b2 bound ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Plt b bound ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Plt b bound ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p)
(*SACCC:*)(NB1: Ple (Mem.nextblock m) (Mem.nextblock m1)),
  match_stacks F1 m1 m1' (*SACC:*)l stk stk' bound

with match_stacks_inside_invariant:
  forall (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs1,
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs1 ->
  forall rs2
         (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
         (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> Ple b2 sp' -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Ple b2 sp' ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Ple b sp' ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Ple b sp' ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p)
(*SACC:*)(NB1: Ple (Mem.nextblock m) (Mem.nextblock m1)),
  match_stacks_inside F1 m1 m1' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs2.

Proof.
  induction 1; intros.
  (* nil *)
  apply match_stacks_nil with (bound1 := bound1).
  inv MG. constructor; auto.
  intros. apply IMAGE with delta. eapply INJ; eauto. eapply Plt_le_trans; eauto.
  auto. auto.
  (* cons *)
  apply match_stacks_cons with (fenv := fenv) (ctx := ctx); auto.
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; xomega.
  intros; eapply PERM1; eauto; xomega.
  intros; eapply PERM2; eauto; xomega.
  intros; eapply PERM3; eauto; xomega.
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto.
  intros; eapply SSZ3; eauto.
  xomega.
  (* untailcall *)
  apply match_stacks_untailcall with (ctx := ctx); auto.
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; xomega.
  intros; eapply PERM1; eauto; xomega.
  intros; eapply PERM2; eauto; xomega.
  intros; eapply PERM3; eauto; xomega.
  eapply range_private_invariant; eauto.

  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros; eapply INJ; eauto; xomega.
  intros; eapply PERM1; eauto; xomega.
  intros; eapply PERM2; eauto; xomega.
  intros; eapply PERM3; eauto; xomega.
  (* inlined *)
  apply match_stacks_inside_inlined with (fenv := fenv) (ctx' := ctx'); auto.
  apply IHmatch_stacks_inside; auto.
  intros. apply RS. red in BELOW. xomega.
  apply agree_regs_incr with F; auto.
  apply agree_regs_invariant with rs'; auto.
  intros. apply RS. red in BELOW. xomega.
  eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto. xomega. eapply PERM1; eauto. xomega.
    intros. eapply PERM2; eauto. xomega.
  intros; eapply SSZ3; eauto. eapply PERM1; eauto. xomega.
  xomega.
Qed.

Lemma match_stacks_empty:
  forall (*SACC:*)l stk stk' bound,
  match_stacks F m m' l stk stk' bound -> stk = nil -> stk' = nil
with match_stacks_inside_empty:
  forall (*SACC:*)n (*SACC:*)l stk stk' f ctx sp rs,
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f ctx sp rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
Proof.
  induction 1; intros.
  auto.
  discriminate.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
  induction 1; intros.
  split. eapply match_stacks_empty; eauto. auto.
  discriminate.
Qed.

End MATCH_STACKS.

(** Preservation by assignment to a register *)

Lemma match_stacks_inside_set_reg:
  forall F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' r v,
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto.
  intros. apply Regmap.gso. zify. unfold sreg; rewrite shiftpos_eq. xomega.
  apply Ple_refl.
Qed.

Lemma match_stacks_inside_set_res:
  forall F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' res v,
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' (regmap_setres (sbuiltinres ctx res) v rs').
Proof.
  intros. destruct res; simpl; auto.
  apply match_stacks_inside_set_reg; auto.
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1',
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' ->
  Mem.store chunk m b ofs v = Some m1 ->
  Mem.store chunk' m' b' ofs' v' = Some m1' ->
  match_stacks_inside F m1 m1' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs'.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto with mem.
  rewrite (Mem.nextblock_store _ _ _ _ _ _ H0); apply Ple_refl.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs',
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' ->
  forall sz m1 b F1 delta,
  Mem.alloc m 0 sz = (m1, b) ->
  inject_incr F F1 ->
  F1 b = Some(sp', delta) ->
  (forall b1, b1 <> b -> F1 b1 = F b1) ->
  delta >= ctx.(dstk) ->
  match_stacks_inside F1 m1 m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H4; inv H4. eelim Plt_strict; eauto.
  rewrite H2 in H4; auto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b1 b); intros; auto.
  subst b1. rewrite H1 in H4. inv H4. eelim Plt_strict; eauto.
  rewrite (Mem.nextblock_alloc _ _ _ _ _ H); xomega.
  (* inlined *)
  eapply match_stacks_inside_inlined; eauto.
  eapply IHmatch_stacks_inside; eauto. destruct SBELOW. omega.
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b0 b); intros.
  subst b0. rewrite H2 in H5; inv H5. elimtype False; xomega.
  rewrite H3 in H5; auto.
  intros.
  eapply SSZ3; eauto. eapply Mem.perm_alloc_inv in H5; eauto.
  destr_in H5.
  subst.
  eapply Mem.fresh_block_alloc in BELOW'. easy. eauto.
  erewrite Mem.nextblock_alloc; eauto. xomega.
Qed.

(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' (*SACC:*)l stk stk' sp b lo hi m1,
  match_stacks F m m' (*SACC:*)l stk stk' sp ->
  Mem.free m b lo hi = Some m1 ->
  match_stacks F m1 m' (*SACC:*)l stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto.
  rewrite (Mem.nextblock_free _ _ _ _ _ H0); xomega.
Qed.

Lemma match_stacks_free_right:
  forall F m m' (*SACC:*)l stk stk' sp lo hi m1',
  match_stacks F m m' (*SACC:*)l stk stk' sp ->
  Mem.free m' sp lo hi = Some m1' ->
  match_stacks F m m1' (*SACC:*)l stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_1; eauto.
  intros. eapply Mem.perm_free_3; eauto.
  xomega.
Qed.

(*SACC:* Preservation by record_stack_blocks*)

(*SACC:*)
Lemma match_stacks_inside_record_left:
  forall F m m' n l stk stk' f' ctx sp' rs',
  match_stacks_inside F m m' n l stk stk' f' ctx sp' rs' ->
  forall f m1,
    Mem.record_stack_blocks m f = Some m1 ->
    match_stacks_inside F m1 m' n l stk stk' f' ctx sp' rs'.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto.
  intros. eapply Mem.record_stack_block_perm; eauto.
  apply Mem.record_stack_block_nextblock in H0. rewrite H0; xomega.
Qed.

(*SACC:* Preservation by push*)

(*SACC:*)
Lemma match_stacks_push_l:
  forall f m m' l s s' nb,
    match_stacks f m m' l s s' nb ->
    match_stacks f (Mem.push_new_stage m) m' l s s' nb.
Proof.
  intros.
  eapply match_stacks_invariant; eauto.
  rewrite Mem.push_new_stage_nextblock; auto. xomega.
Qed.

(*SACC:*)
Lemma match_stacks_push_r:
  forall f m m' l s s' nb,
    match_stacks f m m' l s s' nb ->
    match_stacks f m (Mem.push_new_stage m') l s s' nb.
Proof.
  intros.
  eapply match_stacks_invariant; eauto.
  xomega.
Qed.

(*SACC:*)
Lemma match_stacks_push:
  forall f m m' l s s' nb,
    match_stacks f m m' l s s' nb ->
    match_stacks f (Mem.push_new_stage m) (Mem.push_new_stage m') l s s' nb.
Proof.
  intros.
  eapply match_stacks_push_l; eauto.
  eapply match_stacks_push_r; eauto.
Qed.

(*SACC:*)
Lemma match_stacks_inside_push_l:
  forall j m m' n l s s' f ctx nb rs,
    match_stacks_inside j m m' n l s s' f ctx nb rs ->
    match_stacks_inside j (Mem.push_new_stage m) m' n l s s' f ctx nb rs.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto.
  rewrite Mem.push_new_stage_nextblock; auto. xomega.
Qed.

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H.
  assert (2 <= sz -> (2 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). auto.
    destruct (zle sz 4). apply Zdivides_trans with 4; auto. exists 2; auto.
    apply Zdivides_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). omegaContradiction.
    destruct (zle sz 4). auto.
    apply Zdivides_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). omegaContradiction.
    destruct (zle sz 4). omegaContradiction.
    auto.
  destruct chunk; simpl in *; auto.
  apply Zone_divide.
  apply Zone_divide.
  apply H2; omega.
  apply H2; omega.
Qed.

(** Preservation by external calls *)

Section EXTCALL.

Variables F1 F2: meminj.
(*SACC:*)Variable g: frameinj.
Variables m1 m2 m1' m2': mem.
Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
Hypothesis UNCHANGED: Mem.unchanged_on (loc_out_of_reach F1 m1) m1' m2'.
Hypothesis INJ: Mem.inject F1 (*SACC:*)g m1 m1'.
Hypothesis INCR: inject_incr F1 F2.
Hypothesis SEP: inject_separated F1 F2 m1 m1'.
(*SACC:*)
Hypothesis NB_LE: Ple (Mem.nextblock m1) (Mem.nextblock m2).

Lemma match_stacks_extcall:
  forall (*SACC:*)l stk stk' bound,
  match_stacks F1 m1 m1' (*SACC:*)l stk stk' bound ->
  Ple bound (Mem.nextblock m1') ->
  match_stacks F2 m2 m2' (*SACC:*)l stk stk' bound
with match_stacks_inside_extcall:
  forall (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs',
  match_stacks_inside F1 m1 m1' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' ->
  Plt sp' (Mem.nextblock m1') ->
  match_stacks_inside F2 m2 m2' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  apply match_stacks_nil with bound1; auto.
    inv MG. constructor; intros; eauto.
    destruct (F1 b1) as [[b2' delta']|] eqn:?.
    exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. eapply IMAGE; eauto.
    exploit SEP; eauto. intros [A B]. elim B. red. xomega.
  eapply match_stacks_cons; eauto.
    eapply match_stacks_inside_extcall; eauto. xomega.
    eapply agree_regs_incr; eauto.
    eapply range_private_extcall; eauto. red; xomega.
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega. xomega.
  eapply match_stacks_untailcall; eauto.
    eapply match_stacks_inside_extcall; eauto. xomega.
    eapply range_private_extcall; eauto. red; xomega.
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
  induction 1; intros.
  eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extcall; eauto. xomega.
  eapply match_stacks_inside_inlined; eauto.
    eapply agree_regs_incr; eauto.
    eapply range_private_extcall; eauto.
    xomega.
Qed.

End EXTCALL.

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq.
  apply Zdiv_unique with (b := amount - 1). omega. omega.
Qed.

Lemma match_stacks_inside_inlined_tailcall:
  forall fenv F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' ctx' f,
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx sp' rs' ->
  context_below ctx ctx' ->
  context_stack_tailcall ctx f ctx' ->
  ctx'.(retinfo) = ctx.(retinfo) ->
  range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize) ->
  tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code) ->
  match_stacks_inside F m m' (*SACC:*)n (*SACC:*)l stk stk' f' ctx' sp' rs'.
Proof.
  intros. inv H.
  (* base *)
  eapply match_stacks_inside_base; eauto. congruence.
  rewrite H1. rewrite DSTK. apply align_unchanged. apply min_alignment_pos. apply Zdivide_0.
  (* inlined *)
  assert (dstk ctx <= dstk ctx'). rewrite H1. apply align_le. apply min_alignment_pos.
  eapply match_stacks_inside_inlined; eauto.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply H3. inv H4. xomega.
  congruence.
  unfold context_below in *. xomega.
  unfold context_stack_call in *. omega.
Qed.

(** ** Relating states *)

(*SACC:*)
Definition stack_injects j m :=
  forall b : block, 
    in_stack (Mem.stack m) b -> 
    exists (b' : block) (delta : Z), 
  j b = Some (b', delta).

(*SACC: inline_sizes is an SACC predicate*)
Section INLINE_SIZES.

  Inductive inline_sizes : frameinj -> stack -> stack -> Prop :=
  | inline_sizes_nil: inline_sizes nil nil nil
  | inline_sizes_cons g s1 s2 t1 n t2:
      inline_sizes g (drop (S n) s1) s2 ->
      nth_error s1 n = Some t1 ->
      size_frames t2 <= size_frames t1 ->
      inline_sizes (S n::g) s1 (t2 :: s2).

  Lemma inline_sizes_up:
    forall g s1 s2,
      inline_sizes g s1 s2 ->
      inline_sizes (1%nat :: g) ((None,nil)::s1) ((None,nil)::s2).
  Proof.
    intros. econstructor; simpl; eauto. omega.
  Qed.

  Lemma inline_sizes_upstar:
    forall n g s1 s2 l,
      inline_sizes (n :: g) s1 s2 ->
      inline_sizes (S n :: g) ((None,l) :: s1) s2.
  Proof.
    intros n g s1 s2 l SZ.
    inv SZ.
    econstructor; simpl; eauto.
  Qed.

  Lemma inline_sizes_upright:
    forall g n f1 s1 s2,
      inline_sizes (S (S n) :: g) (f1::s1) s2 ->
      inline_sizes (1%nat :: S n :: g) ((None, opt_cons (fst f1) (snd f1)) :: s1)  ((None,nil)::s2).
  Proof.
    intros g n f1 s1 s2 IS. inv IS.
    simpl in *. repeat destr_in H2. 
    simpl in *.
    repeat econstructor; eauto.
    change (size_frames (None,nil)) with 0. apply size_frames_pos.
  Qed.

  Lemma inline_sizes_record:
    forall g tf1 r1 tf2 r2 fr1 fr2 
      (SZ: inline_sizes (1%nat::g) (tf1 :: r1) (tf2 :: r2))
      (EQ: opt_size_frame fr1 = opt_size_frame fr2),
      inline_sizes (1%nat::g) ((fr1, opt_cons (fst tf1) (snd tf1)) :: r1) ((fr2 , opt_cons (fst tf2) (snd tf2)) :: r2).
  Proof.
    intros. inv SZ.
    simpl in *. inv H5.
    econstructor; simpl; eauto.
    rewrite ! size_frames_cons. simpl. unfold size_frame. rewrite EQ. apply Z.max_le_compat_l; auto.
    fold size_frame. unfold size_frames in H6.
    rewrite ! map_opt_cons.
    rewrite <- ! max_opt_size_frame_tailcall. auto.
  Qed.

  Lemma inline_sizes_record':
    forall g tf1 r1 tf2 r2 fr1 fr2 
      (SZ: inline_sizes (1%nat::g) ((None, tf1) :: r1) ((None,tf2) :: r2))
      (EQ: opt_size_frame fr1 = opt_size_frame fr2),
      inline_sizes (1%nat::g) ((fr1, tf1) :: r1) ((fr2 , tf2) :: r2).
  Proof.
    intros. inv SZ.
    simpl in *. inv H5.
    econstructor; simpl; eauto.
    rewrite ! size_frames_cons. rewrite EQ. apply Z.max_le_compat_l; auto.
    unfold size_frames in H6.
    revert H6.
    rewrite ! max_opt_size_frame_tailcall. simpl. auto.
  Qed.

  
  Lemma inline_sizes_record_left:
    forall g f1 r1 s2 fr1
      (SIZES: inline_sizes g ((None, f1) :: r1) s2),
      inline_sizes g ((fr1,  f1) :: r1) s2.
  Proof.
    intros. inv SIZES.
    destruct n; simpl in *. inv H0.
    econstructor; simpl; auto. etransitivity. apply H1.
    rewrite <- size_frames_tc. rewrite ! size_frames_cons. simpl.
    apply Z.max_le_compat. apply opt_size_frame_pos. omega.
    econstructor; simpl; eauto.
  Qed.

  Lemma inline_sizes_down:
    forall g s1 s2,
      inline_sizes (1%nat::g) s1 s2 ->
      inline_sizes g (tl s1) (tl s2).
  Proof.
    intros. inv H. simpl in *; auto.
  Qed.

  Lemma inline_sizes_downstar:
    forall g n s1 s2,
      inline_sizes (S (S n) :: g) s1 s2 ->
      inline_sizes (S n :: g) (tl s1) s2.
  Proof.
    intros. inv H. simpl in *. repeat destr_in H3.
    econstructor; simpl; eauto.
  Qed.

  Lemma nth_error_take:
    forall {A} n n' (s s': list A) t,
      lt n n' ->
      take n' s = Some s' ->
      nth_error s n = Some t ->
      nth_error s' n = Some t.
  Proof.
    induction n; simpl; intros; eauto.
    repeat destr_in H1.
    destruct n'; simpl in *. omega. repeat destr_in H0. auto.
    destruct n'. omega. simpl in *. repeat destr_in H0.
    eapply IHn. 2: eauto. omega. auto.
  Qed.

  Lemma inline_sizes_size_stack:
    forall g s1 s2
      (SIZES: inline_sizes g s1 s2),
      size_stack s2 <= size_stack s1.
  Proof.
    induction 1; simpl; intros; eauto. omega.
    destruct (take_succeeds (S n) s1) as (t & TAKE).
    eapply nth_error_Some; eauto. congruence.
    rewrite (take_drop _ _ _ TAKE).
    rewrite size_stack_app.
    cut (size_frames t2 <= size_stack t). intros; omega.
    etransitivity. apply H0.
    eapply size_frames_le_size_stack; eauto.
    eapply nth_error_take in H; eauto.
    eapply nth_error_In; eauto.
  Qed.
  
  Lemma inline_sizes_le:
    forall g s1 s2,
      inline_sizes (1%nat::g) s1 s2 ->
      size_stack (tl s2) <= size_stack (tl s1).
  Proof.
    intros g s1 s2 SZ.
    eapply inline_sizes_size_stack.
    apply inline_sizes_down. eauto.
  Qed.

End INLINE_SIZES.

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' f' sp' rs' m' F (*SACC:*)g fenv ctx (*SACC:*)n (*SACC:*)l
        (MS: match_stacks_inside F m m' (*SACC:*)n (*SACC:*)g stk stk' f' ctx sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (MINJ: Mem.inject F ((*SACC:*)S n :: g ++ l) m m')
(*SACC:*)(SI: stack_injects F m)
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs < f'.(fn_stacksize)) (*SACC: strict inequality*)
(*SACC:*)(SSZ3: forall ofs, Mem.perm m sp ofs Max Nonempty -> 0 <= ofs < f.(fn_stacksize))
(*SACC:*)(SIZES: inline_sizes (S n :: g ++ l) (Mem.stack m) (Mem.stack m')),
      match_states (State stk f (Vptr sp Ptrofs.zero) pc rs m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' m')
  | match_call_states: forall stk fd args m stk' fd' args' m' cunit F (*SACC:*)g (*SACC:*)l (*SACC:*)sz
        (MS: match_stacks F m m' (*SACC:*)g stk stk' (Mem.nextblock m'))
        (LINK: linkorder cunit prog)
        (FD: transf_fundef (funenv_program cunit) fd = OK fd')
        (VINJ: Val.inject_list F args args')
        (MINJ: Mem.inject F ((*SACC:*)1%nat :: g ++ l) m m')
(*SACC:*)(SI: stack_injects F m)
(*SACC:*)(SIZES: inline_sizes (1%nat :: g ++ l) (Mem.stack m) (Mem.stack m')),
      match_states (Callstate stk fd args m (*SACC:*)sz)
                   (Callstate stk' fd' args' m' (*SACC:*)sz)
  | match_call_regular_states: forall stk f vargs m stk' f' sp' rs' m' F (*SACC:*)g fenv ctx ctx' pc' pc1' rargs (*SACC:*)n (*SACC:*)l (*SACC:*)sz
        (MS: match_stacks_inside F m m' (*SACC:*)n (*SACC:*)g stk stk' f' ctx sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (BELOW: context_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs)
        (MINJ: Mem.inject F (*SACC:*)(S n :: g ++ l) m m')
(*SACC:*)(SI: stack_injects F m)
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs < f'.(fn_stacksize)) (*SACC: strict inequality*)
(*SACC:*)(SIZES: inline_sizes (S n :: g ++ l) (Mem.stack m) (Mem.stack m')),
      match_states (Callstate stk (Internal f) vargs m (*SACC:*)sz)
                   (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m')
  | match_return_states: forall stk v m stk' v' m' F (*SACC:*)g (*SACC:*)l
        (MS: match_stacks F m m' (*SACC:*)g stk stk' (Mem.nextblock m'))
        (VINJ: Val.inject F v v')
        (MINJ: Mem.inject F ((*SACC:*)1%nat :: g ++ l) m m')
(*SACC:*)(SI: stack_injects F m)
(*SACC:*)(SIZES: inline_sizes (1%nat :: g ++ l) (Mem.stack m) (Mem.stack m')),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v' m')
  | match_return_regular_states: forall stk v m stk' f' sp' rs' m' F (*SACC:*)g ctx pc' or rinfo (*SACC:*)n (*SACC:*)l
        (MS: match_stacks_inside F m m' (*SACC:*)n (*SACC:*)g stk stk' f' ctx sp' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => Val.inject F v rs'#(sreg ctx r) end)
        (MINJ: Mem.inject F ((*SACC:*)S n :: g ++ l) m m')
(*SACC:*)(SI: stack_injects F m)
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
(*SACC:*)(SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs < f'.(fn_stacksize))
(*SACC:*)(SIZES: inline_sizes (S n :: g ++ l) (Mem.stack m) (Mem.stack m')),
      match_states (Returnstate stk v m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m').

(** ** Forward simulation *)

Definition measure (S: RTL.state) : nat :=
  match S with
  | State _ _ _ _ _ _ => 1%nat
  | Callstate _ _ _ _ _ => 0%nat
  | Returnstate _ _ _ => 0%nat
  end.

Lemma tr_funbody_inv:
  forall fenv sz cts f c pc i,
  tr_funbody fenv sz cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv sz cts pc i c.
Proof.
  intros. inv H. eauto.
Qed.

(*SACC:*)
Lemma ros_is_function_transf:
  forall ros rs rs' id F ctx bound,
    match_globalenvs F bound ->
    ros_is_function ge ros rs id ->
    agree_regs F ctx rs rs' ->
    ros_is_function tge (sros ctx ros) rs' id.
Proof.
  unfold ros_is_function. intros.
  destr_in H0. simpl.
  destruct H0 as (b & o & RS & FS).
  generalize (proj1 H1 r) (proj2 H1 r). intros.
  destruct (plt (mreg ctx) r). rewrite H2 in RS; congruence.
  trim H0. xomega.
  rewrite RS in H0. inv H0. do 2 eexists; split; eauto.
  rewrite symbols_preserved. rewrite FS.
  f_equal.
  destruct H. apply SYMBOLS in FS. rewrite DOMAIN in H6; auto. congruence.
Qed.

(*SACC:*)
Lemma in_stack'_norepet:
  forall m b bi1 bi2,
    in_stack' (Mem.stack m) (b, bi1) ->
    in_stack' (Mem.stack m) (b, bi2) ->
    bi1 = bi2.
Proof.
  intros.
  rewrite in_stack'_rew in H, H0.
  destruct H as (tf1 & IFR1 & ITF1).
  destruct H0 as (tf2 & IFR2 & ITF2).
  rewrite in_frames'_rew in IFR1, IFR2.
  destruct IFR1 as (fr1 & IF1 & IFR1).
  destruct IFR2 as (fr2 & IF2 & IFR2).
  assert (tf1 = tf2).
  {
    exploit nodup_nodup'. apply Mem.stack_norepet. apply ITF1. apply ITF2.
    eapply in_frame_in_frames; eauto. eapply in_frame'_in_frame; eauto.
    eapply in_frame_in_frames; eauto. eapply in_frame'_in_frame; eauto. auto.
  }
  subst.
  assert (fr1 = fr2). congruence. subst.
  eapply in_frame'_norepet; eauto.
Qed.

(*SACC:*)
Lemma inline_sizes_same_top:
  forall g f1 f2 s1 s2,
    inline_sizes g (f1::s1) s2 ->
    size_frames f1 = size_frames f2 ->
    inline_sizes g (f2::s1) s2.
Proof.
  intros g f1 f2 s1 s2 SZ EQ; inv SZ; simpl in *. destruct n; simpl in *. inv H0.
  econstructor; simpl; eauto. omega.
  econstructor; simpl; eauto.
Qed.

Theorem step_simulation:
  forall S1 t S2,
  step fn_stack_requirements ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1') (SI: stack_inv S1) (SI': stack_inv S1'),
  (exists S2', plus (step fn_stack_requirements) tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.

- (* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_operation_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
  fold (sop ctx op). intros [v' [A B]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. erewrite eval_operation_preserved; eauto.
  exact symbols_preserved.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold (saddr ctx addr). intros [a' [P Q]].
  exploit Mem.loadv_inject; eauto. intros [v' [U V]].
  assert (eval_addressing tge (Vptr sp' Ptrofs.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
  rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Iload; eauto.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* store *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold saddr. intros [a' [P Q]].
  exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto.
  intros [m1' [U V]].
  assert (eval_addressing tge (Vptr sp' Ptrofs.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Istore; eauto.
  destruct a; simpl in H1; try discriminate.
  destruct a'; simpl in U; try discriminate.
  econstructor; eauto.
  eapply match_stacks_inside_store; eauto.
  {
    red; intros. erewrite Mem.store_stack_unchanged in H3; eauto.
  }
  eapply Mem.store_valid_block_1; eauto.
  eapply range_private_invariant; eauto.
  intros; split; auto. eapply Mem.perm_store_2; eauto.
  intros; eapply Mem.perm_store_1; eauto.
  intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.
  intros; eapply SSZ3; eauto. eapply Mem.perm_store_2; eauto.
  repeat rewrite_stack_blocks; eauto.

- (* call *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros (cu & fd' & A & B & C).
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply ros_is_function_transf; eauto.
  eapply sig_function_translated; eauto.
  econstructor.
  apply match_stacks_push. rewrite Mem.push_new_stage_nextblock.
  eapply match_stacks_cons; eauto. eapply Mem.valid_block_inject_1; eauto.
  4: eapply Mem.push_new_stage_inject; eauto.
  all: eauto.
  eapply agree_val_regs; eauto.
  repeat rewrite_stack_blocks.
  apply inline_sizes_up. auto.
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  right; split. simpl; omega. split. auto.
  econstructor.
  eapply match_stacks_inside_push_l.
  eapply match_stacks_inside_inlined; eauto.
  9: eapply Mem.inject_push_new_stage_left; eauto.
  all: eauto.
  red; intros. apply PRIV. inv H14. destruct H17. xomega.
  eapply Mem.valid_block_inject_1; eauto.
  apply agree_val_regs_gen; auto.
  red; intros. apply loc_private_push_l. apply PRIV. destruct H17. omega.
  repeat rewrite_stack_blocks.
  eapply inline_sizes_upstar; eauto.

- (* tailcall *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros (cu & fd' & A & B & C).
  assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
  { eapply range_private_free_left; eauto. inv FB. rewrite <- H6. auto. }
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* within the original function *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    simpl; auto.
    inv FB. eapply range_private_perms; eauto. xomega.
  destruct X as [m1' FREE].
  assert (Mem.inject F (1%nat :: g ++ l) m' m1') as INJfree.
  {
    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q].
    eelim Q; eauto. replace (ofs + delta - delta) with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  }
  edestruct (Mem.tailcall_stage_inject) as (m2' & TC & EXT). apply INJfree. eauto.
  inv SI'. inv MSA1.
  eapply Mem.free_top_tframe_no_perm; eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall; eauto.
  eapply ros_is_function_transf; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_bound with (bound := sp').
  eapply match_stacks_invariant; eauto.
  intros. revert H6; repeat rewrite_perms. destr.
  intros. revert H5; repeat rewrite_perms. destr.
  rewrite <- andb_assoc in Heqb0. apply andb_true_iff in Heqb0.
  destruct Heqb0. destruct peq; simpl in *; try congruence. subst. xomega.
  intros. revert H5; repeat rewrite_perms. destr.
  rewnb. xomega.
  rewnb. red in VB; xomega.
  eapply agree_val_regs; eauto.
  {
    red; intros b.
    repeat rewrite_stack_blocks. rewrite in_stack_cons.
    unfold in_frames; simpl.
    intros AA [[]|INS]; eauto.
    eapply SI0. rewrite AA.
    rewrite in_stack_cons; auto.
  }
  repeat rewrite_stack_blocks; eauto.
  intros AA BB; rewrite AA, BB in SIZES.
  eapply inline_sizes_record; eauto.

+ (* turned into a call *)
  exploit Mem.free_left_inject. eauto. eauto. intro INJFREE.
  assert (O < n)%nat. {
    inv MS0. congruence. omega.
  }
  exploit Mem.inject_tailcall_left_new_stage_right. apply INJFREE. auto. eauto. intro INJTC.
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply ros_is_function_transf; eauto.
  eapply sig_function_translated; eauto.
  econstructor.
  eapply match_stacks_push_r. rewrite Mem.push_new_stage_nextblock.  
  eapply match_stacks_untailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
  intros b1 b2 delta ofs. repeat rewrite_perms. destr.
  rewnb. xomega.
  {
    eapply range_private_invariant. apply PRIV'.
    intros b delta ofs. repeat rewrite_perms; destr.
    tauto.
  }
  eauto. eauto.
  eapply agree_val_regs; eauto.
  simpl; eauto.
  {
    red; intros b.
    repeat rewrite_stack_blocks.
    intros INS IFR.
    eapply SI0; eauto.
    rewrite INS. rewrite in_stack_cons in IFR |- *.
    destruct IFR as [IFR| INS']. easy. auto.
  }
  repeat rewrite_stack_blocks. intro EQ1; rewrite EQ1 in SIZES.
  simpl. destruct n. omega. apply inline_sizes_upright. auto.

+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  right; split. simpl; omega. split. auto.
  exploit Mem.free_left_inject; eauto. intro FREEINJ.

  eapply Mem.tailcall_stage_inject_left in FREEINJ; eauto.
  econstructor; eauto.
  eapply match_stacks_inside_inlined_tailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
  intros b1 b2 delta ofs; repeat rewrite_perms; destr.
  rewnb; xomega.
  eapply range_private_invariant. apply PRIV'.
  intros b delta ofs; repeat rewrite_perms; destr.
  auto.
  apply agree_val_regs_gen; auto.
  {
    red; intros b.
    repeat rewrite_stack_blocks.
    intros STK. rewrite in_stack_cons. intros [[]|INS];
    eapply SI0; eauto. rewrite STK, in_stack_cons; auto.
  }
  eapply range_private_invariant in PRIV'.
  red; intros; apply PRIV'.
  assert (dstk ctx <= dstk ctx').
  {
    red in H16; rewrite H16. apply align_le. apply min_alignment_pos.
  }
  omega.
  intros b delta ofs; repeat rewrite_perms. auto.
  tauto.
  repeat rewrite_stack_blocks.
  intro EQ1; rewrite EQ1 in SIZES.
  eapply inline_sizes_same_top. eauto.
  rewrite size_frames_tc. auto.

- (* builtin *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit match_stacks_inside_globalenvs; eauto. intros [bound MG].
  exploit tr_builtin_args; eauto. intros (vargs' & P & Q).
  exploit external_call_mem_inject; eauto.
    eapply match_stacks_inside_globals; eauto.
    apply Mem.push_new_stage_inject. eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  edestruct Mem.unrecord_stack_block_inject_parallel as (m2' & USB & INJ'). apply C. eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ibuiltin. eauto. eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved. eauto.
    eauto.
  econstructor.
    eapply match_stacks_inside_set_res.
    eapply match_stacks_inside_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros. eapply Mem.unrecord_stack_block_perm in H4. 2: eauto.
    eapply external_call_max_perm in H4. 2: eauto. apply Mem.push_new_stage_perm; auto.
    red; rewrite Mem.push_new_stage_nextblock; auto.
    intros. eapply Mem.unrecord_stack_block_perm in H4. 2: eauto.
    eapply external_call_max_perm in H4. 2: eauto. apply Mem.push_new_stage_perm; auto.
    red; rewrite Mem.push_new_stage_nextblock; auto.
    eapply Mem.unchanged_on_trans. apply Mem.push_new_stage_unchanged_on.
    eapply Mem.unchanged_on_trans. eapply Mem.unchanged_on_implies. apply E.
    intros. red. setoid_rewrite Mem.push_new_stage_perm. auto.
    eapply Mem.unrecord_stack_block_unchanged_on. auto.
    rewnb. xomega.
    eauto. auto.
  destruct res; simpl; [apply agree_set_reg;auto|idtac|idtac]; eapply agree_regs_incr; eauto.
  auto. eauto.
  red; intro b.
  repeat rewrite_stack_blocks. simpl.
  intro INFR.
  eapply SI0 in INFR.
  destruct INFR as (b' & delta & FF); exists b', delta; eauto.
  red; repeat rewnb. eauto.
  eapply range_private_extcall; eauto.
  intros b ofs p VB' PP.
  exploit Mem.push_new_stage_perm; intros [FW _]; apply FW; clear FW.
  eapply external_call_max_perm. eauto. red; rewnb; auto.
  revert PP. rewrite_perms. auto.
  eapply Mem.unchanged_on_trans. apply Mem.push_new_stage_unchanged_on.
  eapply Mem.unchanged_on_trans. eapply Mem.unchanged_on_implies. apply E.
  intros. red. setoid_rewrite Mem.push_new_stage_perm. auto.
  eapply Mem.unrecord_stack_block_unchanged_on. auto.
  unfold Mem.valid_block.
  auto.
  intros. apply SSZ2. revert H3; repeat rewrite_perms. eauto.
  repeat rewrite_stack_blocks. simpl. inv SI'. inv MSA1. rewrite ! in_stack_cons. right; left.
  rewrite in_frames_cons. unfold in_frame, get_frame_blocks. eexists; rewrite BLOCKS. simpl. auto.
  intros. apply SSZ3. revert H3; repeat rewrite_perms. eauto.
  repeat rewrite_stack_blocks. simpl. inv SI. inv MSA1. rewrite ! in_stack_cons. right; left.
  rewrite in_frames_cons. unfold in_frame, get_frame_blocks. eexists; rewrite BLOCKS. simpl. auto.
  repeat rewrite_stack_blocks. simpl. auto.
  
- (* cond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (eval_condition cond rs'##(sregs ctx args) m' = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto.
  destruct b; econstructor; eauto.

- (* jumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (Val.inject F rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
  rewrite H0 in H2; inv H2.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  rewrite list_nth_z_map. rewrite H1. simpl; reflexivity.
  econstructor; eauto.

- (* return *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    simpl; auto.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); omega.
  destruct X as [m1' FREE].
  assert (Mem.inject F (1%nat::g++l) m' m1') as INJfree.
  {
    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. inversion FB; subst.
    assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H8 in PRIV. eapply range_private_free_left; eauto.
    rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [A B].
    eelim B; eauto. replace (ofs + delta - delta) with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  }
  left; econstructor; split.
  eapply plus_one. eapply exec_Ireturn; eauto.
  econstructor; eauto. 
  eapply match_stacks_bound with (bound := sp').
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    intros. eapply Mem.perm_free_1; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    rewnb. xomega.
    rewnb. red in VB. xomega.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  {
    red; intros b.
    repeat rewrite_stack_blocks.
    intro IFR.
    eapply SI0; eauto.
  }
  repeat rewrite_stack_blocks; auto.
  
+ (* inlined *)
  right. split. simpl. omega. split. auto.
  exploit Mem.free_left_inject; eauto. intros FRINJ.
  assert (O < n)%nat. {
    inv MS0. congruence. omega.
  } 
  econstructor; eauto. 
  eapply match_stacks_inside_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto.
  rewnb. xomega.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  * red; intros b.
    repeat rewrite_stack_blocks.
    intro IFR.
    eapply SI0; eauto.
  * eapply range_private_invariant.
    eapply range_private_free_left; eauto.
    inv FB. rewrite <- H6; eauto.
    intros; split; auto. tauto.
  * repeat rewrite_stack_blocks; auto.

- (* internal function, not inlined *)
  assert (A: exists f', tr_function cunit f f' /\ fd' = Internal f').
  { Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. }
  destruct A as [f' [TR1 EQ]].
  assert (TR: tr_function prog f f').
  { eapply tr_function_linkorder; eauto. }
  inversion TR; subst.
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Zle_refl.
    instantiate (1 := fn_stacksize f'). inv H2. xomega.
  intros [F' [m1' [sp' [A [B [C [D E]]]]]]].
  exploit Mem.record_stack_blocks_inject_parallel.
  apply B. 7: eauto.
  + instantiate (1 := make_singleton_frame_adt sp' (fn_stacksize f') sz).
    red; simpl; intros; auto.
    constructor; auto.
    simpl. rewrite D. inversion 1; subst.
    eexists; split. eauto.
    unfold inject_frame_info.
    simpl.
    intros.
    inv H2.
    rewrite Z.max_r by omega.
    split. omega. eapply Z.lt_le_trans. 2: apply H16.
    rewrite Zmax_spec in H10, H13. destr_in H10. omega. destr_in H13. omega. omega.
  + repeat rewrite_stack_blocks. unfold in_frame; simpl; intros. intros [?|[]]; subst.
    eapply Mem.in_stack_valid in H9. eapply Mem.fresh_block_alloc in H9; eauto.
  + red; unfold in_frame; simpl. intros ? [?|[]]; subst. eapply Mem.valid_new_block; eauto.
  + simpl. intros b fi o k p [AA|[]]; inv AA.
    rewrite_perms. rewrite peq_true. simpl. intros; rewrite Z.max_r; omega.
  + unfold in_frame; simpl.
    intros b1 b2 delta FB. split; intros [?|[]]; subst; left.
    congruence.
    destruct (peq stk b1); auto.
    rewrite E in FB; auto. eapply Mem.valid_block_inject_2 in FB; eauto. eapply Mem.fresh_block_alloc in FB; eauto. easy.
  + reflexivity.
  + inv SI'. rewrite_stack_blocks. inv TOPNOPERM. constructor. auto.
  + repeat rewrite_stack_blocks.
    eapply inline_sizes_le; eauto.

  + intros (m2' & P & Q).
    left; econstructor; split.
    * eapply plus_one. eapply exec_function_internal; eauto.
    * rewrite H6, H7. econstructor. 
      -- instantiate (3 := F'). apply match_stacks_inside_base.
         assert (SP: sp' = Mem.nextblock m'0) by (eapply Mem.alloc_result; eauto).
         rewrite <- SP in MS0.
         eapply match_stacks_invariant; eauto.
         ++ intros. destruct (eq_block b1 stk).
            subst b1. rewrite D in H9; inv H9. eelim Plt_strict; eauto.
            rewrite E in H9; auto.
         ++ intros. exploit Mem.perm_alloc_inv. eexact H. eauto.
            destruct (eq_block b1 stk); intros; auto.
            subst b1. rewrite D in H9; inv H9. eelim Plt_strict; eauto.
            intros. eapply Mem.perm_alloc_1; eauto.
            intros. exploit Mem.perm_alloc_inv. eexact A.
            eapply Mem.record_stack_block_perm; eauto.
            eapply Mem.record_stack_block_perm'; eauto.
            eapply Mem.perm_inject; eauto.
            eapply Mem.record_stack_block_perm; eauto.
            rewrite dec_eq_false; auto.
            intros.
            eapply Mem.perm_alloc_4. eauto. eapply Mem.record_stack_block_perm; eauto. auto.
            destr. subst.
            rewrite D in H9; inv H9; xomega.
         ++ intros. eapply Mem.record_stack_block_perm'. eauto.
            eapply Mem.perm_alloc_1; eauto.
         ++ intros. eapply Mem.perm_alloc_4. eauto.
            eapply Mem.record_stack_block_perm. eauto.
            eauto. intro; subst; xomega.
         ++ rewrite (Mem.record_stack_block_nextblock _ _ _ H0), (Mem.nextblock_alloc _ _ _ _ _ H). xomega.
         ++ auto.
         ++ auto.
      -- eauto.
      -- auto. 
      -- apply agree_regs_init_regs. eauto.
         inv H2. auto.
      -- congruence.
      -- eauto.
      -- intro b.
         repeat rewrite_stack_blocks. rewrite in_stack_cons, in_frames_cons.
         intro EQ1.
         generalize (SI0 b). rewrite EQ1. rewrite in_stack_cons.
         intros HYP [(f1 & EQ & IFR)|INS]. inv EQ.
         destruct IFR as [EQ|[]]. simpl in EQ. subst. eauto. edestruct HYP as (b' & delta & FB); eauto.
      -- red. erewrite Mem.record_stack_block_nextblock. eapply Mem.valid_new_block; eauto. eauto.
      -- red; intros. split.
         ++ eapply Mem.record_stack_block_perm'; eauto.
            eapply Mem.perm_alloc_2; eauto. inv H2; xomega.
         ++ intros; red; intros. eapply Mem.record_stack_block_perm in H11; eauto.
            exploit Mem.perm_alloc_inv. eexact H. eauto.
            destruct (eq_block b stk); intros.
            subst. rewrite D in H10; inv H10. inv H2; xomega.
            rewrite E in H10; auto. eelim Mem.fresh_block_alloc.
            eexact A. eapply Mem.valid_block_inject_2; eauto.
      -- auto.
      -- intros.
         eapply Mem.record_stack_block_perm in H9; eauto.
         exploit Mem.perm_alloc_inv; eauto. rewrite dec_eq_true. omega.
      -- intros.
         eapply Mem.record_stack_block_perm in H9; eauto.
         exploit Mem.perm_alloc_inv. 2: eauto. eauto. rewrite dec_eq_true. omega.
      -- repeat rewrite_stack_blocks. intros S1 S2.
         revert SIZES. rewrite S1, S2.
         intros; eapply inline_sizes_record'; eauto.
         
- (* internal function, inlined *)
  inversion FB; subst.
  exploit Mem.alloc_left_mapped_inject.
    eauto.
    eauto.
    (* sp' is valid *)
    instantiate (1 := sp'). auto.
    (* offset is representable *)
    instantiate (1 := dstk ctx). generalize (Zmax2 (fn_stacksize f) 0). omega.
    (* size of target block is representable *)
    intros. right. exploit SSZ2; eauto with mem. inv FB; omega.
    (* we have full permissions on sp' at and above dstk ctx *)
    intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
    eapply range_private_perms; eauto. xomega.
    (* offset is aligned *)
    replace (fn_stacksize f - 0) with (fn_stacksize f) by omega.
    inv FB. apply min_alignment_sound; auto.
    (* nobody maps to (sp, dstk ctx...) *)
    intros. exploit (PRIV (ofs + delta')); eauto. xomega.
    intros [A B]. eelim B; eauto.
    replace (ofs + delta' - delta') with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    intros [F' [A [B [C D]]]].
  destruct (stack_top_frame_at_position (Mem.stack m'0) sp') as (f1 & FAP & INF).
  inv SI'. red; inv MSA1. simpl. unfold get_frames_blocks. simpl.
  unfold get_frame_blocks. rewrite BLOCKS. simpl. auto.
  exploit Mem.record_stack_blocks_inject_left. apply A.
  eauto.   
  2: eauto.
  {
    red. simpl. intros f0 eq. inv eq. intro HP.
    inv SI'. inv MSA1. rewrite <- H11 in FAP. apply frame_at_pos_last in FAP. subst.
    eexists; split. reflexivity.
    red. simpl.
    constructor; auto. simpl. intros. rewrite BLOCKS.
    rewrite C in H7. inv H7. eexists; split. left; reflexivity.
    unfold inject_frame_info.
    simpl.
    intros.
    rewrite Zmax_spec in H7. destr_in H7. omega.
    split. omega.
    rewrite SIZE. cut (o < mstk ctx). rewrite Z.max_r by omega. omega.
    rewrite H3.
    rewrite Z.max_l; omega.
  }
  intros MINJ'.
  exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]].
  left; econstructor; split.
  eapply plus_left. eapply exec_Inop; eauto. eexact P. traceEq.
  econstructor.
  + eapply match_stacks_inside_record_left.
    eapply match_stacks_inside_alloc_left; eauto.
    eapply match_stacks_inside_invariant; eauto.
    xomega.
    omega. eauto.
  + eauto.
  + auto.
  + apply agree_regs_incr with F; auto.
  + auto.
  + eauto.
  + intro b.
    repeat rewrite_stack_blocks. rewrite in_stack_cons, in_frames_cons.
    intro EQ1. generalize (SI0 b).
    rewrite EQ1. rewrite in_stack_cons.
    intros HYP [(ff1 & eq & IFR)|INS].
    ++ inv eq. destruct IFR as [eq|[]]. simpl in eq; subst; simpl; eauto.
    ++ edestruct HYP as (b' & delta & FB'); eauto; do 2 eexists; eapply C; eauto.
  + auto.
  + rewrite H3.
    eapply range_private_invariant.
    eapply range_private_alloc_left; eauto.
    2: tauto.
    split; auto. eapply Mem.record_stack_block_perm; eauto.
  + auto.
  + auto.
  + intros.
    eapply Mem.record_stack_block_perm in H7. 2: eauto.
    eapply Mem.perm_alloc_inv in H7. 2: eauto. rewrite pred_dec_true in H7. auto. auto.
  + repeat rewrite_stack_blocks.
    intro EQ1. rewrite EQ1 in SIZES.
    eapply inline_sizes_record_left; eauto.

- (* external function *)
  exploit match_stacks_globalenvs; eauto. intros [bound MG].
  exploit external_call_mem_inject; eauto.
    eapply match_globalenvs_preserves_globals; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  simpl in FD. inv FD.
  left; econstructor; split.
  eapply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor. 
    eapply match_stacks_bound with (Mem.nextblock m'0).
    eapply match_stacks_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto.
    intros; eapply external_call_max_perm; eauto.
    eapply external_call_nextblock; eauto.
    xomega.
    eapply external_call_nextblock; eauto.
    auto. eauto.
    red; intro b.
    erewrite <- external_call_stack_blocks; eauto.
    intro INFR.
    eapply SI0 in INFR.
    destruct INFR as (b' & delta & FF); exists b', delta; eauto.
    repeat rewrite_stack_blocks; eauto.

- (* return fron noninlined function *)
  inv MS0.
+ (* normal case *)
  edestruct Mem.unrecord_stack_block_inject_parallel as (m2' & USB & INJ); eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_return; eauto.
  econstructor; eauto.
  * apply match_stacks_inside_set_reg. eapply match_stacks_inside_invariant. 
    2: apply MS. 
    all: eauto.
    -- simpl; intros b1 b2 delta ofs Fb1 PLE. rewrite_perms. auto. 
    -- simpl; intros b ofs PLE. rewrite_perms. auto.
    -- simpl; intros b ofs k p PLE. rewrite_perms. auto.
    -- rewnb. xomega.
  * apply agree_set_reg; auto.
  * intro b. rewrite_stack_blocks. eauto. intros. apply in_stack_tl in H0. eauto.
  * red; rewnb. auto.
  * eapply range_private_invariant. eauto. intros b delta ofs. rewrite_perms. eauto.
    intro ofs; rewrite_perms. auto.
  * intro; rewrite_perms; auto.
  * intro; rewrite_perms; auto.
  * repeat rewrite_stack_blocks.
    eapply inline_sizes_down; eauto.
    
+ (* untailcall case *)
  inv MS; try congruence.
  rewrite RET in RET0; inv RET0.
  edestruct Mem.unrecord_stack_block_inject_parallel as (m2' & USB & INJ); eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_return. eauto.
  eapply match_regular_states. 
  eapply match_stacks_inside_set_reg; eauto.
  eapply match_stacks_inside_invariant.
  2: apply MS0. all: eauto.
  simpl; intros b1 b2 delta ofs Fb1 PLE. rewrite_perms. auto.
  simpl; intros b ofs PLE. rewrite_perms. auto.
  simpl; intros b ofs k p PLE. rewrite_perms. auto.
  rewnb. xomega.
  * apply agree_set_reg; auto.
  * intro b; rewrite_stack_blocks. intro IStl; apply in_stack_tl in IStl; eauto.
  * red; rewnb; auto.
  * eapply range_private_invariant.
    red; intros. destruct (zlt ofs (dstk ctx)).
    red. apply PAD. omega. apply PRIV. omega.
    intros b delta ofs. repeat rewrite_perms. intuition.
    intro; rewrite_perms. auto.
  * intro; rewrite_perms; auto.
  * intro; rewrite_perms; auto.
  * repeat rewrite_stack_blocks.
    eapply inline_sizes_down; eauto.

- (* return from inlined function *)
  inv MS0; try congruence. rewrite RET0 in RET; inv RET.
  unfold inline_return in AT.
  assert (PRIV': range_private F m m'0 sp' (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
    red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. omega. apply PRIV. omega.
  exploit Mem.unrecord_stack_block_inject_left; eauto. omega.
  inv SI. auto. intro INJ'.
  destruct or.
+ (* with a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. simpl. reflexivity.
  econstructor; eauto. apply match_stacks_inside_set_reg; auto.
  eapply match_stacks_inside_invariant.
  2: apply MS. all: eauto.
  simpl; intros b1 b2 delta ofs Fb1 PLE. rewrite_perms. auto.
  rewnb. xomega.
  * apply agree_set_reg; auto.
  * intro b; rewrite_stack_blocks. intro IStl; apply in_stack_tl in IStl; eauto.
  * eapply range_private_invariant. apply PRIV'.
    intros b delta ofs. repeat rewrite_perms. intuition. auto.
  * intro; rewrite_perms; auto.
  * repeat rewrite_stack_blocks.
    eapply inline_sizes_downstar; eauto.
    
+ (* without a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply match_stacks_inside_invariant.
  2: apply MS. all: eauto.
  simpl; intros b1 b2 delta ofs Fb1 PLE. rewrite_perms. auto.
  rewnb. xomega.
  * subst vres. apply agree_set_reg_undef'; auto.
  * intro b; rewrite_stack_blocks. intro IStl; apply in_stack_tl in IStl; eauto.
  * eapply range_private_invariant. apply PRIV'.
    intros b delta ofs. repeat rewrite_perms. intuition. auto.
  * intro; rewrite_perms; auto.
  * repeat rewrite_stack_blocks. eapply inline_sizes_downstar; eauto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state (*SACC:*)fn_stack_requirements prog st1 -> exists st2, initial_state (*SACC:*)fn_stack_requirements tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (cu & tf & FIND & TR & LINK).
  exists (Callstate nil tf nil (Mem.push_new_stage m2) (fn_stack_requirements (prog_main prog))); split.
  - erewrite <- match_program_main; eauto.
    econstructor; eauto.
    eapply (Genv.init_mem_match TRANSF); eauto.
    rewrite symbols_preserved. replace (prog_main tprog) with (prog_main prog). auto.
    symmetry; eapply match_program_main; eauto.
    rewrite <- H3. eapply sig_function_translated; eauto.
  - edestruct (Mem.record_init_sp_flat_inject) as (m2' & RIS & INJ).
    eapply Genv.initmem_inject; eauto. omega. eauto. auto.
    rewrite RIS in H4; inv H4. 
    eapply match_call_states.
    5: apply Mem.push_new_stage_inject; eauto. all: eauto.
    2: instantiate (2 := nil); simpl; eauto.
    + apply match_stacks_nil with (Mem.nextblock m2).
      * constructor; intros.
        unfold Mem.flat_inj. apply pred_dec_true; auto.
        unfold Mem.flat_inj in H. destr_in H.
        cut (Plt b0 (Mem.nextblock m0)). rewnb. xomega. eapply Genv.find_symbol_not_fresh; eauto.
        cut (Plt b0 (Mem.nextblock m0)). rewnb. xomega. eapply Genv.find_funct_ptr_not_fresh; eauto.
        cut (Plt b0 (Mem.nextblock m0)). rewnb. xomega. eapply Genv.find_var_info_not_fresh; eauto.
      * rewnb. apply Ple_refl.
    + intro b0.
      repeat rewrite_stack_blocks.
      rewrite ! in_stack_cons.
      intros [[]|[[|[]]|[]]]. 
      simpl in H; subst. rewnb. 
      unfold Mem.flat_inj.
      destr. eauto. xomega.
    + repeat rewrite_stack_blocks. simpl.
      repeat econstructor; simpl; eauto; omega.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H.
  exploit match_stacks_empty; eauto. intros EQ; subst. inv VINJ. constructor.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics (*SACC:*)fn_stack_requirements prog) (semantics (*SACC:*)fn_stack_requirements tprog).
Proof.
  eapply forward_simulation_star with (match_states := fun s1 s2 => match_states s1 s2 /\ stack_inv s1 /\ stack_inv s2).
  - apply senv_preserved.
  - simpl; intros s1 IS1. edestruct transf_initial_states as (s2 & IS2 & MS); eauto.
    eexists; split; eauto. split; auto. split; eapply stack_inv_initial; eauto.
  - simpl; intros s1 s2 m (MS & SI1 & SI2) FS. eapply transf_final_states; eauto.
  - instantiate (1 := measure).
    simpl; intros s1 t s1' STEP s2 (MS & SI1 & SI2).
    exploit step_simulation; eauto.
    intros [(s2' & PLUS & MS')|(MES & TE0 & MS')].
    + left; eexists; split; eauto. split.
      eauto. split.
      eapply stack_inv_inv; eauto.
      eapply inv_plus. apply stack_inv_inv; eauto. eauto. eauto.
    + right; split; auto. split; auto. split; auto.
      split; auto.
      eapply stack_inv_inv; eauto.
Qed.

End INLINING.

End STACK_WRAPPER.