Require Import Coqlib Integers AST Maps.
Require Import Linking.
Import ListNotations.

Set Implicit Arguments.

Lemma is_def_internal_dec' : forall (F V:Type) (f:F -> bool) (def: option (globdef F V)),
    {is_def_internal f def = true} + {is_def_internal f def <> true}.
Proof.
  decide equality.
Qed.

Lemma is_def_internal_dec : forall (F V:Type) (f:F -> bool) (def: option (globdef F V)),
    {is_def_internal f def = true} + {is_def_internal f def = false}.
Proof.
  intros F V f def.
  generalize (is_def_internal_dec' f def).
  intro H.
  inv H. auto.
  rewrite not_true_iff_false in H0. auto.
Qed.  

Lemma link_fundef_inv1 : forall (F:Type) (f: AST.fundef F) f' e, 
    link_fundef f (External e) = Some f' -> f = f'.
Proof.
  intros F f f' e LINK.
  destruct f. simpl in *. destruct e; try congruence.
  simpl in LINK. destruct (external_function_eq e0 e); congruence.
Qed.

Lemma link_extern_fundef_inv: forall (F:Type) 
                                (f f' f'': AST.fundef F),
    is_fundef_internal f = false ->
    link f' f = Some f'' -> 
    f' = f''.
Proof.
  intros F f f' f'' FINT LINK.
  unfold link in LINK. 
  Transparent Linker_fundef.
  unfold Linker_fundef in LINK.
  destruct f; simpl in *. congruence.
  simpl in LINK.
  apply link_fundef_inv1 in LINK. auto.
Qed.

Lemma link_external_fundefs: forall (F: Type) (f1 f2 f: AST.fundef F), 
    is_fundef_internal f1 = false ->
    is_fundef_internal f2 = false ->
    link_fundef f1 f2 = Some f ->
    is_fundef_internal f = false.
Proof.
  intros F f1 f2 f INT1 INT2 LINK.
  generalize (link_extern_fundef_inv f2 f1 INT2 LINK).
  intros. subst. auto.
Qed.


Lemma link_extern_gfundef_inv: forall (F V:Type) (LV: Linker V)
                             (f: AST.fundef F) (g g': (globdef (AST.fundef F) V)),
    is_fundef_internal f = false ->
    link g (Gfun f) = Some g' -> 
    g = g'.
Proof.
  intros F V LV f g g' INT LINK.
  destruct g. 
  - unfold link in LINK. 
    Transparent Linker_def.
    unfold Linker_def in LINK.
    simpl in LINK. destruct (link_fundef f0 f) eqn:LINKF; try congruence.
    inv LINK.
    generalize (link_extern_fundef_inv _ _ INT LINKF).
    intros. subst.
    auto.
  - simpl in LINK. congruence.
Qed.

Lemma link_external_varinit: forall (V: Type) (LV: Linker V)(v1 v2: globvar V) l, 
    is_var_internal v1 = false ->
    is_var_internal v2 = false ->
    link_varinit (gvar_init v1) (gvar_init v2) = Some l ->
    classify_init l <> Init_definitive l.
Proof.
  intros V LV v1 v2 l INT1 INT2 LINK.
  unfold link_varinit in LINK.
  unfold is_var_internal in *.
  destr_in LINK. inv LINK.
  destr_in INT2.
  destr_in INT2. inv LINK. congruence.
  destr_in LINK; try congruence.
  inv LINK. congruence.
Qed.

Lemma link_external_vars: forall (V: Type) (LV: Linker V)(v1 v2 v: globvar V), 
    is_var_internal v1 = false ->
    is_var_internal v2 = false ->
    link v1 v2 = Some v ->
    is_var_internal v = false.
Proof.
  intros V LV v1 v2 v INT1 INT2 LINK.
  unfold link in LINK.
  Transparent Linker_vardef.
  unfold Linker_vardef in LINK.
  unfold link_vardef in LINK.
  destr_in LINK. destr_in LINK.
  destr_in LINK. inv LINK.
  unfold is_var_internal. simpl.
  unfold link in Heqo0.
  Transparent Linker_varinit.
  unfold Linker_varinit in Heqo0.
  generalize (link_external_varinit _ v1 v2 INT1 INT2 Heqo0).
  intros. destruct (classify_init l); auto.
  congruence.
Qed.


Lemma link_internal_external_varinit: forall (V: Type) (LV: Linker V)(v1 v2: globvar V) l, 
    is_var_internal v1 = true ->
    is_var_internal v2 = false ->
    link_varinit (gvar_init v1) (gvar_init v2) = Some l ->
    gvar_init v1 = l /\
    classify_init l = Init_definitive l.
Proof.
  intros V LV v1 v2 l INT1 INT2 LINK.
  unfold link_varinit in LINK.
  unfold is_var_internal in *.
  destr_in LINK. destr_in LINK.
  inv LINK. auto.
  destr_in LINK; try congruence.
  inv LINK. auto.
Qed.

Lemma link_internal_external_vars: forall (V:Type) (LV: Linker V) (v1 v2 v3: globvar V),
    is_var_internal v1 = true ->
    is_var_internal v2 = false ->
    link v1 v2 = Some v3 ->
    gvar_init v1 = gvar_init v3 /\ is_var_internal v3 = true.
Proof.
  intros V LV v1 v2 v3 INT1 INT2 LINK.
  unfold link in LINK.
  Transparent Linker_vardef.
  unfold Linker_vardef in LINK.
  unfold link_vardef in LINK.
  destr_in LINK. destr_in LINK.
  destr_in LINK. inv LINK.
  unfold is_var_internal. simpl.
  unfold link in Heqo0.
  Transparent Linker_varinit.
  unfold Linker_varinit in Heqo0.
  generalize (link_internal_external_varinit _ v1 v2 INT1 INT2 Heqo0).
  destruct 1.
  split; auto. rewrite H0; auto.
Qed.
