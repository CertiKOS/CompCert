Require Import Coqlib Integers AST Maps.
Require Import Linking.
Require Import LocalLib.
Import ListNotations.

Set Implicit Arguments.

Lemma is_def_internal_dec' : forall (F V:Type) (f:F -> bool) (def: globdef F V),
    {is_def_internal f def = true} + {is_def_internal f def <> true}.
Proof.
  decide equality.
Qed.

Lemma is_def_internal_dec : forall (F V:Type) (f:F -> bool) (def: globdef F V),
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

Definition is_var_comm V (v: globvar V) := 
  match classify_init (gvar_init v) with
  | Init_common _ => true
  | _ => false
  end.

Definition is_var_extern V (v: globvar V) := 
  match classify_init (gvar_init v) with
  | Init_extern => true
  | _ => false
  end.

Lemma extern_var_init_nil : forall V (v:globvar V),
  is_var_extern v = true -> gvar_init v = nil.
Proof.
  intros V v EXT.
  unfold is_var_extern in EXT.
  destruct (gvar_init v); try congruence.
  destr_in EXT; try congruence.
Qed.


Lemma var_not_internal_iff : forall V (v: globvar V),
    is_var_internal v = false <->
    is_var_comm v = true \/ is_var_extern v = true.
Proof. 
  intros V v; split;
  unfold is_var_internal, is_var_comm, is_var_extern;
  destruct (classify_init (gvar_init v)); try congruence; auto.
  destruct 1; try congruence.
Qed.

Lemma link_internal_comm_varinit: forall (V: Type) (LV: Linker V)(v1 v2: globvar V) l, 
    is_var_internal v1 = true ->
    is_var_comm v2 = true ->
    link_varinit (gvar_init v1) (gvar_init v2) = Some l ->
    gvar_init v1 = l /\
    init_data_list_size (gvar_init v1) = init_data_list_size (gvar_init v2) /\
    classify_init l = Init_definitive l.
Proof.
  intros V LV v1 v2 l INT1 INT2 LINK.
  unfold link_varinit in LINK.
  unfold is_var_internal, is_var_comm in *.
  destr_in LINK. destr_in LINK.
  destruct zeq; try congruence.
  subst. inv LINK. cbn.
  split; auto.
  erewrite Z_max_0.
  split. omega. auto.
  apply init_data_list_size_pos.
Qed.

Lemma link_comm_vars_init : forall V (v1 v2: globvar V) init,
    is_var_comm v1 = true
    -> is_var_comm v2 = true
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some init
    -> (init_data_list_size (gvar_init v1)) =
      (init_data_list_size (gvar_init v2)) /\
      init = gvar_init v2.
Proof.
  intros V v1 v2 init INT1 INT2 LINK.
  unfold is_var_comm in *.
  destruct (gvar_init v1); cbn in *; try congruence.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
  destruct (gvar_init v2); cbn in *; try congruence.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
  destruct zeq; try congruence.
  inv LINK.
  repeat (rewrite Z.add_comm; cbn).
  split; auto.
Qed.

Lemma link_comm_extern_var_init : forall V (v1 v2: globvar V) init,
    is_var_comm v1 = true
    -> is_var_extern v2 = true
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some init
    -> init = (gvar_init v1).
Proof.
  intros V v1 v2 init INT1 INT2 LINK.
  unfold is_var_comm, is_var_extern in *.
  destruct (gvar_init v1); cbn in *; try congruence.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
  destruct (gvar_init v2); cbn in *; try congruence.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
Qed.

Lemma link_extern_comm_var_init : forall V (v1 v2: globvar V) init,
    is_var_extern v1 = true
    -> is_var_comm v2 = true
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some init
    -> init = (gvar_init v2).
Proof.
  intros V v1 v2 init INT1 INT2 LINK.
  unfold is_var_comm, is_var_extern in *.
  destruct (gvar_init v1); cbn in *; try congruence.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
Qed.

Lemma link_extern_vars_init : forall V (v1 v2: globvar V) init,
    is_var_extern v1 = true
    -> is_var_extern v2 = true
    -> link_varinit (gvar_init v1) (gvar_init v2) = Some init
    -> init = nil.
Proof.
  intros V v1 v2 init INT1 INT2 LINK.
  unfold is_var_extern in *.
  destruct (gvar_init v1); cbn in *; try congruence.
  destruct (gvar_init v2); cbn in *; try congruence.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
  destruct i; cbn in *; try congruence.
  destruct l; cbn in *; try congruence.
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

(* SACC
Existing Instance Linker_option. *)
Existing Instance Linker_fundef.

Lemma link_internal_fundefs_none: forall F (f1 f2:fundef F),
    is_fundef_internal f1 = true ->
    is_fundef_internal f2 = true ->
    link_fundef f1 f2 = None.
Proof.
  intros F f1 f2 INT1 INT2.
  destruct f1, f2.
  - cbn. auto.
  - cbn in *. congruence.
  - cbn in *. congruence.
  - cbn in *. congruence.
Qed.

Lemma link_internal_varinit_none: forall {V} {LV: Linker V} (v1 v2:globvar V),
    is_var_internal v1 = true ->
    is_var_internal v2 = true ->
    link_varinit (gvar_init v1) (gvar_init v2) = None.
Proof.
  intros V LV v1 v2 INT1 INT2.
  unfold link_varinit.
  unfold is_var_internal in *.
  destr_in INT1.
  destr_in INT2.
Qed.


Lemma link_internal_vardefs_none: forall {V} {LV: Linker V} (v1 v2:globvar V),
    is_var_internal v1 = true ->
    is_var_internal v2 = true ->
    link_vardef v1 v2 = None.
Proof.
  Local Transparent Linker_varinit.
  intros V LV v1 v2 INT1 INT2.
  unfold link_vardef.
  destr. destr. destr.
  generalize (link_internal_varinit_none _ _ INT1 INT2).
  cbn in *.
  intros. congruence.
Qed.

Lemma link_int_defs_none: forall {F V} {LV: Linker V} (def1 def2: globdef (fundef F) V),
    is_def_internal is_fundef_internal def1 = true ->
    is_def_internal is_fundef_internal def2 = true ->
    link def1 def2 = None.
Proof.
  Local Transparent Linker_def Linker_fundef Linker_vardef.
  intros F V LV def1 def2 INT1 INT2.
  cbn.
  unfold is_def_internal in *.
  destr_in INT1; destr_in INT2;
  destr_in INT1; destr_in INT2; subst.
  - unfold link. cbn.   
    erewrite link_internal_fundefs_none; eauto.
  - cbn. 
    erewrite link_internal_vardefs_none; eauto.
Qed.

Lemma link_int_defs_some_inv: forall {F V} {LV: Linker V} (def1 def2 def: globdef (fundef F) V),
    is_def_internal is_fundef_internal def1 = true ->
    link def1 def2 = Some def ->
    is_def_internal is_fundef_internal def2 = false.
Proof.
  intros F V LV def1 def2 def INT LINK.
  destruct (is_def_internal is_fundef_internal def2) eqn:INT'.
  erewrite link_int_defs_none in LINK; eauto. congruence.
  auto.
Qed.

Lemma link_fundef_pres_int_def:
  forall (F : Type) (f1 f2 f : fundef F),
  is_fundef_internal f1 = true ->
  link_fundef f1 f2 = Some f -> is_fundef_internal f = true.
Proof.
  intros F f1 f2 f INT LINK.
  unfold link_fundef in LINK.
  destruct f1. destruct f2; try congruence.
  destruct e; try congruence.
  destruct f2. destruct e; try congruence.
  inv LINK. auto.
  destruct external_function_eq. try congruence.
  congruence.
Qed.

Lemma link_vardef_pres_int_def: forall {V} {LV: Linker V} (v1 v2 v: globvar V),
    is_var_internal v1 = true ->
    link_vardef v1 v2 = Some v ->
    is_var_internal v = true.
Proof.
  intros V LV v1 v2 v INT LINK.
  unfold link_vardef in LINK.
  destr_in LINK. destr_in LINK. destr_in LINK.
  inv LINK. cbn in Heqo0.
  destruct (is_var_internal v2) eqn:INT'.
  - generalize (link_internal_varinit_none _ _ INT INT').
    intros LINK'. congruence.
  - apply link_internal_external_varinit in Heqo0; auto.
    destruct Heqo0. subst.
    unfold is_var_internal. cbn. rewrite H0. auto.
Qed.


Lemma link_def_pres_int_def: forall {F V} {LV: Linker V} (def1 def2 def: globdef (fundef F) V),
    is_def_internal is_fundef_internal def1 = true ->
    link_def def1 def2 = Some def ->
    is_def_internal is_fundef_internal def = true.
Proof.
  intros F V LV def1 def2 def INT LINK.
  cbn in *. destruct def1. cbn in *.
  destruct def2. destr_in LINK. inv LINK.
  eapply link_fundef_pres_int_def; eauto.
  congruence.
  cbn in LINK. destruct def2; try congruence.
  destr_in LINK. inv LINK.
  eapply link_vardef_pres_int_def; eauto.
Qed.

(* SACC
Lemma link_option_pres_int_def: forall {F V} {LV: Linker V} (def1 def2 def: option (globdef (fundef F) V)),
    is_def_internal is_fundef_internal def1 = true ->
    link_option def1 def2 = Some def ->
    is_def_internal is_fundef_internal def = true.
Proof.
  intros F V LV def1 def2 def INT LINK.
  cbn in LINK.
  unfold link_option in LINK.
  destruct def. destruct def1. destruct def2. destr_in LINK.
  - inv LINK. 
    eapply link_def_pres_int_def; eauto. eapply Heqo.
  - inv LINK. auto.
  - inv LINK. cbn in INT. congruence.
  - destruct def1. destruct def2. destr_in LINK.
    congruence.
    inv LINK. cbn in INT. congruence.
Qed.
*)

Lemma link_external_defs : 
  forall {F V} {LV: Linker V}
    (def1 def2 def: globdef (AST.fundef F) V),
    is_def_internal is_fundef_internal def1 = false ->
    is_def_internal is_fundef_internal def2 = false ->
    link_def def1 def2 = Some def ->
    is_def_internal is_fundef_internal def = false.
Proof.
  intros F V LV def1 def2 def INT1 INT2 LINK.
  unfold link_def in LINK.
  destruct def1, def2.
  - 
    destruct (link f f0) eqn:LINKF; try congruence. inv LINK.
          unfold link in LINKF.
      Transparent Linker_fundef.
      unfold Linker_fundef in LINKF.
      simpl in *.
      apply link_external_fundefs with f f0; eauto.
 - congruence.   
 - congruence.
 - destruct (link v v0) eqn:LINKV; try congruence. inv LINK.
   simpl in *.
   apply link_external_vars with _ v v0; eauto.
Qed.    


(** Properties *)
Local Transparent Linker_def.
Local Transparent Linker_fundef.
Local Transparent Linker_vardef.
Local Transparent Linker_unit.
Local Transparent Linker_varinit.

Lemma link_unit_symm: forall (i1 i2:unit) , link i1 i2 = link i2 i1.
Proof.
  intros. cbn. auto.
Qed.

Lemma link_fundef_symm: forall {F} (def1 def2: (AST.fundef F)),
    link_fundef def1 def2 = link_fundef def2 def1.
Proof.
  intros. destruct def1, def2; auto.
  cbn. 
  destruct external_function_eq; destruct external_function_eq; subst; congruence.
Qed.

Lemma link_varinit_symm: forall i1 i2,
    link_varinit i1 i2 = link_varinit i2 i1.
Proof.
  intros. unfold link_varinit.
  destruct (classify_init i1), (classify_init i2); cbn; try congruence.
  destruct zeq; destruct zeq; subst; cbn in *; try congruence.
Qed.

Lemma link_vardef_symm: 
  forall {V} {LV: Linker V}
    (LinkVSymm: forall (i1 i2: V), link i1 i2 = link i2 i1)
    (v1 v2: globvar V),
    link_vardef v1 v2 = link_vardef v2 v1.
Proof.
  intros. destruct v1,v2; cbn.
  unfold link_vardef; cbn.
  rewrite LinkVSymm.
  destruct (link gvar_info0 gvar_info); try congruence.
  rewrite link_varinit_symm. 
  destruct (link_varinit gvar_init0 gvar_init); try congruence.
  destruct gvar_readonly, gvar_readonly0, gvar_volatile, gvar_volatile0; 
    cbn; try congruence.
Qed.

Lemma link_def_symm: forall {F V} {LV: Linker V}
                       (LinkVSymm: forall (i1 i2: V), link i1 i2 = link i2 i1)
                          (def1 def2: (globdef (AST.fundef F) V)),
    link_def def1 def2 = link_def def2 def1.
Proof.
  intros.
  destruct def1, def2; auto.
  - cbn. 
    rewrite link_fundef_symm. auto.
  - cbn.
    rewrite link_vardef_symm. auto. auto.
Qed.

(* SACC
Lemma link_option_symm: forall {F V} {LV: Linker V} 
                          (LinkVSymm: forall (i1 i2: V), link i1 i2 = link i2 i1)
                          (def1 def2: option (globdef (AST.fundef F) V)),
    link_option def1 def2 = link_option def2 def1.
Proof.
  intros.
  unfold link_option. destruct def1, def2; auto.
  cbn.
  erewrite link_def_symm; eauto.
Qed.
*)

Lemma link_prog_merge_symm: 
  forall {F V} {LV: Linker V} 
    (LinkVSymm: forall (i1 i2: V), link i1 i2 = link i2 i1)
    (a b:option (globdef (AST.fundef F) V)), 
    link_prog_merge a b = link_prog_merge b a.
Proof.
  intros. unfold link_prog_merge.
  destruct a, b; auto.
  apply link_def_symm. auto.
Qed.


Lemma link_prog_check_link_exists: 
  forall {F V} {LF: Linker F} {LV: Linker V} (p1 p2: AST.program F V),
  PTree_Properties.for_all (prog_defmap p1) (link_prog_check p1 p2) = true ->
  (forall x d1 d2, (prog_defmap p1)!x = Some d1 ->
              (prog_defmap p2)!x = Some d2 ->
              exists d, link d1 d2 = Some d).
Proof.
  intros F V LF LV p1 p2 CHECK x d1 d2 GE1 GE2.
  rewrite PTree_Properties.for_all_correct in CHECK.
  apply CHECK in GE1.
  unfold link_prog_check in GE1. 
  rewrite GE2 in GE1. destr_in GE1; eauto.
  rewrite andb_true_iff in GE1. destruct GE1; congruence.
Qed.

Lemma link_prog_merge_none: forall {F V} {LF: Linker F} {LV: Linker V},
  @link_prog_merge F V LF LV None None = None.
Proof.
  intros. cbn. auto.
Qed.



Definition def_none_or_ext {F V} (fi:F -> bool) (def: option (globdef F V)) :=
  def = None \/ 
  exists def', def = Some def' /\ is_def_internal fi def' = false.

Definition defs_none_or_ext {F V} {LV: Linker V} 
           (t: PTree.t (globdef (AST.fundef F) V)) ids :=
  forall id, In id ids ->
        def_none_or_ext is_fundef_internal (t ! id).

Lemma defs_none_or_ext_head: 
  forall {F V} {LV: Linker V} (t: PTree.t (globdef (AST.fundef F) V)) id ids,
  defs_none_or_ext t (id :: ids) ->
  def_none_or_ext is_fundef_internal (t!id).
Proof.
  intros. red in H.
  generalize (H _ (in_eq _ _)).
  auto.
Qed.

Lemma defs_none_or_ext_tail: 
  forall {F V} {LV: Linker V} (t: PTree.t (globdef (AST.fundef F) V)) id ids,
  defs_none_or_ext t (id :: ids) ->
  defs_none_or_ext t ids.
Proof.
  intros. red in H.
  red. intros.
  eapply H; eauto. 
  apply in_cons. auto.
Qed.


Definition def_some_int {F V} (fi:F -> bool) (def: option (globdef F V)) :=
  exists def', def = Some def' /\ is_def_internal fi def' = true.

Definition defs_some_int {F V} {LV: Linker V} 
           (t: PTree.t (globdef (AST.fundef F) V)) ids :=
  forall id, In id ids ->
        def_some_int is_fundef_internal (t ! id).
  

Lemma link_prog_merge_defs_none_or_ext: 
  forall {F V} {LV: Linker V} d1 d2 (d: globdef (AST.fundef F) V),
    def_none_or_ext is_fundef_internal d1 ->
    def_none_or_ext is_fundef_internal d2 ->
    link_prog_merge d1 d2 = Some d ->
    is_def_internal is_fundef_internal d = false.
Proof.
  intros F V LV d1 d2 d DE1 DE2 LINK.
  unfold link_prog_merge in LINK. 
  destr_in LINK; destr_in LINK; subst.
  - red in DE1. destruct DE1; try congruence.
    destruct H as (def1' & EQ & DE1'). inv EQ.
    red in DE2. destruct DE2; try congruence.
    destruct H as (def2' & EQ & DE2'). inv EQ.
    cbn in LINK.
    eapply (link_external_defs def1' def2'); eauto.
  - inv LINK. 
    red in DE1. destruct DE1; try congruence.
    destruct H as (def1' & EQ & DE1'). inv EQ.
    auto.
  - red in DE2. destruct DE2; try congruence.
    destruct H as (def2' & EQ & DE2'). inv EQ.
    auto.
Qed.

Lemma link_prog_merge_def_internal:
  forall {F V} {LV: Linker V} d1 d2 (d: globdef (AST.fundef F) V),
    is_def_internal is_fundef_internal d1 = true ->
    link_prog_merge (Some d1) d2 = Some d ->
    is_def_internal is_fundef_internal d = true.
Proof.
  intros F V LV d1 d2 d DI1 LINK.
  cbn in LINK. destruct d2.
  - eapply link_def_pres_int_def; eauto.
  - inv LINK. auto.
Qed.

(* Lemma link_merge_pres_internal: *)
(*   forall (F V : Type) (LV : Linker V) *)
(*     (def2 : option (option (globdef (AST.fundef F) V))) *)
(*     (def1 def : option (globdef (AST.fundef F) V)), *)
(*   is_def_internal is_fundef_internal def1 = true -> *)
(*   link_prog_merge (Some def1) def2 = Some def ->  *)
(*   is_def_internal is_fundef_internal def = true. *)
(* Proof. *)
(*   intros. *)
(*   assert (def_eq def def1). *)
(*   { eapply link_merge_internal_external_defs; eauto. } *)
(*   erewrite def_eq_pres_internal; eauto. *)
(* Qed. *)
