Require Import Coqlib List.

Section ASSOC.
  Variables A B: Type.

  Variable Aeq: forall (a1 a2: A), {a1=a2}+{a1<>a2}.

  Fixpoint get_assoc (l: list (A*B)) (b: A) : option B :=
    match l with
      nil => None
    | (k,v)::r => if Aeq k b then Some v else get_assoc r b
    end.

  Lemma get_assoc_in:
    forall (l: list (A*B)) b r,
      get_assoc l b = Some r ->
      In (b,r) l.
  Proof.
    induction l; simpl; intros; eauto. inv H.
    repeat destr_in H. simpl. right.
    eauto.
  Qed.

  Lemma in_lnr_get_assoc:
    forall l b f,
      list_norepet (map fst l) ->
      In (b,f) l ->
      get_assoc l b = Some f.
  Proof.
    induction l; intros b f LNR IN; simpl in *. easy.
    destruct IN. subst. destr.
    inv LNR. erewrite IHl; eauto.
    repeat destr. subst. simpl in *.
    exfalso; apply H2; apply in_map_iff.
    exists (b,f); split; auto.
  Qed.

End ASSOC.