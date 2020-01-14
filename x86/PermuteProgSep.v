(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 12th, 2019 *)
(* *******************  *)

(** * Separate compilation for permutation of definitions *)
Require Import Coqlib Errors Maps.
Require Import Integers Floats AST.
Require Import Values Memory Events Linking OrderedLinking.
Require Import Permutation.
Require Import PermuteProgproof.

Local Transparent Linker_prog_ordered.

(** Commutativity between permutation and linking *)
Instance TransfPermuteOrderedLink1 {F V} {LV: Linker V}
  : @TransfLink _ _ (Linker_prog (fundef F) V) (Linker_prog_ordered F V) match_prog.
Proof.
  Local Transparent Linker_prog.
  red. unfold match_prog. cbn. 
  intros until p.
  intros LINK (PERM1 & MAINEQ1 & PUBEQ1) (PERM2 & MAINEQ2 & PUBEQ2).
  generalize LINK. intros LINK'.
  unfold link_prog in LINK.
  destr_in LINK. inv LINK. cbn.
  repeat (rewrite andb_true_iff in Heqb). 
  destruct Heqb as (((MAINEQ & NORPT1) & NORPT2) & CHECK).
  destruct ident_eq; try discriminate.
  destruct list_norepet_dec; try discriminate.
  destruct list_norepet_dec; try discriminate.
  unfold link_prog_ordered.
  assert (prog_main tp1 = prog_main tp2) as MAINEQ3 by congruence.
  rewrite MAINEQ3.
  destruct ident_eq; try congruence. cbn.
  assert (list_norepet (map fst (prog_defs tp1))) as NORPT3.
  { eapply Permutation_list_norepet_map; eauto. }
  destruct list_norepet_dec; try contradiction. cbn.
  assert (list_norepet (map fst (prog_defs tp2))) as NORPT4.
  { eapply Permutation_list_norepet_map; eauto. }
  destruct list_norepet_dec; try contradiction. cbn.  
  edestruct (@extract_defs_exists F V _ tp1 tp2) as (defs1 & t1 & EXTR); eauto.
  eapply prog_linkable_permutation; eauto.
  rewrite EXTR. 
  eexists; split; eauto.
  cbn.
  repeat (split; auto).
  generalize (PTree_extract_elements_permutation _ _ _ _ EXTR).
  intros PERM3. 
  apply Permutation_trans with (defs1 ++ PTree.elements t1).
  eapply Permutation_trans; [| exact PERM3].
  unfold prog_option_defmap.
  eapply PTree_combine_permutation; eauto.
  apply Permutation_app_comm.
  congruence.
  congruence.
Qed.

Instance TransfPermuteOrderedLink2 {F V} {LV: Linker V}
  : @TransfLink _ _ (Linker_prog_ordered F V) (Linker_prog (fundef F) V) match_prog.
Proof.
Admitted.
