(* *******************  *)
(* Author: Pierre Wilke *)
(* Author: Xiangzhe Xu  *)
(* Date:   Feb 4, 2020  *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import RelocBingen.
Require Import RelocProgram RelocProgSemantics1 RelocProgSemantics2.
Import ListNotations.
Require AsmFacts.
Require SymbolString.

Lemma instr_eq_size_eq: forall i1 i2,
    RelocBinDecode.instr_eq i1 i2 -> instr_size i1 = instr_size i2.
Proof.
  intros.
  destruct i1; try (inv H; cbn; auto).
  destruct i2; inv H; cbn; auto.
  destruct i2; inv H; cbn; auto.
  destruct i2; inv H; cbn; auto.
  destruct i2; inv H; cbn; auto.
  destruct i2; inv H; cbn; auto.
  destruct i2; inv H; cbn; auto.
  destruct i2; inv H; cbn; auto.
Qed.


Lemma list_has_tail: forall {A:Type} (l:list A) n,
    (length l = 1 + n)%nat
    ->exists tail prefix, l = prefix++[tail].
Proof.
  intros A l n.
  revert l.
  induction n.
  intros l H.
  destruct l; simpl in H; inversion H.
  exists a. exists [].
  simpl.
  generalize (length_zero_iff_nil l).
  intros H0. destruct H0.
  rewrite(H0 H1). auto.
  intros l H.
  replace (1 + Datatypes.S n)%nat with (Datatypes.S (1+n)%nat)%nat in H by omega.
  destruct l; simpl in H; inversion H.
  generalize (IHn l H1).
  intros [tail [prefix HHasTail]].
  exists tail. exists (a::prefix).
  rewrite HHasTail. simpl. auto.
Qed.


Definition match_prog p tp :=
  transf_program false p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program false p = OK tp -> match_prog p tp.
Proof.
  intros. subst. red.
  auto.
Qed.

Fixpoint instr_size_acc code: Z :=
  match code with
  |nil => 0
  |i::tail => instr_size i + instr_size_acc tail
  end.

Lemma instr_size_app: forall n a b,
    length a = n
    -> instr_size_acc (a++b) = instr_size_acc a + instr_size_acc b.
Proof.
  induction n.
  (* base case *)
  intros a b H.
  generalize (length_zero_iff_nil a).
  intros (H1 & H2).
  generalize(H1 H).
  intros H0.
  rewrite H0.
  simpl. auto.
  
  intros a b HLa.
  generalize (list_has_tail _ _ HLa).
  intros [tail [prefix Ha]].
  rewrite Ha.
  cut(length prefix = n).
  intros HLPrefix.
  generalize(IHn prefix ([tail]++b) HLPrefix).
  intros HApp.
  rewrite <- app_assoc.
  rewrite HApp.
  generalize(IHn prefix [tail] HLPrefix).
  intros HPrefixTail.
  rewrite HPrefixTail.
  assert(HTailB: instr_size_acc ([tail]++b) = instr_size_acc [tail] + instr_size_acc b). {
    unfold instr_size_acc.
    simpl. omega.
  }
  rewrite HTailB. omega.
  rewrite Ha in HLa.
  rewrite app_length in HLa.
  simpl in HLa.
  omega.
Qed.

Fixpoint transl_code_spec code bytes ofs rtbl_ofs_map: Prop :=
  match code, bytes  with
  |nil, nil => True 
  |h::t, _ =>
   exists h' t', RelocBinDecode.fmc_instr_decode rtbl_ofs_map ofs bytes = OK (h',t')
                 /\  RelocBinDecode.instr_eq h h'
                 /\ transl_code_spec t t' (ofs+instr_size h) rtbl_ofs_map
  |_, _ => False
  end.


Lemma prefix_success: forall rtbl a b ofs r z l,
    fold_left (acc_instrs rtbl false) (a ++ [b]) (OK (ofs, r)) = OK (z, l)
    ->exists z' l', fold_left (acc_instrs rtbl false) a  (OK (ofs, r)) = OK (z', l').
Proof.
  intros rtbl a b ofs r z l HFoldPrefix.
  rewrite fold_left_app in HFoldPrefix.
  inversion HFoldPrefix.
  monadInv H0.
  destruct x.
  exists z0. exists l0.
  unfold acc_instrs.
  auto.
Qed.  

Lemma fold_spec_length: forall n rtbl code ofs r z l,
    length code = n ->
    fold_left (acc_instrs rtbl false) (code) (OK (ofs, r)) = OK (z, l)
    -> z = ofs + instr_size_acc code.
Proof.
  induction n.
  intros rtbl code ofs r z l H H0.
  generalize (length_zero_iff_nil code).
  intros (HLCode & HNCode).
  generalize(HLCode H).
  intros HCode.
  subst code.
  simpl.
  simpl in H0. inversion H0.
  omega.
  
  intros rtbl code ofs r z l HLCode HFoldAll.
  generalize (list_has_tail code n HLCode).
  intros [tail [prefix HCode]].
  rewrite HCode in HFoldAll.
  generalize (prefix_success _ _ _ _ _ _ _ HFoldAll).
  intros [z' [l' HFoldPrefix]].
  assert(HLPrefix: length prefix = n). {
    rewrite HCode in HLCode.
    rewrite app_length in HLCode.
    simpl in HLCode.
    omega.
  }
  generalize(IHn rtbl prefix _ _ _ _ HLPrefix HFoldPrefix).
  intros Hz'.
  rewrite fold_left_app in HFoldAll.
  rewrite HFoldPrefix in HFoldAll.
  simpl in HFoldAll.
  monadInv HFoldAll.
  rewrite (instr_size_app (length prefix)).
  simpl.
  omega.
  auto.
Qed.

Lemma decode_int_app: forall l bytes x,
    RelocBinDecode.decode_int_n bytes 4 = OK x
    ->RelocBinDecode.decode_int_n (bytes++l) 4 = OK x.
Proof.
  intros l bytes x HDecode.
  unfold RelocBinDecode.decode_int_n.
  unfold RelocBinDecode.decode_int_n in HDecode.
  monadInv HDecode.
  simpl in EQ.
  do 4(destruct bytes; inversion EQ).
  simpl.
  destruct bytes;
  simpl; destruct l; simpl; inversion H3; auto.
Qed.

Lemma decode_int_1_app: forall l bytes x,
    RelocBinDecode.decode_int_n bytes 1 = OK x
    ->RelocBinDecode.decode_int_n (bytes++l) 1 = OK x.
Proof.
  intros l bytes x HDecode.
  unfold RelocBinDecode.decode_int_n.
  unfold RelocBinDecode.decode_int_n in HDecode.
  monadInv HDecode.
  simpl in EQ.
  destruct bytes; inversion EQ.
  simpl.
  destruct bytes;
  simpl; destruct l; simpl; inversion H0; auto.
Qed.
  
Lemma remove_first_n_app: forall {A} (bytes:list A) n x l,
    RelocBinDecode.remove_first_n bytes n = OK x
    ->RelocBinDecode.remove_first_n (bytes++l) n = OK(x++l).
Proof.
  intros A bytes n x l HDecode.
  revert dependent bytes.
  induction n.
  simpl. intros bytes HDecode. inversion HDecode. auto.
  intros bytes HDecode.
  simpl in HDecode.
  destruct bytes; inversion HDecode.
  generalize(IHn _ HDecode).
  simpl. auto.
Qed.




Lemma decode_0f_app: forall bytes h t l,
    RelocBinDecode.decode_0f bytes = OK(h, t)
    ->RelocBinDecode.decode_0f (bytes++l) = OK(h, t++l).
Proof.
  intros bytes h t l HDecode.
  unfold RelocBinDecode.decode_0f in HDecode.
  unfold RelocBinDecode.decode_0f.
  monadInv HDecode.
  cbn [RelocBinDecode.get_n].
  cbn [RelocBinDecode.get_n] in EQ.
  destruct bytes; inversion EQ.
  simpl.
  simpl in EQ0.
  destruct Byte.eq_dec.
  (* imull *)
  unfold RelocBinDecode.decode_imull_rr in EQ0.
  monadInv EQ0.
  unfold RelocBinDecode.decode_imull_rr.
  simpl in EQ1. destruct bytes; inversion EQ1.
  simpl. rewrite EQ0.
  simpl. simpl in EQ2.
  inversion EQ2. auto.
  (* jcc *)
  unfold RelocBinDecode.decode_jcc_rel in EQ0.
  simpl in EQ0.
  monadInv EQ0.
  do 4 (destruct bytes; inversion EQ0).
  unfold RelocBinDecode.decode_jcc_rel.
  simpl. unfold RelocBinDecode.decode_int_n.
  simpl.
  rewrite<- H4.
  unfold RelocBinDecode.decode_int_n in EQ1.
  simpl in EQ1.
  destruct bytes.
  simpl in EQ1. simpl.
  destruct l; simpl;
  rewrite <- H0.
  repeat (destruct Byte.eq_dec; try(inversion EQ3; rewrite<- H6;
                                    rewrite <- H4; simpl; inversion EQ1; auto)).
  repeat (destruct Byte.eq_dec; try(inversion EQ3; rewrite<- H6;
                                    rewrite <- H4; simpl; inversion EQ1; auto)).
  simpl in EQ1. simpl.
  rewrite <- H0.
  repeat (destruct Byte.eq_dec; try(inversion EQ3; rewrite<- H6;
                                    rewrite <- H4; simpl; inversion EQ1; auto)).
Qed.

Lemma decode_addrmode_size_app: forall bytes x l,
    RelocBinDecode.decode_addrmode_size bytes = OK x
    -> RelocBinDecode.decode_addrmode_size (bytes++l) = OK x.
Proof.
  intros bytes x l HDecode.
  unfold RelocBinDecode.decode_addrmode_size.
  unfold RelocBinDecode.decode_addrmode_size in HDecode.
  destruct bytes;inversion HDecode.
  simpl.
  auto.
Qed.

Lemma addrmode_SIB_parse_base_app: forall mode base bs mc x l,
    RelocBinDecode.addrmode_SIB_parse_base mode base bs mc = OK x ->
    RelocBinDecode.addrmode_SIB_parse_base mode base bs (mc++l) = OK x.
Proof.
  intros mode base bs mc x l HDecode.
  unfold RelocBinDecode.addrmode_SIB_parse_base.
  unfold RelocBinDecode.addrmode_SIB_parse_base in HDecode.
  destruct Byte.eq_dec.
  destruct Byte.eq_dec.
  monadInv HDecode.
  rewrite (decode_int_app l _ _ EQ). simpl. auto.
  destruct Byte.eq_dec.
  monadInv HDecode.
  rewrite(decode_int_1_app l _ _ EQ). simpl. auto.
  destruct Byte.eq_dec.
  monadInv HDecode.
  rewrite (decode_int_app l _ _ EQ). simpl. auto.
  inversion HDecode.
  destruct Byte.eq_dec.
  auto.
  destruct Byte.eq_dec.
  monadInv HDecode.
  rewrite(decode_int_1_app l _ _ EQ). simpl; auto.
  destruct Byte.eq_dec; inversion HDecode.
  monadInv HDecode.
  rewrite(decode_int_app l _ _ EQ). simpl. auto.
Qed.

Lemma addrmode_parse_SIB_app:forall rtbl ofs x1 x2 bytes a l1 l,
    RelocBinDecode.addrmode_parse_SIB rtbl ofs x1 x2 bytes = OK (a,l1)->
    RelocBinDecode.addrmode_parse_SIB rtbl ofs x1 x2 (bytes++l) = OK (a, l1++l).
Proof.
  intros rtbl ofs x1 x2 bytes a l1 l HDecode.
  unfold RelocBinDecode.addrmode_parse_SIB.
  unfold RelocBinDecode.addrmode_parse_SIB in HDecode.
  monadInv HDecode.
  rewrite EQ0. simpl.
  rewrite EQ. simpl.
  rewrite EQ1. simpl.
  rewrite (addrmode_SIB_parse_base_app _ _ _ _ _ l EQ2).
  simpl.
  destruct (RelocBinDecode.find_ofs_in_rtbl rtbl ofs).
  destruct Byte.eq_dec.
  destruct Byte.eq_dec.
  monadInv EQ4.
  simpl in EQ3.
  do 4 (destruct bytes; inversion EQ3).
  simpl.
  auto.
  inversion EQ4. auto.
  inversion EQ4. auto.
  destruct Byte.eq_dec.
  destruct Byte.eq_dec.
  monadInv EQ4.
  simpl in EQ3.
  do 4 (destruct bytes; inversion EQ3).
  simpl.
  auto.
  1-2: inversion EQ4; auto.
Qed.

Lemma decode_addrmode_app:forall rtbl_ofs_map ofs bytes p l l1,
    RelocBinDecode.decode_addrmode rtbl_ofs_map ofs bytes = OK (p, l)
    ->RelocBinDecode.decode_addrmode rtbl_ofs_map ofs (bytes++l1) = OK (p, l++l1).
Proof.
  intros rtbl_ofs_map ofs bytes p l l1 HDecode.
  unfold  RelocBinDecode.decode_addrmode.
  unfold  RelocBinDecode.decode_addrmode in HDecode.
  destruct bytes; inversion HDecode.
  monadInv HDecode.
  simpl.
  rewrite EQ.
  simpl.
  destruct Byte.eq_dec.
  monadInv EQ0.
  rewrite EQ1.
  simpl. destruct Byte.eq_dec.
  monadInv EQ2.
  simpl in EQ2.
  destruct bytes; inversion EQ2. simpl.
  inversion EQ0.
  destruct x3.
  rewrite (addrmode_parse_SIB_app _ _ _ _ _ _ _ l1 EQ3).
  simpl. auto.
  destruct Byte.eq_dec.
  monadInv EQ2.
  rewrite(decode_int_app l1 _ _ EQ0).
  simpl.
  destruct(RelocBinDecode.find_ofs_in_rtbl rtbl_ofs_map ofs).
  monadInv EQ3.
  simpl in EQ2.
  do 4 (destruct bytes; inversion EQ2).
  simpl.
  auto.
  monadInv EQ3.
  simpl in EQ2.
  do 4(destruct bytes; inversion EQ2).
  simpl.
  auto.
  inversion EQ2. auto.
  destruct Byte.eq_dec.
  monadInv EQ0.
  rewrite EQ1.
  simpl.
  destruct Byte.eq_dec.
  monadInv EQ2.
  simpl in EQ2.
  destruct bytes; inversion EQ2. simpl.
  destruct x3.
  inversion EQ3.
  simpl in EQ0.
  inversion EQ0.
  rewrite(addrmode_parse_SIB_app _ _ _ _ _ _ _ l1 EQ3).
  simpl.
  simpl in EQ4.
  destruct l0;inversion EQ4. simpl. auto.
  monadInv EQ2.
  rewrite (decode_int_1_app l1 _ _ EQ0).
  simpl.
  simpl in EQ2.
  destruct bytes; inversion EQ2.
  simpl.
  auto.

  destruct Byte.eq_dec.
  monadInv EQ0.
  rewrite EQ1. simpl.
  destruct Byte.eq_dec.
  monadInv EQ2.
  simpl in EQ2.
  destruct bytes; inversion EQ2.
  simpl.
  simpl in EQ0. inversion EQ0.
  destruct x3.
  rewrite(addrmode_parse_SIB_app _ _ _ _ _ _ _ l1 EQ3).
  simpl.
  simpl in EQ4.
  do 4 (destruct l0;inversion EQ4).
  simpl.
  auto.
  monadInv EQ2.
  rewrite(decode_int_app l1 _ _ EQ0).
  simpl.
  destruct (RelocBinDecode.find_ofs_in_rtbl rtbl_ofs_map ofs).
  1-2: monadInv EQ3;
    simpl in EQ2;
    do 4 (destruct bytes; inversion EQ2);
    simpl;
    auto.
  inversion EQ0.
Qed.


Lemma decode_81_app: forall bytes h t l,
    RelocBinDecode.decode_81 bytes = OK (h, t)
    ->RelocBinDecode.decode_81 (bytes++l) = OK (h, t++l).
Proof.
  intros bytes h t l HDecode.
  unfold RelocBinDecode.decode_81 in HDecode.
  simpl in HDecode.
  unfold RelocBinDecode.decode_81. simpl.
  destruct bytes; inversion HDecode.
  simpl in HDecode.
  simpl.
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_cmpl_ri in H0.
  unfold RelocBinDecode.decode_cmpl_ri.
  monadInv H0.
  simpl.
  simpl in EQ1. simpl in EQ. inversion EQ.
  rewrite EQ1.
  simpl.
  simpl in EQ0. inversion EQ0.
  rewrite(decode_int_app l _ _ EQ2).
  simpl.
  unfold RelocBinDecode.remove_first_n in EQ3.
  do 4 (destruct bytes; inversion EQ3).
  rewrite<- H1. simpl. rewrite H5. auto.

  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_addl_ri.
  unfold RelocBinDecode.decode_addl_ri in H0.
  simpl in H0.
  monadInv H0.
  simpl.
  rewrite EQ.
  simpl.
  rewrite(decode_int_app l _ _ EQ1).
  simpl.
  do 4 (destruct bytes; inversion EQ0).
  simpl. auto.

  destruct Byte.eq_dec;inversion H0.
  unfold RelocBinDecode.decode_subl_ri in HDecode.
  unfold RelocBinDecode.decode_subl_ri.
  monadInv HDecode.
  simpl.
  simpl in EQ1.
  simpl in EQ; inversion EQ.
  rewrite EQ1.
  simpl.
  simpl in EQ0; inversion EQ0.
  rewrite(decode_int_app l _ _ EQ2).
  simpl.
  simpl in EQ3.
  do 4 (destruct bytes; inversion EQ3).
  rewrite <- H3.
  simpl.
  rewrite H7. auto.
Qed.

Lemma decode_8b_app:forall rtbl_ofs_map ofs bytes h t l,
    RelocBinDecode.decode_8b rtbl_ofs_map ofs bytes = OK(h,t)
    -> RelocBinDecode.decode_8b rtbl_ofs_map ofs (bytes ++l )
       = OK(h, t++l).
Proof.
  intros rtbl_ofs_map ofs bytes h t l HDecode.
  unfold RelocBinDecode.decode_8b.
  unfold RelocBinDecode.decode_8b in HDecode.
  monadInv HDecode.
  simpl in *.
  destruct bytes; inversion EQ.
  simpl.
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_mov_rr.
  simpl.
  unfold RelocBinDecode.decode_mov_rr in EQ0.
  monadInv EQ0.
  inversion EQ1.
  rewrite EQ0. simpl.
  inversion EQ2. auto.

  unfold RelocBinDecode.decode_movl_rm.
  unfold RelocBinDecode.decode_movl_rm in EQ0.
  monadInv EQ0.
  setoid_rewrite (decode_addrmode_size_app _ _ l EQ1).
  simpl.
  destruct x1.
  setoid_rewrite (decode_addrmode_app _ _ _ _ _ l EQ0).
  simpl. auto.
Qed.


  

Lemma decode_app:forall x rtbl_ofs_map  ofs bytes h t,
    RelocBinDecode.fmc_instr_decode rtbl_ofs_map  ofs bytes =OK (h, t)                 
    -> RelocBinDecode.fmc_instr_decode rtbl_ofs_map  ofs (bytes++x) = OK (h, t++x).
Proof.
  intros x rtbl_ofs_map  ofs bytes h t HDecode.
  unfold RelocBinDecode.fmc_instr_decode in HDecode.
  inversion HDecode.
  destruct bytes;inversion H0.
  unfold RelocBinDecode.fmc_instr_decode.
  simpl.
  (* nop *)
  destruct Byte.eq_dec; inversion HDecode; auto.
  (* jmp *)
  destruct Byte.eq_dec.
  unfold  RelocBinDecode.decode_jmp_l_rel.
  unfold  RelocBinDecode.decode_jmp_l_rel in HDecode.
  monadInv HDecode.
  rewrite(decode_int_app x bytes x0).
  rewrite(remove_first_n_app bytes 4 t x).
  simpl.
  1-3: auto.
  (* decode_0f *)
  destruct Byte.eq_dec.
  rewrite(decode_0f_app bytes h t x).
  1-2: auto.
  (* call *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_call.
  unfold RelocBinDecode.decode_call in HDecode.
  monadInv HDecode.
  rewrite (decode_int_app x bytes x0 EQ).
  simpl.
  destruct RelocBinDecode.find_ofs_in_rtbl; inversion EQ0.
  (* destruct RelocBinDecode.get_nth_symbol; inversion H3. *)
  monadInv H3.
  do 4 (destruct bytes;inversion EQ1).
  simpl. auto.
  (* leal *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_leal.
  unfold RelocBinDecode.decode_leal in HDecode.
  monadInv HDecode.
  rewrite (decode_addrmode_size_app _ _ x EQ).
  simpl.
  destruct x1.
  rewrite(decode_addrmode_app _ _ _ _ _ x EQ1).
  simpl. auto.
  (* xorl *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_xorl_r.
  unfold RelocBinDecode.decode_xorl_r in H2.
  monadInv H2.
  unfold RelocBinDecode.get_n in EQ.
  destruct bytes; inversion EQ.
  simpl.
  simpl in EQ1.
  rewrite EQ1.
  simpl.
  simpl in EQ0.
  inversion EQ0.
  auto.
  (* decode_81 *)
  destruct Byte.eq_dec.
  rewrite(decode_81_app _ _ _ x H2).
  auto.
  (* decode_subl_rr *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_subl_rr.
  unfold RelocBinDecode.decode_subl_rr in HDecode.
  simpl in HDecode.
  monadInv HDecode.
  simpl.
  destruct bytes; inversion EQ.
  simpl.
  rewrite EQ1.
  rewrite EQ0.
  simpl.
  inversion EQ2. auto.
  (* decode_movl_ri *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_movl_ri.
  unfold RelocBinDecode.decode_movl_ri in HDecode; simpl in HDecode.
  monadInv HDecode.
  simpl.
  rewrite EQ.
  rewrite(decode_int_app x _ _ EQ1).
  simpl.
  do 4 (destruct bytes; inversion EQ0).
  simpl. auto.
  (* decode_8b *)
  destruct Byte.eq_dec.
  rewrite(decode_8b_app _ _ _ _ _ x H2).
  auto.
  (* decode_movl_mr *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_movl_mr.
  unfold RelocBinDecode.decode_movl_mr in H2.
  monadInv H2.
  rewrite(decode_addrmode_size_app  _ _ x EQ).
  simpl.
  destruct x1.
  rewrite(decode_addrmode_app _ _ _ _ _ x EQ1).
  simpl. auto.

  (* decode_testl_rr *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_testl_rr.
  unfold RelocBinDecode.decode_testl_rr in HDecode.
  monadInv HDecode.
  inversion EQ. destruct bytes; inversion H3.
  simpl.
  rewrite EQ1.
  simpl. inversion EQ0. auto.
  (* Pret *)
  destruct Byte.eq_dec.
  inversion HDecode. auto.
  (* imull_ri *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_imull_ri.
  unfold RelocBinDecode.decode_imull_ri in HDecode.
  monadInv HDecode.
  inversion EQ.
  destruct bytes;inversion H3.
  simpl.
  simpl in EQ1. rewrite EQ1.
  simpl.
  inversion EQ0.
  rewrite (decode_int_app x _ _ EQ2).
  simpl.
  inversion EQ3.
  rewrite<- H5.
  do 4 (destruct bytes;inversion H6).
  simpl.
  auto.
  (* cmpl_rr *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_cmpl_rr.
  unfold RelocBinDecode.decode_cmpl_rr in HDecode.
  monadInv HDecode.
  inversion EQ. destruct bytes; inversion H3.
  simpl.
  rewrite EQ1. simpl.
  inversion EQ0.
  auto.
  (* Pcltd *)
  destruct Byte.eq_dec.
  inversion HDecode. auto.
  (* idivl *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_idivl.
  unfold RelocBinDecode.decode_idivl in HDecode.
  monadInv HDecode.
  inversion EQ. destruct bytes; inversion H3.
  simpl.
  simpl in EQ1. rewrite EQ1.
  simpl. inversion EQ0. auto.
  (* sall *)
  destruct Byte.eq_dec.
  unfold RelocBinDecode.decode_sall_ri.
  unfold RelocBinDecode.decode_sall_ri in HDecode.
  simpl in HDecode.
  monadInv HDecode.
  destruct bytes; inversion EQ.
  simpl.
  rewrite EQ1. simpl.
  inversion EQ0.
  unfold RelocBinDecode.decode_int_n in EQ2.
  monadInv EQ2.
  unfold RelocBinDecode.decode_int_n.
  destruct x2;inversion EQ3.
  simpl.
  inversion EQ4.
  monadInv H4.
  destruct t.
  destruct x.
  simpl. inversion EQ2. auto.
  simpl. inversion EQ2. auto.
  simpl. inversion EQ2. auto.
  inversion HDecode.
Qed.



Lemma transl_code_spec_inc: forall code ofs rtbl_ofs_map bytes instr x,
    (* length code = n -> *)
    transl_code_spec code bytes ofs rtbl_ofs_map
    -> encode_instr rtbl_ofs_map false (ofs+(instr_size_acc code)) instr = OK x
    -> transl_code_spec (code++[instr]) (bytes++x) ofs rtbl_ofs_map.
Proof.
  induction code as [|i code].
  - intros ofs rtbl_ofs_map  bytes instr x TL EN.
    cbn.
    unfold instr_size_acc in EN. rewrite Z.add_0_r in EN.
    cbn in TL. destruct bytes; try contradiction. cbn.
    generalize (RelocBinDecode.encode_decode_instr_refl _ _ _ _ nil EN).
    rewrite app_nil_r.
    intros (i' & DE & EQ).
    exists i', nil. split; auto.
  - intros ofs rtbl_ofs_map bytes instr x TL EN.
    cbn in TL.
    destruct TL as (h' & t' & DE & EQ & TL).
    cbn in EN. rewrite Z.add_assoc in EN.
    cbn.
    generalize (IHcode _ _ _ _ _ TL EN).
    intros TL'.
    exists h', (t' ++ x).
    split; auto.
    generalize(decode_app x _ _ _ _ _ DE).
    auto.
Qed.

Lemma transl_init_data_size:
  forall rmap o l bl,
    transl_init_data rmap o l = OK bl ->
    Z.of_nat (length bl) = init_data_size l.
Proof.
  unfold transl_init_data. intros. autoinv; simpl; rewrite ? encode_int_length; auto.
  unfold Encode.zero_bytes.
  rewrite map_length. rewrite seq_length. apply nat_of_Z_max.
Qed.

Lemma init_data_list_size_rev:
  forall l,
    init_data_list_size (rev l) = init_data_list_size l.
Proof.
  induction l; simpl; intros; eauto.
  rewrite LocalLib.init_data_list_size_app. simpl. omega.
Qed.

Lemma transl_init_data_list_size:
  forall rmap l bl,
    transl_init_data_list rmap l = OK bl ->
    Z.of_nat (length bl) = init_data_list_size l.
Proof.
  unfold transl_init_data_list. intros. autoinv.
  rewrite <- fold_left_rev_right in EQ.
  rewrite rev_length.
  revert EQ.
  rewrite <- init_data_list_size_rev.
  generalize (rev l) z l0. clear.
  induction l; simpl; intros; eauto.
  inv EQ. reflexivity.
  unfold acc_init_data at 1 in EQ. autoinv.
  apply IHl in EQ0. rewrite <- EQ0.
  rewrite app_length, rev_length.
  rewrite Nat2Z.inj_add.
  erewrite <- transl_init_data_size; eauto.
Qed.



Lemma encode_int32_size: forall x,
    (length(Encode.encode_int32 x) = 4)%nat.
Proof.
  intros x.
  unfold Encode.encode_int32.
  unfold encode_int.
  unfold bytes_of_int.
  auto.
Qed.


Lemma encode_addrmode_size_refl: forall rmap o i a rd x,
    encode_addrmode rmap o i a rd = OK x
    -> addrmode_size a = Z.of_nat (length x).
Proof.
  Transparent addrmode_size.
  intros rmap o i a rd x HEncode.
  unfold encode_addrmode in HEncode.
  destruct a.
  monadInv HEncode.
  destruct const.
  destruct (Reloctablesgen.instr_reloc_offset i).
  destruct get_instr_reloc_addend'; inversion EQ1.
  unfold encode_addrmode_aux in EQ.
  destruct ofs.
  destruct base.
  monadInv EQ. destruct p.
  destruct ireg_eq; inversion EQ2.
  monadInv H1.
  simpl.
  rewrite encode_int32_size. simpl.
  unfold addrmode_size.
  unfold addrmode_size_aux. omega.
  
  monadInv EQ. destruct p.
  destruct ireg_eq; inversion EQ2.
  monadInv H1.
  simpl. unfold addrmode_size. simpl.
  rewrite encode_int32_size.
  simpl. omega.

  monadInv EQ. destruct base.
  monadInv EQ2.
  destruct ireg_eq eqn:EQR.
  inversion EQ3.
  simpl.
  rewrite encode_int32_size.
  simpl. unfold addrmode_size.
  simpl. rewrite EQR. omega.
  inversion EQ3.
  simpl. rewrite encode_int32_size.
  simpl. unfold addrmode_size.
  simpl. rewrite EQR. omega.

  inversion EQ2.
  simpl.
  rewrite encode_int32_size.
  simpl.
  unfold addrmode_size.
  simpl. omega.

  unfold encode_addrmode_aux in EQ.
  monadInv EQ.
  destruct ofs.
  destruct p.
  destruct base.
  destruct ireg_eq; inversion EQ2.
  monadInv EQ2.
  simpl.
  rewrite encode_int32_size.
  simpl. unfold addrmode_size. simpl. omega.

  destruct ireg_eq; inversion EQ2.
  monadInv EQ2.
  simpl. unfold addrmode_size. simpl.
  rewrite encode_int32_size. simpl. omega.

  destruct base.
  monadInv EQ2.
  destruct ireg_eq eqn:EQR. inversion EQ3.
  simpl.
  rewrite encode_int32_size.
  simpl. unfold addrmode_size.
  simpl. rewrite e0. simpl. auto.
  inversion EQ3. simpl.
  rewrite encode_int32_size.
  simpl. unfold addrmode_size. simpl.
  rewrite EQR.
  omega.

  inversion EQ2.
  simpl. rewrite encode_int32_size.
  simpl. unfold addrmode_size. simpl. auto.

  destruct p. destruct i0; inversion EQ1.
  simpl in EQ.
  monadInv EQ. destruct ofs.
  destruct p.
  destruct base.
  destruct ireg_eq; inversion EQ2.
  monadInv H1.
  simpl. rewrite encode_int32_size.
  unfold addrmode_size. simpl. omega.
  unfold addrmode_size. simpl.
  destruct ireg_eq; inversion EQ2.
  monadInv H1. simpl. rewrite encode_int32_size. simpl. auto.

  destruct base.
  monadInv EQ2.
  destruct ireg_eq eqn:EQR.
  1-2: inversion EQ3.
  1-2: simpl.
  1-2: rewrite encode_int32_size.
  1-2: unfold addrmode_size.
  1-2: simpl.
  1-2: rewrite EQR.
  1-2: omega.

  inversion EQ2.
  simpl. rewrite encode_int32_size.
  unfold addrmode_size.
  simpl. omega.
    
Qed.

Lemma encode_instrs_size:
  forall rmap o i bl,
    encode_instr rmap false o i = OK bl ->
    Asm.instr_size i = Z.of_nat (length bl).
Proof.
  unfold encode_instr.
  cbn [negb ready_for_proof negb].
  Transparent Asm.instr_size. Opaque Z.add.
  destruct i eqn:EQI; simpl; intros; autoinv; simpl;auto;try congruence.
  1-3,6,7:rewrite (encode_addrmode_size_refl _ _ _ _ _ _ EQ);
    rewrite Zpos_P_of_succ_nat; omega.
  1-6:inversion H; auto.
  rewrite app_length.
  rewrite encode_int32_size.
  unfold encode_testcond. destruct c; simpl; auto.
Qed.


Lemma code_size_rev:
  forall l, code_size (rev l) = code_size l.
Proof.
  induction l; simpl; intros; eauto.
  rewrite RealAsm.code_size_app. simpl. omega.
Qed.

Lemma transl_code_size:
  forall rmap l bl,
    transl_code rmap false l = OK bl ->
    Z.of_nat (length bl) = code_size l.
Proof.
  unfold transl_code. intros. autoinv.
  rewrite <- fold_left_rev_right in EQ.
  rewrite rev_length.
  revert EQ.
  rewrite <- code_size_rev.
  generalize (rev l) z l0. clear.
  induction l; simpl; intros; eauto.
  inv EQ. reflexivity.
  unfold acc_instrs at 1 in EQ. autoinv.
  apply IHl in EQ0. rewrite <- EQ0.
  rewrite app_length, rev_length.
  rewrite Nat2Z.inj_add.
  erewrite encode_instrs_size; eauto.
Qed.

(* This lemma means the transl_code could preserve the spec 
 * Specifically, if there're two list, code code', having the relation `transl_code_spec` ,
 * where code is list asm, code' is list byte.
 * Then after translation code2 starting from code', we'll get the result 
 * that has `transl_code_spce` relation with (code++code2) 
 *)
Lemma transl_code_spec_prsv: forall code code' code2 l ofs rtbl_ofs_map z n,
    transl_code_spec code (rev code') ofs rtbl_ofs_map
    -> length code2 = n
    -> fold_left (acc_instrs rtbl_ofs_map false) code2 (OK (ofs + (instr_size_acc code), code')) = OK (z, l)
    -> transl_code_spec (code ++ code2) (rev l) ofs rtbl_ofs_map.
Proof.
  intros code code' code2 l ofs rtbl_ofs_map  z n HTransCode.
  revert dependent l.
  revert dependent z.
  revert dependent code2.
  revert dependent n.
  induction n.
  (* base case *)
  intros code2 z l H H0.
  assert(HCode2: code2=[]). {
    apply length_zero_iff_nil.
    auto.
  }
  subst code2.
  simpl in H0.
  inversion H0.
  subst code'.
  replace (code++[]) with code.
  auto.
  rewrite app_nil_r.
  auto.

  intros code2 z l HLCode2 HFoldCode2.
  generalize (list_has_tail code2 n HLCode2).
  intros [tail [prefix HCode2]].
  rewrite HCode2.
  assert(HLPrefix: length prefix = n). {
    rewrite HCode2 in HLCode2.
    rewrite app_length in HLCode2.
    simpl in HLCode2.
    omega.
  }
  rewrite HCode2 in HFoldCode2.
  generalize (prefix_success _ _ _ _ _ _ _ HFoldCode2).
  intros [z' [l' HFoldPrefix]].
  
  generalize (IHn prefix _ _ HLPrefix HFoldPrefix).
  rewrite fold_left_app in HFoldCode2.
  rewrite HFoldPrefix in HFoldCode2.
  generalize (fold_spec_length (length prefix) _ _ _ _ _ _ eq_refl HFoldPrefix).
  intros Hz'.
  rewrite Hz' in HFoldCode2.
  simpl in HFoldCode2.
  monadInv HFoldCode2.
  intros HSpecPrefix.
  assert(HInstrSize: instr_size_acc (code ++ prefix) = instr_size_acc code + instr_size_acc prefix). {
    rewrite (instr_size_app (length code) code prefix eq_refl).
    auto.
  }
  rewrite <- Zplus_assoc in EQ.
  rewrite <- HInstrSize in EQ.
  generalize (transl_code_spec_inc _ _ _ _ _ _ HSpecPrefix EQ).
  rewrite app_assoc.
  intros HResult.
  rewrite rev_app_distr.
  rewrite rev_involutive.
  auto.
Qed.

Lemma decode_encode_refl: forall n rtbl z code l,
    length code = n ->
    fold_left (acc_instrs rtbl false) code (OK (0, [])) = OK (z, l)
    -> transl_code_spec code (rev l) 0 rtbl.
Proof.
  intros n.
  induction n.
  (* n is O *)
  intros prog z code l H H0.
  assert(HCode: code = []). {
    apply length_zero_iff_nil.
    auto.
  }
  subst code.
  simpl in H0.
  inversion H0.
  subst z.
  subst l.
  simpl.
  auto.
  (* n is S n *)
  intros prog z code l HLength HEncode.
  generalize (list_has_tail code _ HLength).
  intros [lastInstr [prefix HTail]].

  rewrite HTail in HEncode.
  generalize (prefix_success _ _ _ _ _ _ _ HEncode).
  intros [z' [l' HEncodePrefix]].

  cut(length prefix = n).
  intros HLengthN.
  generalize (IHn prog z' prefix l' HLengthN HEncodePrefix).
  intros HPrefix.
  rewrite fold_left_app in HEncode.
  rewrite HEncodePrefix in HEncode.
  (* generalize (suffix_success _ _ _ 0 [] z l z' l'  HEncode HEncodePrefix). *)
  (* intros HEncodeSuffix. *)
  (* simpl in Hz'. *)
  (* rewrite Hz' in HEncodeSuffix. *)
  generalize (fold_spec_length (length prefix) _ _ _ _ _ _ eq_refl HEncodePrefix).
  intros Hz'.
  rewrite Hz' in HEncode.
  generalize (transl_code_spec_prsv prefix l' [lastInstr] _ _ _ _  1 HPrefix eq_refl HEncode).
  rewrite HTail.
  auto.
  rewrite HTail in HLength.
  rewrite app_length in HLength.
  simpl in HLength.
  omega.
Qed.


Fixpoint instr_eq_list code1 code2:=
  match code1, code2 with
  |nil, nil => True
  |h::t, h'::t' => RelocBinDecode.instr_eq h h' /\ instr_eq_list t t'
  |_, _ => False
  end.

Lemma instr_eq_list_size_eq: forall c1 c2, 
    instr_eq_list c1 c2 -> code_size c1 = code_size c2.
Proof.
  induction c1 as [|i1 c1].
  - cbn. intros. destr_in H; eauto.
  - cbn. intros. destr_in H; subst; eauto.
    destr_in H.
    apply instr_eq_size_eq in H0.
    cbn. erewrite IHc1; eauto. congruence.
Qed.

(* this is guaranteed by the decoder *)
Axiom instr_eq_bound: forall rd n a, 
    RelocBinDecode.instr_eq (Psall_ri rd n) a -> 0 <= Int.unsigned n < Byte.modulus.

Lemma decode_instrs_append': forall rtbl  fuel ofs t l1 l2 code,
    decode_instrs rtbl fuel ofs t l1 = OK code ->
    decode_instrs rtbl fuel ofs t (l1 ++ l2) = OK (rev l2 ++ code).
Proof.
  induction fuel as [|fuel].
  - (* base case *)
    intros ofs t l1 l2 code DI.
    cbn in DI. destruct t; try congruence. inv DI.
    cbn. rewrite rev_app_distr. auto.
  - 
    intros ofs t l1 l2 code DI.
    cbn in DI. destruct t.
    + inv DI. cbn. rewrite rev_app_distr. auto.
    + monadInv DI. destruct x as (instr, bytes').
      apply (IHfuel _ _ _ l2) in EQ0.
      cbn ["++"] in EQ0.
      unfold decode_instrs. rewrite EQ. cbn.
      exact EQ0.
Qed.

Lemma decode_instrs_append: forall rtbl fuel ofs t l code,
    decode_instrs rtbl  fuel ofs t [] = OK code ->
    decode_instrs rtbl  fuel ofs t l = OK (rev l ++ code).
Proof.
  intros rtbl fuel ofs t l code DI.
  apply (decode_instrs_append' _ _ _ _ _ l) in DI.
  cbn in DI. auto.
Qed.


Lemma spec_decode_ex: forall code ofs l rtbl,
    transl_code_spec code l ofs rtbl ->
    exists fuel code', decode_instrs rtbl fuel ofs l nil = OK code'
             /\ instr_eq_list code code'.
Proof.
  induction code as [|i code].
  - (* base case *)
    intros ofs l rtbl TL.
    cbn in TL. destruct l; try contradiction.
    cbn. exists O, nil. split; auto.
  - intros ofs l rtbl TL.
    cbn in TL.
    destruct TL as (h' & t' & DE & EQ & TL).
    generalize (IHcode _ _ _ TL).
    intros (fuel & code' & DE' & EQ').
    exists (Datatypes.S fuel), (h'::code').
    split.
    cbn. destruct l. cbn in DE. congruence.
    rewrite DE. cbn.
    assert (instr_size i = instr_size h') as IEQ. {
      destruct i;
        simpl in EQ;
        try(rewrite EQ;
            auto);
        try(destruct h';inversion EQ; auto).

      1-2: rewrite H; rewrite H0; auto.
    }      
    rewrite <- IEQ.
    generalize (decode_instrs_append _ _ _ _ [h'] _ DE').
    intros HAppend.
    simpl in HAppend.
    auto.
    simpl. auto.
Qed.

    

Lemma transl_code_spec_length: forall code l ofs rtbl,
    transl_code_spec code l ofs rtbl ->
    code_size code = Z.of_nat (length l).
Proof.
  induction code as [|i code].
  - intros l ofs rtbl H. cbn in H.
    destr_in H; congruence.
  - intros l ofs rtbl H.
    cbn in H.
    destruct H as (h' & t' & DEC & IEQ & SPEC).
    cbn.
    apply RelocBinDecode.decode_length in DEC. rewrite DEC.
    rewrite Nat2Z.inj_add.
    rewrite Z2Nat.id.
    assert (code_size code = Z.of_nat (length t')).
    { eapply IHcode; eauto. }
    apply instr_eq_size_eq in IEQ.
    omega.
    generalize (instr_size_positive h').
    omega.
Qed.

Lemma spec_length: forall code l t ofs rtbl  i,
    transl_code_spec (i::code) l ofs rtbl 
    -> transl_code_spec code t (ofs+instr_size i) rtbl 
    -> Z.of_nat (length l) = Z.of_nat (length t) + (instr_size i).
Proof.
  intros code l t ofs rtbl i H H0.
  apply transl_code_spec_length in H.
  apply transl_code_spec_length in H0.
  cbn in H. omega.
Qed.

Lemma spec_decode_ex': forall code ofs l rtbl ,
    transl_code_spec code l ofs rtbl ->
    exists fuel code', decode_instrs rtbl  fuel ofs l nil = OK code'/\ instr_eq_list code code'
                       /\ (fuel <= length(l))%nat.
Proof.
  induction code as [|i code].
  - (* base case *)
    intros ofs l rtbl  TL.
    cbn in TL. destruct l; try contradiction.
    cbn. exists O, nil. split; auto.
  - intros ofs l rtbl  TL.
    generalize TL. intros TL'.
    cbn in TL.
    destruct TL as (h' & t' & DE & EQ & TL).
    generalize (IHcode  _ _ _ TL).
    intros (fuel & code' & DE' & EQ' & EQL).
    generalize (spec_length code l t' ofs rtbl i TL' TL).
    intros HLength.
    exists (Datatypes.S fuel), (h'::code').
    split.
    2: split.
    cbn. destruct l. cbn in DE. congruence.
    rewrite DE. cbn.
    assert (instr_size i = instr_size h') as IEQ. {
      destruct i;
        simpl in EQ;
        try(rewrite EQ;
            auto);
        try(destruct h';inversion EQ; auto).
      1-2: rewrite H; rewrite H0; auto.
    }      
    rewrite <- IEQ.
    generalize (decode_instrs_append _ _ _ _  [h'] _ DE').
    intros HAppend.
    simpl in HAppend.
    auto.
    simpl. auto.
    assert(HSize: instr_size i >= 1). {
      generalize (instr_size_positive i).
      omega.
    }
    omega.
Qed.

Lemma decode_fuel_le: forall rtbl  fuel fuel' ofs l instrs code,
    decode_instrs rtbl  fuel ofs l instrs = OK code
    -> (fuel' >= fuel)%nat
    -> decode_instrs rtbl fuel' ofs l instrs = OK code.
Proof.
  intros rtbl.
  induction fuel.
  (* bc *)
  intros fuel' ofs l instrs code HDecode HFGE.
  simpl in HDecode.
  destruct l; inversion HDecode.
  unfold decode_instrs.
  destruct fuel'.
  1-2: auto.
  intros fuel' ofs l instrs code HDecode HGE.
  induction HGE.
  auto.
  simpl in HDecode.
  destruct l.
  (* easy *)
  simpl. auto.
  monadInv HDecode.
  destruct x.
  cbn [decode_instrs].
  rewrite EQ.
  simpl.
  cut((m >= fuel)%nat).
  intros HMGE.
  generalize (IHfuel _ _ _ _ _ EQ0 HMGE). auto.
  omega.
Qed.

 (* {| *)
 (*    prog_defs := prog_defs prog; *)
 (*    prog_public := prog_public prog; *)
 (*    prog_main := prog_main prog; *)
 (*    prog_sectable := [sec_bytes x2; sec_bytes x1]; *)
 (*    prog_symbtable := prog_symbtable prog; *)
 (*    prog_strtable := prog_strtable prog; *)
 (*    prog_reloctables := prog_reloctables prog; *)
 (*    prog_senv := prog_senv prog |} *)

Definition prog_eq prog tprog:=
  prog.(prog_defs) = tprog.(prog_defs)
  /\  prog.(prog_main) = tprog.(prog_main)
  /\ prog.(prog_public) = tprog.(prog_public)
  /\ prog.(prog_symbtable) = tprog.(prog_symbtable)
  /\ prog.(prog_reloctables) = tprog.(prog_reloctables)
  /\ prog.(prog_senv) = tprog.(prog_senv)
  /\ prog.(prog_strtable) = tprog.(prog_strtable).
(* sectable is not equal!! globalenv prog = globalenv tprog *)
Ltac destr_prog_eq H :=
    match goal with
    | [H: prog_eq _ _ |- _]=>
      unfold prog_eq in H;
      destruct H as (?HDef & ?HMain & ?HPub & ?HSym & ?HREloc & ?HSenv & ?HStr);
      try rewrite HDef;
      try rewrite HMain;
      try rewrite HPub;
      try rewrite HSym;
      try rewrite HREloc;
      try rewrite HSenv;
      try rewrite HStr
    end.

Definition genv_eq ge ge' :=
  ge.(RelocProgSemantics.Genv.genv_symb) = ge'.(RelocProgSemantics.Genv.genv_symb)
  /\ge.(RelocProgSemantics.Genv.genv_ext_funs) = ge'.(RelocProgSemantics.Genv.genv_ext_funs)
  /\ge.(RelocProgSemantics.Genv.genv_next) = ge'.(RelocProgSemantics.Genv.genv_next)
  /\ge.(RelocProgSemantics.Genv.genv_senv) = ge'.(RelocProgSemantics.Genv.genv_senv).

Ltac destr_genv_eq H:=
    match goal with
    |[H: genv_eq _ _ |- _ ] =>
     unfold genv_eq in H;
     destruct H as (?HSymb & ?HExtF & ?HNext & ?HSenv)
    end.


Lemma add_ext_genv_eq_pre': forall ge ge' extfuns symbol,
    genv_eq ge ge'
    ->  genv_eq (RelocProgSemantics.add_external_global extfuns ge symbol) (RelocProgSemantics.add_external_global extfuns ge' symbol).
Proof.
  intros ge ge' extfuns symbol HEq.
  unfold RelocProgSemantics.add_external_global.
  unfold genv_eq. simpl.

  generalize HEq. intros H.
  destr_genv_eq H.
  rewrite HSymb.
  rewrite HExtF.
  rewrite HNext.
  rewrite HSenv.
  repeat split; auto.
Qed.

Lemma add_ext_genv_eq_pre: forall symbt extfuns ge ge',
   genv_eq ge ge'
    ->  genv_eq (RelocProgSemantics.add_external_globals extfuns ge symbt) (RelocProgSemantics.add_external_globals extfuns ge' symbt).
Proof.
  induction symbt.
  intros extfuns ge ge' H.
  simpl.
  auto.
  
  intros extfuns ge ge' H.
  simpl.
  generalize (add_ext_genv_eq_pre' ge ge' extfuns a H).
  intros HAddEq.
  apply(IHsymbt extfuns _ _ HAddEq).
Qed.




Lemma prog_eq_transitivity: forall a b c,
    prog_eq a b
    ->prog_eq b c
    ->prog_eq a c.
Proof.
  intros a b c HAB HBC.
  unfold prog_eq in *.
  destruct HAB as (HABDefs & HABMain & HABPub & HABSym & HABReloc & HABSenv & HABStr).
  destruct HBC as (HBCDefs & HBCMain & HBCPub & HBCSym & HBCReloc & HBCSenv & HBCStr).
  repeat split.
  rewrite HABDefs. auto.
  rewrite HABMain. auto.
  rewrite HABPub. auto.
  rewrite HABSym. auto.
  rewrite HABReloc. auto.
  rewrite HABSenv. auto.
  rewrite HABStr. auto.
Qed.

Lemma prog_eq_symm: forall a b,
    prog_eq a b
    ->prog_eq b a.
Proof.
  intros a b H.
  unfold prog_eq in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  repeat split; auto.
Qed.


Definition get_prog_code prog :=
  let sec_table := prog.(prog_sectable) in
  match SecTable.get sec_code_id sec_table with
  |None => None
  |Some code_sec
   => match code_sec with
      |sec_text c => Some c
      |_ => None
      end
  end.

Lemma prog_eq_to_genv_eq: forall prog tprog,
    prog_eq prog tprog ->
    genv_eq (RelocProgSemantics.globalenv prog)
            (RelocProgSemantics.globalenv tprog).
Proof.
  intros prog tprog HProgEq.
  unfold RelocProgSemantics.globalenv.
  remember {|
       RelocProgSemantics.Genv.genv_symb := RelocProgSemantics.gen_symb_map
                                          (prog_symbtable prog);
       RelocProgSemantics.Genv.genv_ext_funs := Maps.PTree.empty
                                          external_function;
       RelocProgSemantics.Genv.genv_instrs := RelocProgSemantics.gen_instr_map'
                                          (SecTable.get
                                          sec_code_id
                                          (prog_sectable prog));
       RelocProgSemantics.Genv.genv_next := 3%positive;
       RelocProgSemantics.Genv.genv_senv := prog_senv prog |} as env1.
  remember {|
       RelocProgSemantics.Genv.genv_symb := RelocProgSemantics.gen_symb_map
                                          (prog_symbtable tprog);
       RelocProgSemantics.Genv.genv_ext_funs := Maps.PTree.empty
                                          external_function;
       RelocProgSemantics.Genv.genv_instrs := RelocProgSemantics.gen_instr_map'
                                          (SecTable.get
                                          sec_code_id
                                          (prog_sectable tprog));
       RelocProgSemantics.Genv.genv_next := 3%positive;
       RelocProgSemantics.Genv.genv_senv := prog_senv tprog |} as env2.
  assert(Heqenv12: genv_eq env1 env2). {
    subst env1. subst env2.
    destr_prog_eq HProgEq.
    unfold genv_eq. simpl.
    auto.
  }
  destr_prog_eq HProgEq.
  generalize (add_ext_genv_eq_pre (prog_symbtable tprog) (RelocProgSemantics.gen_extfuns (prog_defs tprog)) _ _ Heqenv12).
  intros HgenvEq.
  auto.
Qed.

Lemma symbol_address_transf: forall prog tprog sym ofs,
    prog_eq prog tprog ->
    (RelocProgSemantics.Genv.symbol_address (RelocProgSemantics.globalenv prog) sym ofs) = 
    (RelocProgSemantics.Genv.symbol_address (RelocProgSemantics.globalenv tprog) sym ofs).
Proof.
  intros prog tprog sym ofs HProgEq.

  generalize (prog_eq_to_genv_eq _ _ HProgEq).
  intros HGenvEq.
  unfold RelocProgSemantics.Genv.symbol_address.
  destr_genv_eq HGenvEq.
  unfold RelocProgSemantics.Genv.find_symbol.
  rewrite HSymb.
  auto.
Qed.

Definition code_section_eq (t1 t2: option section) := 
  match t1, t2 with
  | Some (sec_text c1), Some (sec_text c2) => instr_eq_list c1 c2
  | _, _ => False
  end.

Definition data_section_eq rtbl (t1 t2: option section) :=
  match t1, t2 with
  | Some (sec_data l), Some (sec_bytes bs) =>
    transl_init_data_list (gen_reloc_ofs_map (reloctable_data rtbl)) l = OK bs
  | _, _ => False
  end.


Lemma transl_code_spec_decode_refl: forall c bs rtbl c1 ofs,
    transl_code_spec c bs ofs rtbl ->
    exists c', decode_instrs rtbl (length bs) ofs bs c1 = OK (rev c1 ++ c') /\ instr_eq_list c c'.
Proof.
  induction c as [|i c].
  - intros bs rtbl c1 ofs H. cbn in H. destr_in H. subst. 
    cbn. exists nil. split; eauto. rewrite app_nil_r. auto.
  - intros bs rtbl c1 ofs H. cbn in H.
    destruct H as (i' & bs' & DEC & EQ & TL).              
    assert ((length bs > length bs')%nat). 
    { generalize (RelocBinDecode.decode_length _ _ _ _ _ DEC).
      intros. generalize (instr_size_positive i').
      rewrite Z2Nat.inj_lt. omega.
      omega.
      generalize (instr_size_positive i'). omega.
    }
    destruct bs. cbn in H. omega.
    cbn [length decode_instrs].
    rewrite DEC. cbn.
    generalize (IHc bs' _ (i'::c1) _ TL).
    intros (c' & DIS & IEQ).
    erewrite <- instr_eq_size_eq; eauto.
    assert (length bs >= length bs')%nat. cbn in H. omega.
    erewrite decode_fuel_le; eauto.
    eexists. split. cbn. rewrite <- app_assoc. auto.
    cbn. split; auto.
Qed.


Lemma transl_code_decode_instrs_refl: forall rtbl code bytes,
    transl_code rtbl false code = OK bytes ->
    exists code', decode_instrs rtbl (length bytes) 0 bytes [] = OK code' /\ instr_eq_list code code'.
Proof.
  intros.
  monadInv H. destruct x. inv EQ0.
  generalize (decode_encode_refl _ _ _ _ _ eq_refl EQ).
  intros SPEC.
  eapply transl_code_spec_decode_refl; eauto.
Qed.

Lemma transf_program_decode_eq : forall p tp,
    transf_program false p = OK tp -> 
    exists tp', decode_prog_code_section tp = OK tp' /\
           code_section_eq (SecTable.get sec_code_id (prog_sectable p)) (SecTable.get sec_code_id (prog_sectable tp')) /\
           data_section_eq (prog_reloctables p) (SecTable.get sec_data_id (prog_sectable p)) (SecTable.get sec_data_id (prog_sectable tp')) /\
           prog_eq p tp'.
Proof.
  intros p tp TRANSF.
  monadInv TRANSF. destr_in EQ2. inv EQ2.
  unfold transl_sectable in EQ. repeat destr_in EQ. 
  monadInv H0.
  unfold decode_prog_code_section; cbn. 
  replace (Pos.to_nat 1) with (1%nat) by xomega. cbn.
  unfold decode_instrs'; cbn.  
  exploit transl_code_decode_instrs_refl; eauto.
  intros (code' & DEC & CEQ).
  setoid_rewrite DEC.
  cbn. 
  eexists; split; eauto; cbn.
  split; auto.
  split; auto.
  red; cbn; auto.
  repeat (split; auto).
Qed.

Lemma fold_acc_instrs_error:
  forall c e rtbl,
    fold_left (acc_instrs rtbl false) c (Error e) = Error e.
Proof.
  induction c; simpl; intros; eauto.
Qed.
  
Lemma acc_instrs_ready_for_proof: forall rtbl code ofs l x,
    fold_left (acc_instrs rtbl false) code (OK(ofs,l)) = OK x
    -> forallb ready_for_proof code = true.
Proof.
  induction code.
  auto.
  intros ofs l x H.
  simpl in H.
  unfold encode_instr in H.
  simpl in H.
  destruct negb eqn:EQPA.
  simpl in H.
  rewrite ! fold_acc_instrs_error in H. inversion H.
  destruct (encode_instr' rtbl ofs a).
  simpl.
  unfold andb.
  unfold negb in EQPA.
  destruct ready_for_proof; inversion EQPA.
  simpl in H.
  generalize (IHcode _ _ _ H). auto.
  simpl in H.
  rewrite ! fold_acc_instrs_error in H. inversion H.
Qed.


Section PRESERVATION.
  Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.




Axiom init_data_list_relf: forall init m b ofs result bytes prog,
    store_init_data_list (globalenv prog) m b ofs init = Some result
    -> transl_init_data_list (gen_reloc_ofs_map (reloctable_data (prog_reloctables prog))) init = OK bytes
    -> store_init_data_bytes m b ofs bytes = Some result.

Lemma prog_tprog_prog_eq: forall prog tprog,
    transf_program false prog = OK tprog
    ->prog_eq prog tprog.
Proof.
  intros prog tprog TRANSF.
  unfold prog_eq.
  monadInv TRANSF.
  destruct zlt; inversion EQ2.
  simpl.
  repeat split; auto.
Qed.
  


Lemma ge_tge_genv_eq': forall prog tprog,
    transf_program false prog = OK tprog
    -> genv_eq (RelocProgSemantics.globalenv prog)  (RelocProgSemantics.globalenv tprog).
Proof.
  intros prog tprog TRANSF.
  unfold match_prog in TRANSF.
  monadInv TRANSF.
  destruct zlt; inversion EQ2.
  unfold RelocProgSemantics.globalenv.
  simpl.
  remember {|
      RelocProgSemantics.Genv.genv_symb := RelocProgSemantics.gen_symb_map
                                             (prog_symbtable prog);
      RelocProgSemantics.Genv.genv_ext_funs := Maps.PTree.empty
                                                 external_function;
      RelocProgSemantics.Genv.genv_instrs := RelocProgSemantics.gen_instr_map'
                                               (SecTable.get
                                                  sec_code_id
                                                  (prog_sectable prog));
      RelocProgSemantics.Genv.genv_next := 3%positive;
      RelocProgSemantics.Genv.genv_senv := prog_senv prog |} as env1.
  remember {|
      RelocProgSemantics.Genv.genv_symb := RelocProgSemantics.gen_symb_map
                                             (prog_symbtable prog);
      RelocProgSemantics.Genv.genv_ext_funs := Maps.PTree.empty
                                                 external_function;
      RelocProgSemantics.Genv.genv_instrs := RelocProgSemantics.gen_instr_map'
                                               (SecTable.get
                                                  sec_code_id x);
      RelocProgSemantics.Genv.genv_next := 3%positive;
      RelocProgSemantics.Genv.genv_senv := prog_senv prog |} as env2.
  assert(HGenv_eq': genv_eq env1 env2). {
    unfold genv_eq. subst env1. subst env2.
    simpl. repeat split; auto.
  }
  
  generalize  (add_ext_genv_eq_pre (prog_symbtable prog) (RelocProgSemantics.gen_extfuns (prog_defs prog)) env1 env2 HGenv_eq').
  clear HGenv_eq'.
  intros HGenv_eq'.
  destr_genv_eq HGenv_eq'.
  unfold genv_eq.
  rewrite HSymb.
  rewrite HExtF.
  rewrite HNext.
  rewrite HSenv.
  repeat split; auto.
Qed.


Axiom find_instr_refl':forall prog tprog ofs i,
    transf_program false prog = OK tprog
    -> (RelocProgSemantics.globalenv prog).(RelocProgSemantics.Genv.genv_instrs) ofs = Some i
   ->exists i', (RelocProgSemantics.globalenv tprog).(RelocProgSemantics.Genv.genv_instrs) ofs = Some i' /\ RelocBinDecode.instr_eq i i'.

Variables prog tprog: program.

Let ge := RelocProgSemantics1.globalenv prog.
Let tge := RelocProgSemantics1.globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.



Lemma ge_tge_genv_eq:
  genv_eq (RelocProgSemantics.globalenv prog)  (RelocProgSemantics.globalenv tprog).
Proof.
  apply ge_tge_genv_eq'. auto.
Qed.



Lemma init_mem_pres: forall p p' m,
    code_section_eq (SecTable.get sec_code_id (prog_sectable p)) (SecTable.get sec_code_id (prog_sectable p')) ->
    data_section_eq (prog_reloctables p) (SecTable.get sec_data_id (prog_sectable p)) (SecTable.get sec_data_id (prog_sectable p')) ->
    prog_eq p p' ->
    RelocProgSemantics1.init_mem p = Some m -> 
    init_mem p' = Some m.
Proof.
  intros p p' m CEQ DEQ PEQ HInit.
  unfold RelocProgSemantics1.init_mem in HInit.
  destruct (RelocProgSemantics1.alloc_data_section (globalenv p) (prog_sectable p) Mem.empty) eqn:EQData;
    inversion HInit.
  clear H0.
  destruct (alloc_code_section (prog_sectable p) m0) eqn:EQCode;
    inversion HInit.
  clear H0.
  unfold init_mem.
  red in CEQ. destr_in CEQ. 
  destruct v; try contradiction.
  destr_in CEQ; try contradiction.
  destruct v; try contradiction.
  red in DEQ. 
  destr_in DEQ; try contradiction.
  destruct v; try contradiction.
  destr_in DEQ; try contradiction.
  destruct v; try contradiction.
  red in PEQ. destruct PEQ. destruct H0. destruct H1. destruct H2. destruct H3. destruct H4.

  (* data section *)
  unfold alloc_data_section.
  rewrite Heqo2.
  unfold RelocProgSemantics1.alloc_data_section in EQData.
  rewrite Heqo1 in EQData.
  repeat destr_in EQData.
  cbn.
  assert(HSizeEQ: init_data_list_size init = Z.of_nat(length bs)). {
    generalize (transl_init_data_list_size _ _ _  DEQ).
    auto.
  }
  rewrite <- HSizeEQ in *.
  setoid_rewrite Heqp0.
  setoid_rewrite Heqo3.
  erewrite init_data_list_relf; eauto.
  rewrite H7.
  
  (* code section *)
  unfold alloc_code_section.
  unfold alloc_code_section in EQCode.
  rewrite Heqo0. rewrite Heqo in EQCode.
  destr_in EQCode.
  cbn. erewrite <- instr_eq_list_size_eq; eauto.
  setoid_rewrite Heqp1.
  setoid_rewrite EQCode. congruence.
Qed.


Lemma prog_eq_initial_state_gen : forall p p' rs m st,
    prog_eq p p' ->
    initial_state_gen p rs m st -> initial_state_gen p' rs m st.
Proof.
  intros p p' rs m st PEQ INIT.
  inv INIT.
  generalize (initial_state_gen_intro p' rs _ _ _ _ _ _ MALLOC MDROP MRSB MST).
  cbn. intros.
  unfold rs0, ge0. cbn.
  erewrite symbol_address_transf; eauto.
  red in PEQ. destruct PEQ. destruct H1. congruence.
Qed.


Lemma transf_initial_states:
  forall st rs, RelocProgSemantics1.initial_state prog rs st ->
           initial_state tprog rs st.
Proof.
  intros st rs HInit.
  inv HInit.
  edestruct transf_program_decode_eq as (tporg' & DEC & CEQ & DEQ & PEQ).
  red in TRANSF. eauto.
  econstructor; eauto.
  eapply init_mem_pres; eauto.
  apply prog_eq_initial_state_gen with prog; eauto.
Qed.  


Lemma transf_final_states:
  forall st r,
    RelocProgSemantics1.final_state st r -> final_state st r.
Proof.
  intros st r MS.
  auto.
Qed.

Lemma not_find_ext_funct_refl: forall b ofs,
    Genv.find_ext_funct ge (Vptr b ofs) = None
    -> Genv.find_ext_funct (globalenv tprog) (Vptr b ofs) = None.
Proof.
  generalize ge_tge_genv_eq.
  intros HGenv_eq.
  destr_genv_eq HGenv_eq.
  simpl.
  rewrite HExtF.
  auto.
Qed.
  
  
Lemma find_ext_funct_refl: forall b ofs f,
    Genv.find_ext_funct ge (Vptr b ofs) = Some f
    -> Genv.find_ext_funct (globalenv tprog) (Vptr b ofs) = Some f.
Proof.
  unfold Genv.find_ext_funct.
  simpl.
  generalize ge_tge_genv_eq.
  intros HGenv_eq.
  destr_genv_eq HGenv_eq.
  rewrite HExtF. auto.
    
Qed.


Lemma find_instr_refl: forall b ofs i,
    Genv.find_instr ge (Vptr b ofs) = Some i ->
    exists i', Genv.find_instr tge (Vptr b ofs) = Some i' /\ RelocBinDecode.instr_eq i i'.
Proof.
  intros b ofs i HFind.
  simpl in HFind.
  simpl.
  apply (find_instr_refl' prog tprog).
  auto. auto.
Qed.

Definition ge_eq (ge1 ge2: RelocProgSemantics.Genv.t) : Prop :=
  ge1.(RelocProgSemantics.Genv.genv_symb) = ge2.(RelocProgSemantics.Genv.genv_symb) /\
  ge1.(RelocProgSemantics.Genv.genv_ext_funs) = ge2.(RelocProgSemantics.Genv.genv_ext_funs) /\
  ge1.(RelocProgSemantics.Genv.genv_next) = ge2.(RelocProgSemantics.Genv.genv_next) /\ 
  ge1.(RelocProgSemantics.Genv.genv_senv) = ge2.(RelocProgSemantics.Genv.genv_senv) /\
  forall ofs i, ge1.(RelocProgSemantics.Genv.genv_instrs) ofs = Some i -> 
           exists i', ge2.(RelocProgSemantics.Genv.genv_instrs) ofs = Some i' /\ RelocBinDecode.instr_eq i i'.

Definition ge_eq1 (ge1 ge2: RelocProgSemantics1.Genv.t) : Prop :=
  ge1.(Genv.genv_reloc_ofs_symb) = ge2.(Genv.genv_reloc_ofs_symb) /\
  ge_eq (ge1.(Genv.genv_genv)) (ge2.(Genv.genv_genv)).


Lemma transf_program_pres_genv: forall p1 p2,
    transf_program false p1 = OK p2 ->
    ge_eq1 (globalenv p1) (globalenv p2).
Proof.
  intros p1 p2 H.
  generalize (ge_tge_genv_eq' p1 p2 H).
  intros HGenvEq.
  unfold ge_eq1.
  split.
  unfold transf_program in H.
  monadInv H.
  destruct zlt; inversion EQ2.
  simpl.
  unfold gen_reloc_ofs_symbs.
  simpl. auto.
  simpl.

  unfold ge_eq.
  destr_genv_eq HGenvEq.
  rewrite HSymb. rewrite HExtF. rewrite HNext. rewrite HSenv.
  repeat split; auto.
  intros ofs i H0.
  apply (find_instr_refl' p1 p2). auto.
  auto.
Qed.


Lemma symbol_address_refl: forall RELOC_CODE z ofs,
    Genv.symbol_address (globalenv tprog) RELOC_CODE z ofs =
    Genv.symbol_address ge RELOC_CODE z ofs.
Proof.
  intros RELOC_CODE z.
  unfold Genv.symbol_address.
  unfold Genv.find_symbol.
  unfold Genv.genv_reloc_ofs_symb.
  unfold match_prog in TRANSF. monadInv TRANSF.
  unfold ge.
  unfold globalenv.
  simpl.
  unfold gen_reloc_ofs_symbs.
  assert(HSymTable: prog_symbtable tprog = prog_symbtable prog). {
    destruct zlt; inversion EQ2.
    simpl.
    auto.
  }
  rewrite HSymTable.
  simpl.
  assert(HReloctable: prog_reloctables tprog = prog_reloctables prog). {
    destruct zlt; inversion EQ2. simpl. auto.
  }
  rewrite HReloctable.
  destruct Maps.ZTree.get; auto.
  unfold RelocProgSemantics.globalenv.
  assert(HProgDef: (prog_defs tprog) = (prog_defs prog)). {
    destruct zlt; inversion EQ2. simpl. auto.
  }
  rewrite HProgDef.
  simpl.
  rewrite HSymTable.
  unfold  RelocProgSemantics.Genv.find_symbol.
  remember {|
            RelocProgSemantics.Genv.genv_symb := RelocProgSemantics.gen_symb_map
                                          (prog_symbtable prog);
            RelocProgSemantics.Genv.genv_ext_funs := Maps.PTree.empty
                                          external_function;
            RelocProgSemantics.Genv.genv_instrs := RelocProgSemantics.gen_instr_map'
                                          (SecTable.get
                                          sec_code_id
                                          (prog_sectable prog));
            RelocProgSemantics.Genv.genv_next := 3%positive;
            RelocProgSemantics.Genv.genv_senv := prog_senv prog |} as ge'.
  remember {|
            RelocProgSemantics.Genv.genv_symb := RelocProgSemantics.gen_symb_map
                                          (prog_symbtable prog);
            RelocProgSemantics.Genv.genv_ext_funs := Maps.PTree.empty
                                          external_function;
            RelocProgSemantics.Genv.genv_instrs := RelocProgSemantics.gen_instr_map'
                                          (SecTable.get
                                          sec_code_id
                                          (prog_sectable tprog));
            RelocProgSemantics.Genv.genv_next := 3%positive;
            RelocProgSemantics.Genv.genv_senv := prog_senv tprog |} as anotherGe.
  assert(HGenvEq: genv_eq ge' anotherGe). {
    unfold genv_eq.
    subst ge'. subst anotherGe.
    simpl. repeat split; auto.
    destruct zlt; inversion EQ2.
    simpl. auto.
  }
  generalize (add_ext_genv_eq_pre (prog_symbtable prog) (RelocProgSemantics.gen_extfuns (prog_defs prog)) ge' anotherGe HGenvEq).
  intros HGenvEq'.
  destr_genv_eq HGenvEq'.
  rewrite HSymb.
  auto.
Qed.

    
Lemma eval_addrmode32_refl: forall idofs a rs,
    eval_addrmode32 ge idofs a rs = eval_addrmode32 tge idofs a rs.
Proof.
  intros idofs a rs.
  unfold eval_addrmode32.
  unfold tge.
  destruct a.
  destruct base; destruct ofs; destruct const; auto.
  1-4: destruct p.
  1,3: destruct p0.
  1-4: destruct idofs; auto.
  1-4: rewrite symbol_address_refl; auto.
Qed.

Lemma eval_addrmode_refl: forall idofs a rs,
    eval_addrmode ge idofs a rs = eval_addrmode tge idofs a rs.
Proof.
  intros idofs a rs.
  unfold eval_addrmode.
  destruct Archi.ptr64 eqn:EQW; inversion EQW.
  apply eval_addrmode32_refl.
Qed.


Lemma exec_instr_simulation: forall i i' rs m,
    RelocBingen.ready_for_proof i = true ->
    RelocBinDecode.instr_eq i i' -> 
    exec_instr ge i rs m =  exec_instr tge i' rs m.
Proof.
  intros i i' rs m HReadyForProof HInstrEq.
  destruct i; simpl in HReadyForProof; inversion HReadyForProof.
  all:
    try(unfold RelocBinDecode.instr_eq in HInstrEq;
    rewrite HInstrEq;
    unfold exec_instr; simpl;
    destruct (get_pc_offset rs); [rewrite <- HInstrEq|auto]);auto.  
  1:unfold exec_load.
  2:unfold exec_store.
  1-2: rewrite HInstrEq.
  1-2: generalize (eval_addrmode_refl (id_reloc_offset z i') a rs).
  1-2: intros HAddrmode; rewrite HAddrmode; auto.
  
  
  (* lea *)
  rewrite HInstrEq.
    generalize (eval_addrmode32_refl (id_reloc_offset z i') a rs).
    intros HAddrmode. rewrite HAddrmode. auto.

    (* sall *)
    exploit instr_eq_bound; eauto.
    intros RNG.
    destruct i';unfold RelocBinDecode.instr_eq in HInstrEq; try(exfalso; apply HInstrEq).
    destruct HInstrEq as [Hrd Hn].
    rewrite Hrd.
    rewrite Zmod_small in Hn.
    Focus 2.
    auto.
    rewrite Int.repr_unsigned in Hn. subst n.
    unfold exec_instr.
    destruct get_pc_offset; auto.

    (* test *)
    destruct i';unfold RelocBinDecode.instr_eq in HInstrEq; try(exfalso; apply HInstrEq).
    destruct HInstrEq as [[H10 H23] | [H13 H20]].
    rewrite H10. rewrite H23. auto.
    rewrite H13. rewrite H20.
    unfold exec_instr.
    rewrite Val.and_commut. auto.

    (* jmp *)
    destruct ros; inversion HReadyForProof.
    simpl in HInstrEq. destruct i'; inversion HInstrEq.
    unfold exec_instr.
    unfold instr_size.
    cbn [Asm.instr_size'].
    unfold id_reloc_offset.
    cbn [Reloctablesgen.instr_reloc_offset].
    destruct get_pc_offset; auto.
    destruct Mem.storev; auto.
    unfold eval_ros.
    unfold tge.
    rewrite (symbol_address_refl RELOC_CODE (z+1)).
    auto.
    
    (* Pmov_rm_a *)
    destruct i';unfold RelocBinDecode.instr_eq in HInstrEq; try(exfalso; apply HInstrEq).
    destruct HInstrEq as [Hrd Ha].
    rewrite Hrd. rewrite Ha.
    unfold exec_instr.
    destruct (get_pc_offset rs);auto.
    unfold exec_load.
    destruct Archi.ptr64 eqn:EQW; inversion EQW.
    generalize (eval_addrmode_refl  (id_reloc_offset z (Pmov_rm_a rd a0)) a0 rs).
    intros HAddrmode.
    rewrite HAddrmode.
    unfold id_reloc_offset.
    unfold Reloctablesgen.instr_reloc_offset.
    unfold tge. 
    (* int32 and any32 *)
    rewrite Mem.loadv_many_mint_32.
    auto.

    (* Pmov_mr_a , will have the same problem *)
    destruct i';unfold RelocBinDecode.instr_eq in HInstrEq; try(exfalso; apply HInstrEq).
    destruct HInstrEq as [Hrd Ha].
    rewrite Hrd. rewrite Ha.
    unfold exec_instr.
    destruct (get_pc_offset rs);auto.
    unfold exec_store.
    destruct Archi.ptr64 eqn:EQW; inversion EQW.
    generalize (eval_addrmode_refl  (id_reloc_offset z (Pmov_mr_a a0 rs1)) a0 rs).
    intros HAddrmode.
    rewrite HAddrmode.
    unfold id_reloc_offset.
    unfold Reloctablesgen.instr_reloc_offset.
    unfold tge.
    rewrite Mem.storev_many_mint_32.
    auto.

    (* Plabel *)
    destruct i';unfold RelocBinDecode.instr_eq in HInstrEq; try(exfalso; apply HInstrEq).
    unfold exec_instr.
    destruct (get_pc_offset rs); auto.
    unfold exec_instr.
    destruct get_pc_offset; auto.
    
    (* Pnop *)
    simpl in HInstrEq.
    destruct i'; inversion HInstrEq.
    unfold exec_instr.
    cbn [instr_size].
    cbn [Asm.instr_size']. auto.

    unfold exec_instr. auto.
Qed.

Lemma eval_builtin_args_pres: forall idofs e sp m al vl,
    eval_builtin_args preg ge idofs e sp m al vl ->
    eval_builtin_args preg tge idofs e sp m al vl.
Proof.
  induction 1; simpl; intros; eauto. constructor.
  unfold eval_builtin_args.
  assert(HEvalHead: eval_builtin_arg preg tge idofs e sp m a1 b1). {
    induction H;
      try econstructor; try auto; try eauto.

    rewrite symbol_address_refl. auto.
    rewrite<- symbol_address_refl. fold tge. econstructor.
    auto.
  }
  apply list_forall2_cons; auto.
Qed.

Lemma senv_equiv: Senv.equiv (RelocProgSemantics.Genv.genv_senv (Genv.genv_genv ge))
                             (RelocProgSemantics.Genv.genv_senv (Genv.genv_genv tge)).
Proof.
  simpl.
  generalize ge_tge_genv_eq.
  intros HEq.
  destr_genv_eq HEq.
  rewrite HSenv.
  unfold Senv.equiv.
  auto.
Qed.

Lemma find_instr_ready_for_proof vptr i:
  Genv.find_instr ge vptr = Some i
  -> ready_for_proof i = true.
Proof.
  intros HFind.
  unfold Genv.find_instr in HFind.
  simpl in HFind.
  destruct vptr eqn:EQPTR.
  1-5: simpl in HFind; inversion HFind.
  generalize (RelocProgSemantics.global_env_find_instr_inv _ _ _ _ HFind).
  intros (c & HCodeSec & HIn).
  assert (HReadyForAll: forallb ready_for_proof c = true). {
    unfold match_prog in TRANSF.
    monadInv TRANSF.
    destruct zlt; inversion EQ2.
    unfold transl_sectable in EQ.
    simpl in EQ.
    destruct prog_sectable; inversion EQ.
    destruct v; inversion H1.
    destruct s; inversion H2.
    destruct v; inversion H3.
    destruct s; inversion H4.
    clear H2. clear H3. clear H4. clear H5.
    monadInv H1.
    inversion HCodeSec.
    subst c.
    unfold transl_code in EQ0.
    monadInv EQ0.

    generalize (acc_instrs_ready_for_proof (gen_reloc_ofs_map
                                              (reloctable_code (prog_reloctables prog))) code 0 [] _ EQ3).
    auto.
  }
  generalize (forallb_forall ready_for_proof c).
  intros (H1 & H2).
  generalize (H1 HReadyForAll i HIn).
  auto.
Qed.

Theorem step_simulation:
  forall s1 t s2, step ge s1 t s2 -> step tge s1 t s2.
Proof.
  intros s1 t s2 STEP. inv STEP.
  - (* Internal Step *)
    simpl.
    generalize (find_instr_refl _ _ _ H1). intros [i' [HInsEx  HInsEQ]].

    eapply exec_step_internal; eauto.
    eapply not_find_ext_funct_refl; eauto.
    erewrite <- exec_instr_simulation; eauto.
    apply (find_instr_ready_for_proof _ _ H1).

  - (* Builtin Step *)
    generalize (find_instr_refl _ _ _ H1). intros [i' [HInsEx  HInsEQ]].

    eapply exec_step_builtin; eauto.
    eapply not_find_ext_funct_refl; eauto.
    unfold RelocBinDecode.instr_eq in HInsEQ. subst.
    eauto.
    eapply eval_builtin_args_pres; eauto. 
    eapply external_call_symbols_preserved; eauto.
    eapply senv_equiv.

  - (* External Step *)
    eapply exec_step_external; eauto.
    eapply find_ext_funct_refl; eauto.
    eapply external_call_symbols_preserved; eauto.
    apply senv_equiv.
Qed.


Lemma transf_program_correct:
  forall rs, forward_simulation (RelocProgSemantics1.semantics prog rs) (RelocProgSemantics2.semantics tprog rs).
Proof.
  intro rs.
  apply forward_simulation_step with (match_states := fun x y : Asm.state => x = y).
  + simpl.
    unfold match_prog, transf_program in TRANSF. monadInv TRANSF. repeat destr_in EQ2.
    unfold globalenv, genv_senv. simpl.
    unfold RelocProgSemantics.globalenv. simpl. intro id.
    rewrite ! RelocProgSemantics.genv_senv_add_external_globals. simpl. auto.
  + simpl. intros s1 IS. exists s1. split; eauto.
    eapply transf_initial_states; eauto.
  +  (* final state *)
    intros s1 s2 r HState HFinal. inv HState.
    eapply transf_final_states; eauto.
  + simpl. intros s1 t s1' HStep s2 HState.
    inv HState.
    exists s1'. split; eauto.
    eapply step_simulation; eauto.
Qed.
    

End PRESERVATION.

Require Import RelocLinking1.

Lemma transl_sectable_get_code:
  forall rmap sect sect',
    transl_sectable false sect rmap = OK sect' ->
    forall s,
      SecTable.get sec_code_id sect = Some s ->
      exists code x,
        s = sec_text code /\
        transl_code (gen_reloc_ofs_map (reloctable_code rmap)) false code = OK x /\
        SecTable.get sec_code_id sect' = Some (sec_bytes x).
Proof.
  unfold transl_sectable. intros. autoinv.
  vm_compute in H0. inv H0.
  exists code, x. split; auto.
Qed.

Lemma transl_sectable_get_data:
  forall rmap sect sect',
    transl_sectable false sect rmap = OK sect' ->
    forall s,
      SecTable.get sec_data_id sect = Some s ->
      exists data x,
        s = sec_data data /\
        transl_init_data_list (gen_reloc_ofs_map (reloctable_data rmap)) data = OK x /\
        SecTable.get sec_data_id sect' = Some (sec_bytes x).
Proof.
  unfold transl_sectable. intros. autoinv.
  vm_compute in H0. inv H0.
  exists init, x0. split; auto.
Qed.



Lemma transf_program_eq: forall p p',
  transf_program false p = OK p' -> prog_eq p p'.
Proof.
  intros. monadInv H.
  destr_in EQ2. inv EQ2.
  red; cbn. tauto.
Qed.

Lemma match_prog_pres_symbtable: forall p p',
    match_prog p p' -> prog_symbtable p = prog_symbtable p'.
Proof.
  intros p p' H.
  red in H. monadInv H.
  destr_in EQ2. inv EQ2. cbn. auto.
Qed.

Lemma match_prog_pres_reloctables: forall p p',
    match_prog p p' -> prog_reloctables p = prog_reloctables p'.
Proof.
  intros p p' H.
  red in H. monadInv H.
  destr_in EQ2. inv EQ2. cbn. auto.
Qed.

Lemma match_prog_pres_link_data_reloctable: forall p1 p2 p p',
    match_prog p p' -> 
    link_data_reloctable p1 p2 p = link_data_reloctable p1 p2 p'.
Proof.
  intros.
  unfold link_data_reloctable.
  erewrite (match_prog_pres_symbtable _ _ H); eauto.
Qed.

Lemma match_prog_pres_link_code_reloctable: forall p1 p2 p p',
    match_prog p p' -> 
    link_code_reloctable p1 p2 p = link_code_reloctable p1 p2 p'.
Proof.
  intros.
  unfold link_code_reloctable.
  erewrite (match_prog_pres_symbtable _ _ H); eauto.
Qed.

Lemma prog_eq_pres_symbtable: forall p p',
    prog_eq p p' -> prog_symbtable p = prog_symbtable p'.
Proof.
  intros p p' H.
  red in H. intuition.
Qed.


Lemma link_data_reloctable_prog_eq:
  forall p1 p2 p p',
    prog_eq p p' ->
    link_data_reloctable p1 p2 p' = link_data_reloctable p1 p2 p.
Proof.
  intros.
  unfold link_data_reloctable.
  rewrite (prog_eq_pres_symbtable p p'); auto.
Qed.

Lemma link_code_reloctable_prog_eq:
  forall p1 p2 p p',
    prog_eq p p' ->
    link_code_reloctable p1 p2 p' = link_code_reloctable p1 p2 p.
Proof.
  intros.
  unfold link_code_reloctable.
  rewrite (prog_eq_pres_symbtable p p'); auto.
Qed.


Lemma transl_sectable_res_not_nil: forall t1 m t2,
    transl_sectable false t1 m = OK t2 -> t2 <> nil.
Proof.
  intros. unfold transl_sectable in H.
  destruct t1; auto; try congruence.
  destruct v; auto; try congruence.
  destruct t1; auto; try congruence.
  destruct v; auto; try congruence.
  destruct t1; auto; try congruence.
  monadInv H. intro E. congruence.
Qed.

Lemma transf_link_data_reloctable:
  forall p1 p2 tp1 tp2 p t,
    link_data_reloctable p1 p2 p = Some t ->
    match_prog p1 tp1 ->
    match_prog p2 tp2 ->
    link_data_reloctable tp1 tp2 p = Some t.
Proof.
  intros p1 p2 tp1 tp2 p t LINK MATCH1 MATCH2.
  red in MATCH1. red in MATCH2.
  monadInv MATCH1. destr_in EQ2. inv EQ2.
  monadInv MATCH2. destr_in EQ4. inv EQ4.
  unfold link_data_reloctable in LINK.
  destr_in LINK.
  unfold link_data_reloctable; cbn.
  assert (x <> nil).
  { eapply transl_sectable_res_not_nil; eauto. }
  destruct x; try congruence.
  rewrite <- LINK.
  f_equal.
  (* sec_size v0 = sec_size v *)
  unfold transl_sectable in EQ.
  repeat destr_in EQ. monadInv H1.
  cbn in Heqo. inv Heqo.
  cbn.
  erewrite transl_init_data_list_size; eauto.
Qed.

Lemma transf_link_code_reloctable:
  forall p1 p2 tp1 tp2 p t,
    link_code_reloctable p1 p2 p = Some t ->
    match_prog p1 tp1 ->
    match_prog p2 tp2 ->
    link_code_reloctable tp1 tp2 p = Some t.
Proof.
  intros p1 p2 tp1 tp2 p t LINK MATCH1 MATCH2.
  red in MATCH1. red in MATCH2.
  monadInv MATCH1. destr_in EQ2. inv EQ2.
  monadInv MATCH2. destr_in EQ4. inv EQ4.
  unfold link_code_reloctable in LINK.
  destr_in LINK.
  unfold link_code_reloctable; cbn.
  unfold transl_sectable in EQ.
  repeat destr_in EQ.
  monadInv H0. 
  replace (Pos.to_nat 1) with 1%nat by xomega.
  cbn.
  rewrite <- LINK.
  f_equal.
  cbn in Heqo. 
  replace (Pos.to_nat 1) with 1%nat in Heqo by xomega.
  inv Heqo. cbn.
  erewrite transl_code_size; eauto.
Qed.

Lemma reloc_tbl_pres_acc_instrs: forall rtbl1 rtbl2 c1 ofs1 c2 ofs2 c3,
    (forall ofs i l, encode_instr' rtbl1 ofs i = OK l -> encode_instr' rtbl2 ofs i = OK l) ->
    fold_left (acc_instrs rtbl1 false) c1 (OK (ofs1, c2)) = OK (ofs2, c3) ->
    fold_left (acc_instrs rtbl2 false) c1 (OK (ofs1, c2)) = OK (ofs2, c3).
Proof.
  induction c1 as [|i1 c1].
  - cbn. inversion 2; subst. inv H0. auto.
  - intros ofs1 c2 ofs2 c3 ECI ACC.
    cbn in ACC. destr_in ACC. cbn in ACC.
    rewrite fold_acc_instrs_error in ACC. congruence.
    destruct (encode_instr' rtbl1 ofs1 i1) eqn:EI; cbn in ACC.
    Focus 2.
    rewrite fold_acc_instrs_error in ACC. congruence.
    cbn. rewrite Heqb. 
    erewrite ECI; eauto.
Qed.

Lemma transl_code_rtbl: forall c1 c2 rtbl1 rtbl2, 
    (forall ofs i l, encode_instr' rtbl1 ofs i = OK l -> encode_instr' rtbl2 ofs i = OK l) ->
    transl_code rtbl1 false c1 = OK c2 ->
    transl_code rtbl2 false c1 = OK c2.
Proof.
  unfold transl_code.
  intros. monadInv H0. destruct x. inv EQ0.
  erewrite reloc_tbl_pres_acc_instrs; eauto. cbn. auto.
Qed.


(* Lemma transl_code_app : forall c1 c1' c2 c2' rtbl1 rtbl2 rtbl3, *)
(*     (forall ofs i l, encode_instr' rtbl1 ofs i = OK l -> encode_instr' rtbl3 ofs i = OK l) -> *)
(*     (forall ofs i l, encode_instr' rtbl2 ofs i = OK l -> encode_instr' rtbl3 ofs i = OK l) -> *)
(*     transl_code rtbl1 false c1 = OK c1' -> *)
(*     transl_code rtbl2 false c2 = OK c2' -> *)
(*     transl_code rtbl3 false (c1 ++ c2) = OK (c1' ++ c2'). *)
(* Proof. *)
(*   intros. *)
(*   monadInv H1. destruct x. inv EQ0. *)
(*   monadInv H2. destruct x. inv EQ1. *)
(*   generalize (acc_instrs_app _ _ _ _ _ _ _ _ _ _ _ 0 H H0 EQ EQ0). *)
(*   intros (ofs4 & ACC). *)
(*   unfold transl_code.  *)
(*   rewrite ACC. cbn. rewrite rev_app_distr. auto. *)
(* Qed. *)

Axiom transl_code_app : forall c1 c1' c2 c2' rtbl1 rtbl2 rtbl3,
    transl_code rtbl1 false c1 = OK c1' ->
    transl_code rtbl2 false c2 = OK c2' ->
    transl_code rtbl3 false (c1 ++ c2) = OK (c1' ++ c2').

Axiom transl_init_data_list_app : forall d1 d1' d2 d2' rtbl1 rtbl2 rtbl3,
    transl_init_data_list rtbl1 d1 = OK d1' ->
    transl_init_data_list rtbl2 d2 = OK d2' ->
    transl_init_data_list rtbl3 (d1 ++ d2) = OK (d1' ++ d2') .


Lemma transl_sectable_link_comm: forall p1 p2 p rd rc t1 t2,
    RelocLinking.link_reloc_prog p1 p2 = Some p ->
    link_data_reloctable p1 p2 p = Some rd ->
    link_code_reloctable p1 p2 p = Some rc ->
    transl_sectable false (prog_sectable p1) (prog_reloctables p1) = OK t1 ->
    transl_sectable false (prog_sectable p2) (prog_reloctables p2) = OK t2 ->
    exists t, RelocLinking.link_sectable t1 t2 = Some t /\ 
         transl_sectable false (prog_sectable p) {| reloctable_code := rc; reloctable_data := rd |} = OK t.
Proof.
  intros p1 p2 p rd rc t1 t2 LINK LINKD LINKC TL1 TL2.
  unfold transl_sectable in TL1.
  repeat destr_in TL1. monadInv H0.
  unfold transl_sectable in TL2.
  repeat destr_in TL2. monadInv H0.
  cbn. replace (Pos.to_nat 1) with 1%nat by xomega. cbn.
  eexists; split; eauto.
  unfold RelocLinking.link_reloc_prog in LINK.
  repeat destr_in LINK. cbn.
  rewrite Heqs in *.
  rewrite Heqs0 in *.
  cbn in *.
  replace (Pos.to_nat 1) with 1%nat in * by xomega. cbn in *.
  inv Heqo2. inv Heqo0. inv Heqo1. cbn.
  unfold link_data_reloctable in LINKD.
  repeat destr_in LINKD.
  unfold link_code_reloctable in LINKC.
  repeat destr_in LINKC.
  assert (transl_code (fold_right acc_reloc_ofs_map (Maps.ZTree.empty relocentry) rc) 
                      false (code ++ code0) = OK (x ++ x1)) as TLC.
  { eapply transl_code_app; eauto. } 
  rewrite TLC. cbn.
  assert (transl_init_data_list (fold_right acc_reloc_ofs_map (Maps.ZTree.empty relocentry) rd) 
                                (init ++ init0) = OK (x0 ++ x2)) as TLD.
  { eapply transl_init_data_list_app; eauto. }
  rewrite TLD. auto.
Qed.


Definition sec_size_eq n t1 t2 := 
  match SecTable.get n t1, SecTable.get n t2 with
  | Some v1, Some v2 => sec_size v1 = sec_size v2
  | _, _ => True
  end.

Lemma link_reloc_prog_eq: forall p1 p2 p p1' p2' t,
    RelocLinking.link_reloc_prog p1 p2 = Some p ->
    RelocLinking.link_sectable (prog_sectable p1') (prog_sectable p2') = Some t ->
    sec_size_eq sec_data_id (prog_sectable p1) (prog_sectable p1') ->
    sec_size_eq sec_code_id (prog_sectable p1) (prog_sectable p1') ->
    prog_eq p1 p1' ->
    prog_eq p2 p2' ->
    exists p', RelocLinking.link_reloc_prog p1' p2' = Some p' /\
          prog_eq p p' /\ (prog_sectable p' = t).
Proof.
  intros p1 p2 p p1' p2' t LINK LINKTBL SEQ1 SEQ2 PEQ1 PEQ2.
  unfold RelocLinking.link_reloc_prog in LINK.
  repeat destr_in LINK.
  red in PEQ1. 
  inv PEQ1. inv H0. inv H2. inv H3. inv H4. inv H5.
  red in PEQ2. 
  inv PEQ2. inv H7. inv H9. inv H10. inv H11. inv H12.
  unfold RelocLinking.link_reloc_prog.
  rewrite <- H. rewrite <- H1. rewrite <- H0.
  rewrite <- H5. rewrite <- H8. rewrite <- H7.
  rewrite Heqo.
  rewrite LINKTBL.
  unfold RelocLinking.link_sectable in LINKTBL.
  repeat destr_in LINKTBL.
  exists {|
      prog_defs := AST.prog_defs p0;
      prog_public := AST.prog_public p0;
      prog_main := AST.prog_main p0;
      prog_sectable := [s3; s2];
      prog_symbtable := s1;
      prog_strtable := prog_strtable p1;
      prog_reloctables := prog_reloctables p1;
      prog_senv := Genv.globalenv p0 |}; cbn.
  split.
  Focus 2.
  split; auto.
  red; cbn; tauto.
  rewrite <- H9.
  assert (sec_size v1 = sec_size v) as SZEQ1.
  { red in SEQ1.
    rewrite Heqo0 in SEQ1.
    rewrite Heqo5 in SEQ1. congruence.
  }
  rewrite SZEQ1.
  assert (sec_size v2 = sec_size v0) as SZEQ2.
  { red in SEQ2.
    rewrite Heqo1 in SEQ2.
    rewrite Heqo6 in SEQ2. congruence.
  }
  rewrite SZEQ2.
  rewrite Heqo3.
  rewrite <- H2. rewrite Heqo4.
  congruence.
Qed.

Lemma transl_sectable_size_eq: forall t1 rt t2,
  transl_sectable false t1 rt = OK t2 ->
  sec_size_eq sec_code_id t1 t2 /\ sec_size_eq sec_data_id t1 t2.
Proof.
  intros.
  unfold transl_sectable in H. 
  repeat destr_in H. monadInv H1.
  cbn. unfold sec_size_eq. cbn.
  replace (Pos.to_nat 1) with 1%nat by xomega. cbn.
  split.
  erewrite transl_code_size; eauto.
  erewrite transl_init_data_list_size; eauto.
Qed.


Instance transf_link : @TransfLink _ _ RelocLinking1.Linker_reloc_prog
                          RelocLinking1.Linker_reloc_prog
                          match_prog.
Proof.  
  red. simpl. unfold link_reloc_prog.
  intros p1 p2 tp1 tp2 p LINK MATCH1 MATCH2.
  repeat destr_in LINK. 
  exploit transf_link_data_reloctable; eauto. intros LINKDS.
  exploit transf_link_code_reloctable; eauto. intros LINKCS.
  red in MATCH1.
  red in MATCH2.
  monadInv MATCH1. destr_in EQ2. inv EQ2; cbn in *.
  monadInv MATCH2. destr_in EQ4. inv EQ4; cbn in *.
  exploit transl_sectable_link_comm; eauto.
  intros (sec_tbl & LINKSTBL & TL).
  unfold match_prog. unfold transf_program; cbn.
  rewrite TL. cbn.
  generalize (SymbolString.string_bounds (symbentry_id ## (prog_symbtable p0))).
  intros (z & STR & BND). rewrite STR. cbn.
  destruct zlt; try omega.
  eexists; split; eauto. 

  (* Prove linking *)
  set (p1' := {| prog_defs := prog_defs p1;
                       prog_public := prog_public p1;
                       prog_main := prog_main p1;
                       prog_sectable := x;
                       prog_symbtable := prog_symbtable p1;
                       prog_strtable := prog_strtable p1;
                       prog_reloctables := prog_reloctables p1;
                       prog_senv := prog_senv p1 |}) in *.
  set (p2' := {| prog_defs := prog_defs p2;
                 prog_public := prog_public p2;
                 prog_main := prog_main p2;
                 prog_sectable := x1;
                 prog_symbtable := prog_symbtable p2;
                 prog_strtable := prog_strtable p2;
                 prog_reloctables := prog_reloctables p2;
                 prog_senv := prog_senv p2 |}) in *.
  assert (prog_eq p1 p1') as PEQ1.
  { red. subst p1'; cbn. tauto. }
  assert (prog_eq p2 p2') as PEQ2.
  { red. subst p2'; cbn. tauto. }
  generalize (transl_sectable_size_eq _ _ _ EQ).
  intros (SEQ1 & SEQ2).
  generalize (link_reloc_prog_eq _ _ _ p1' p2' _ Heqo LINKSTBL SEQ2 SEQ1 PEQ1 PEQ2).
  intros (p' & LINK & PEQ & STBL).
  rewrite LINK.
  erewrite link_data_reloctable_prog_eq; eauto.
  rewrite LINKDS.
  erewrite link_code_reloctable_prog_eq; eauto.
  rewrite LINKCS. 
  f_equal. 
  red in PEQ.
  inv PEQ. inv H0. inv H2. inv H3. inv H4. inv H5.
  congruence.
Qed.
