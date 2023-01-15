From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     LanguageInterface Smallstep Globalenvs Memory Floats.
Require Import Ctypes Cop Clight.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Require Import LogicalRelations.
Require Import OptionRel.
Require Import Lia.

Section JOIN.

  Inductive contents_join: block -> Z -> mem -> mem -> mem -> Prop  :=
  | contents_join_l:
    forall m1 m2 m b ofs,
      ~Mem.perm m1 b ofs Max Nonempty ->
      (forall k p, Mem.perm m2 b ofs k p <-> Mem.perm m b ofs k p) ->
      ZMap.get ofs m1.(Mem.mem_contents)#b = Undef ->
      ZMap.get ofs m2.(Mem.mem_contents)#b =ZMap.get ofs m.(Mem.mem_contents)#b ->
      Mem.valid_block m2 b ->
      contents_join b ofs m1 m2 m
  | contents_join_r:
    forall m1 m2 m b ofs,
      ~Mem.perm m2 b ofs Max Nonempty ->
      (forall k p, Mem.perm m1 b ofs k p <-> Mem.perm m b ofs k p) ->
      ZMap.get ofs m2.(Mem.mem_contents)#b = Undef ->
      ZMap.get ofs m1.(Mem.mem_contents)#b =ZMap.get ofs m.(Mem.mem_contents)#b ->
      Mem.valid_block m1 b ->
      contents_join b ofs m1 m2 m.

  Inductive alloc_flag_join: mem -> mem -> mem -> Prop :=
  | alloc_flag_join_l:
    forall m m1 m2,
      Mem.alloc_flag m = false ->
      Mem.alloc_flag m1 = true ->
      Mem.alloc_flag m2 = true ->
      (Mem.nextblock m <= Mem.nextblock m1)%positive ->
      alloc_flag_join m m1 m2
  | alloc_flag_join_r:
    forall m m1 m2,
      Mem.alloc_flag m1 = true ->
      Mem.alloc_flag m = false ->
      Mem.alloc_flag m2 = true ->
      (Mem.nextblock m <= Mem.nextblock m1)%positive ->
      alloc_flag_join m1 m m2
  | alloc_flag_join_x:
    forall m1 m2 m,
      Mem.alloc_flag m1 = false ->
      Mem.alloc_flag m2 = false ->
      Mem.alloc_flag m = false ->
      alloc_flag_join m1 m2 m.

  Record join (m1 m2 m: mem) : Prop :=
    mk_join {
        mjoin_contents: forall b ofs, contents_join b ofs m1 m2 m;
        mjoin_nextblock: Mem.nextblock m = Pos.max (Mem.nextblock m1) (Mem.nextblock m2);
        mjoin_alloc_flag: alloc_flag_join m1 m2 m;
      }.

End JOIN.

Section JOIN_PROP.

  Variable (m: mem).

  Instance valid_pointer_join:
    Monotonic
      (@Mem.valid_pointer)
      (join m ++> - ==> - ==> leb).
  Proof.
    do 4 rstep. destruct Mem.valid_pointer eqn: X; try easy.
    cbn. rewrite !Mem.valid_pointer_nonempty_perm in *.
    rename x0 into b. rename x1 into ofs.
    destruct H. specialize (mjoin_contents0 b ofs). inv mjoin_contents0.
    - apply H0. apply X.
    - exfalso. apply H. eauto with mem.
  Qed.

  Instance weak_valid_pointer_join:
    Monotonic
      (@Mem.weak_valid_pointer)
      (join m ++> - ==> - ==> leb).
  Proof.
    unfold Mem.weak_valid_pointer. do 4 rstep.
    destruct orb eqn: X.
    - simpl. rewrite orb_true_iff in *.
      destruct X; [ left | right ]; apply valid_pointer_join in H.
      specialize (H x0 x1). rewrite H0 in H. eauto.
      specialize (H x0 (x1 - 1)%Z). rewrite H0 in H. eauto.
    - easy.
  Qed.

  Instance bool_val_join:
    Monotonic
      (@bool_val)
      (- ==> - ==> join m ++> option_le eq).
  Proof. unfold bool_val. rauto. Qed.

  Instance sem_unary_operation_join:
    Monotonic
      (@sem_unary_operation)
      (- ==> - ==> - ==> join m ++> option_le eq).
  Proof.
    unfold sem_unary_operation.
    unfold sem_notbool, sem_notint, sem_neg, sem_absfloat.
    repeat rstep. f_equal. congruence.
  Qed.

  Instance sem_cast_join:
    Monotonic
      (@Cop.sem_cast)
      (- ==> - ==> - ==> join m ++> option_le eq).
  Proof. unfold Cop.sem_cast. rauto. Qed.

  Instance sem_binarith_join:
    Monotonic
      (@Cop.sem_binarith)
      (- ==> - ==> - ==> - ==> - ==> - ==> - ==> - ==> join m ++> option_le eq).
  Proof. unfold Cop.sem_binarith. rauto. Qed.

  Instance cmp_ptr_join:
    Related
      (@Cop.cmp_ptr)
      (@Cop.cmp_ptr)
      (join m ++> - ==> - ==> - ==> option_le eq).
  Proof.
    rstep. rstep. rstep. rstep. rstep.
    unfold Cop.cmp_ptr. rstep. rstep. rewrite H0. reflexivity. rstep.
    - rstep. unfold Val.cmplu_bool. repeat rstep.
      destruct eq_block; repeat rstep.
    - rstep. unfold Val.cmpu_bool. repeat rstep.
      destruct eq_block; repeat rstep.
  Qed.

  Instance sem_cmp_join:
    Monotonic
      (@Cop.sem_cmp)
      (- ==> - ==> - ==> - ==> - ==> join m ++> option_le eq).
  Proof. unfold Cop.sem_cmp. repeat rstep. Qed.

  Instance sem_binary_operation_join:
    Monotonic
      (@sem_binary_operation)
      (- ==> - ==> - ==> - ==> - ==> - ==> join m ++> option_le eq).
  Proof.
    unfold sem_binary_operation.
    unfold
      Cop.sem_add,
      Cop.sem_add_ptr_int,
      Cop.sem_add_ptr_long,
      Cop.sem_sub,
      Cop.sem_mul,
      Cop.sem_div,
      Cop.sem_mod,
      Cop.sem_and,
      Cop.sem_or,
      Cop.sem_xor,
      Cop.sem_shl,
      Cop.sem_shr.
    repeat rstep.
  Qed.

  Lemma perm_join m1 m2 b ofs k p:
    join m m1 m2 ->
    Mem.perm m1 b ofs k p ->
    Mem.perm m2 b ofs k p.
  Proof.
    intros HM H. inv HM. specialize (mjoin_contents0 b ofs).
    inv mjoin_contents0.
    - apply H1. apply H.
    - exfalso. apply H0. eauto with mem.
  Qed.

  Lemma range_perm_join m1 m2 b lo hi k p:
    join m m1 m2 ->
    Mem.range_perm m1 b lo hi k p ->
    Mem.range_perm m2 b lo hi k p.
  Proof.
    intros HM H ofs X. specialize (H _ X).
    eauto using perm_join.
  Qed.

  Instance load_join:
    Monotonic
      (@Mem.load)
      (- ==> join m ++> - ==> - ==> option_le eq).
  Proof.
    repeat rstep. destruct Mem.load eqn: X; try constructor.
    rename x1 into b. rename x2 into ofs. rename x into ch.
    rename x0 into m1. rename y into m2.
    exploit Mem.load_valid_access. eauto. intros [A B].
    exploit Mem.valid_access_load. split. eapply range_perm_join; eauto. apply B.
    intros [w Y]. rewrite Y. constructor.
    exploit Mem.load_result. apply X.
    exploit Mem.load_result. apply Y. intros -> ->.
    f_equal. apply Mem.getN_exten.
    intros i Hi. destruct H. specialize (mjoin_contents0 b i).
    inv mjoin_contents0; eauto.
    exfalso. apply H. exploit A. instantiate (1 := i).
    rewrite <- size_chunk_conv in Hi. exact Hi.
    eauto with mem.
  Qed.

  Instance loadv_join:
    Monotonic
      (@Mem.loadv)
      (- ==> join m ++> - ==> option_le eq).
  Proof. unfold Mem.loadv. repeat rstep. Qed.

  Instance deref_loc_join a:
    Monotonic
      (@deref_loc a)
      (join m ++> - ==> - ==> - ==> impl).
  Proof.
    repeat rstep. intros A. inv A; eauto using @deref_loc_reference, @deref_loc_copy.
    transport H1. subst. eapply deref_loc_value; eauto.
  Qed.

  Lemma get_setN_inside:
    forall vl p q c,
      p <= q < p + Z.of_nat (length vl) ->
      (ZMap.get q (Mem.setN vl p c)) = nth (Z.to_nat (q - p)) vl Undef.
  Proof.
    induction vl; intros.
    simpl in H. lia.
    simpl length in H. rewrite Nat2Z.inj_succ in H. simpl.
    destruct (zeq p q).
    - subst q. rewrite Mem.setN_outside by lia. rewrite ZMap.gss.
      replace (p - p) with 0 by lia. reflexivity.
    - rewrite IHvl by lia. destruct H as [A B].
      replace (q - p) with (Z.succ (q - p - 1)) by lia.
      rewrite Z2Nat.inj_succ. 2: lia.
      f_equal. f_equal. lia.
  Qed.

  Instance store_join:
    Monotonic
      (@Mem.store)
      (- ==> join m ++> - ==> - ==> - ==> option_le (join m)).
  Proof.
    repeat rstep. destruct Mem.store eqn: X; try constructor.
    rename x into ch. rename x1 into b. rename x2 into ofs. rename x3 into v.
    rename x0 into m1. rename y into m2.
    exploit Mem.store_valid_access_3; eauto. intros [A B].
    edestruct Mem.valid_access_store as [n Y]. split. 2: eauto.
    eapply range_perm_join; eauto.
    rewrite Y. constructor.
    constructor.
    - intros bx ox. destruct H.
      specialize (mjoin_contents0 bx ox). inv mjoin_contents0.
      + apply contents_join_l; eauto.
        * intros k p. specialize (H0 k p).
          assert (P1: Mem.perm m0 bx ox k p <-> Mem.perm m1 bx ox k p).
          split; eauto with mem.
          assert (P2: Mem.perm n bx ox k p <-> Mem.perm m2 bx ox k p).
          split; eauto with mem.
          rewrite P1. rewrite H0. symmetry. apply P2.
        * exploit Mem.store_mem_contents. apply X. intros ->.
          exploit Mem.store_mem_contents. apply Y. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite !PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (length (encode_val ch v))) ox).
                now rewrite !Mem.setN_outside by lia.
                now rewrite !get_setN_inside by lia.
          -- rewrite !PMap.gso; eauto.
        * eauto with mem.
      + apply contents_join_r; eauto.
        * intros P. apply H. eauto with mem.
        * intros k p.
          assert (P: Mem.perm n bx ox k p <-> Mem.perm m2 bx ox k p).
          split; eauto with mem.
          rewrite P. eauto.
        * exploit Mem.store_mem_contents. apply X. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (length (encode_val ch v))) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox).
                exploit A.
                rewrite encode_val_length in g0.
                rewrite <- size_chunk_conv in g0. lia.
                intros. exfalso. eauto with mem.
          -- rewrite PMap.gso; eauto.
        * rewrite H2.
          exploit Mem.store_mem_contents. apply Y. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (length (encode_val ch v))) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox).
                exploit A.
                rewrite encode_val_length in g0.
                rewrite <- size_chunk_conv in g0. lia.
                intros. exfalso. eauto with mem.
          -- rewrite PMap.gso; eauto.
    - destruct H.
      apply Mem.nextblock_store in X.
      apply Mem.nextblock_store in Y. congruence.
    - destruct H.
      exploit Mem.nextblock_store. apply X. intros C.
      apply Mem.store_alloc_flag in X.
      apply Mem.store_alloc_flag in Y.
      inv mjoin_alloc_flag0.
      + apply alloc_flag_join_l; eauto. congruence.
      + apply alloc_flag_join_r; eauto. congruence.
      + apply alloc_flag_join_x; eauto.
  Qed.

  Instance storev_join:
    Monotonic
      (@Mem.storev)
      (- ==> join m ++> - ==> - ==> option_le (join m)).
  Proof. unfold Mem.storev. repeat rstep. Qed.

  Transparent Mem.loadbytes Mem.storebytes.
  Instance loadbytes_join:
    Monotonic
      (@Mem.loadbytes)
      (join m ++> - ==> - ==> - ==> option_le eq).
  Proof.
    repeat rstep. destruct Mem.loadbytes eqn: X; try constructor.
    unfold Mem.loadbytes in *.
    rename x0 into b. rename x1 into ofs. rename x2 into sz.
    rename x into m1. rename y into m2.
    destruct (Mem.range_perm_dec m1 b ofs (ofs + sz) Cur Readable); inv X.
    destruct Mem.range_perm_dec.
    - constructor. apply Mem.getN_exten. intros i Hi.
      destruct H. specialize (mjoin_contents0 b i).
      inv mjoin_contents0; eauto.
      specialize (r i). exploit r.
      {
        destruct (zle 0 sz).
        + rewrite Z2Nat.id in Hi; eauto.
        + rewrite Z_to_nat_neg in Hi; lia.
      }
      intros. exfalso. eauto with mem.
    - exfalso. destruct H.  apply n. intros x Hx.
      specialize (mjoin_contents0 b x). inv mjoin_contents0.
      + apply H0. eauto.
      + exfalso. apply H. eauto with mem.
  Qed.

  Instance storebytes_join:
    Monotonic
      (@Mem.storebytes)
      (join m ++> - ==> - ==> - ==> option_le (join m)).
  Proof.
    repeat rstep. destruct Mem.storebytes eqn: X; try constructor.
    rename x0 into b. rename x1 into ofs. rename x2 into vl.
    rename x into m1. rename y into m2.
    pose proof (Mem.storebytes_range_perm _ _ _ _ _ X) as A.
    edestruct Mem.range_perm_storebytes as (n & Y).
    eapply range_perm_join; eauto.  rewrite Y. constructor.
    constructor.
    - intros bx ox. destruct H.
      specialize (mjoin_contents0 bx ox). inv mjoin_contents0.
      + apply contents_join_l; eauto.
        * intros k p. specialize (H0 k p).
          assert (P1: Mem.perm m0 bx ox k p <-> Mem.perm m1 bx ox k p).
          split; eauto with mem.
          assert (P2: Mem.perm n bx ox k p <-> Mem.perm m2 bx ox k p).
          split; eauto with mem.
          rewrite P1. rewrite H0. symmetry. apply P2.
        * exploit Mem.storebytes_mem_contents. apply X. intros ->.
          exploit Mem.storebytes_mem_contents. apply Y. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite !PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (Datatypes.length vl)) ox).
                now rewrite !Mem.setN_outside by lia.
                now rewrite !get_setN_inside by lia.
          -- rewrite !PMap.gso; eauto.
        * eauto with mem.
      + apply contents_join_r; eauto.
        * intros P. apply H. eauto with mem.
        * intros k p.
          assert (P: Mem.perm n bx ox k p <-> Mem.perm m2 bx ox k p).
          split; eauto with mem.
          rewrite P. eauto.
        * exploit Mem.storebytes_mem_contents. apply X. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (Datatypes.length vl)) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox). exploit A. lia.
                intros. exfalso. eauto with mem.
          -- rewrite PMap.gso; eauto.
        * rewrite H2.
          exploit Mem.storebytes_mem_contents. apply Y. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (Datatypes.length vl)) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox). exploit A. lia.
                intros. exfalso. eauto with mem.
          -- rewrite PMap.gso; eauto.
    - destruct H.
      apply Mem.nextblock_storebytes in X.
      apply Mem.nextblock_storebytes in Y. congruence.
    - destruct H.
      exploit Mem.nextblock_storebytes. apply X. intros C.
      apply Mem.storebytes_alloc_flag in X.
      apply Mem.storebytes_alloc_flag in Y.
      inv mjoin_alloc_flag0.
      + apply alloc_flag_join_l; eauto. congruence.
      + apply alloc_flag_join_r; eauto. congruence.
      + apply alloc_flag_join_x; eauto.
  Qed.

  Opaque Mem.loadbytes Mem.storebytes.

  Instance assign_loc_join:
    Monotonic
      (@assign_loc)
      (- ==> - ==> join m ++> - ==> - ==> - ==> set_le (join m)).
  Proof.
    repeat rstep. intros ma A. inv A.
    - transport H1. eexists; split; eauto.
      eapply assign_loc_value; eauto.
    - transport H4. subst.
      transport H5.
      eexists; split; eauto.
      eapply assign_loc_copy; eauto.
  Qed.

  Instance free_join:
    Monotonic
      (@Mem.free)
      (join m ++> - ==> - ==> - ==> option_le (join m)).
  Proof.
    repeat rstep.
    rename x0 into b. rename x1 into lo. rename x2 into hi.
    rename x into m1. rename y into m2.
    destruct (Mem.free m1 b lo hi) eqn: HF; try constructor.
    edestruct Mem.range_perm_free.
    eapply range_perm_join; eauto.
    eapply Mem.free_range_perm; eauto.
    rewrite e. constructor. constructor.
    - intros bx ox. destruct H.
      specialize (mjoin_contents0 bx ox). inv mjoin_contents0.
      + apply contents_join_l; eauto.
        * intros k p. specialize (H0 k p). split; intros.
          -- exploit Mem.perm_free_3. apply HF. eauto. intros A.
             eapply Mem.perm_free_1; eauto.
             destruct (peq bx b). 2: eauto.
             destruct (zle lo ox). 2: lia.
             destruct (zlt ox hi). 2: lia.
             subst. exfalso. eapply Mem.perm_free_2. apply HF.
             instantiate (1 := ox). lia. eauto.
             apply H0; eauto.
          -- exploit Mem.perm_free_3. apply e. eauto. intros.
             eapply Mem.perm_free_1; eauto.
             destruct (peq bx b). 2: eauto.
             destruct (zle lo ox). 2: lia.
             destruct (zlt ox hi). 2: lia.
             subst. exfalso. eapply Mem.perm_free_2. apply e.
             instantiate (1 := ox). lia. eauto.
             apply H0; eauto.
        * eapply Mem.free_result in HF.
          eapply Mem.free_result in e. subst.
          apply H2.
        * eauto with mem.
      + apply contents_join_r; eauto.
        * intros A. apply H.
          eapply Mem.perm_free_3; eauto.
        * intros k p. specialize (H0 k p). rewrite H0.
          assert (bx <> b \/ ox < lo \/ hi <= ox).
          {
             destruct (peq bx b). 2: eauto.
             destruct (zle lo ox). 2: lia.
             destruct (zlt ox hi). 2: lia.
             exfalso. subst. apply H.
             apply Mem.free_range_perm in HF.
             eauto with mem.
          }
          split; intros.
          -- eapply Mem.perm_free_1; eauto.
          -- eapply Mem.perm_free_3; eauto.
        * eapply Mem.free_result in HF. subst. apply H1.
        * eapply Mem.free_result in HF.
          eapply Mem.free_result in e. subst.
          apply H2.
    - destruct H.
      apply Mem.nextblock_free in HF.
      apply Mem.nextblock_free in e. congruence.
    - destruct H.
      exploit Mem.nextblock_free. apply HF. intros C.
      apply Mem.free_alloc_flag in HF.
      apply Mem.free_alloc_flag in e.
      inv mjoin_alloc_flag0.
      + apply alloc_flag_join_l; eauto. congruence.
      + apply alloc_flag_join_r; eauto. congruence.
      + apply alloc_flag_join_x; eauto.
  Qed.

  Instance free_list_join:
    Monotonic
      (@Mem.free_list)
      (join m ++> - ==> option_le (join m)).
  Proof.
    repeat rstep. revert x y H. rename x0 into l. induction l.
    - constructor. eauto.
    - intros. destruct a. destruct p.
      cbn. destruct (Mem.free x b z0 z) eqn: HX. 2: constructor.
      transport HX. rewrite H0. eauto.
  Qed.

  Local Transparent Mem.alloc.
  Instance alloc_join:
    Monotonic
      (@Mem.alloc)
      (join m ++> - ==> - ==> option_le ((join m) * eq)).
  Proof.
    repeat rstep.
    rename x0 into lo. rename x1 into hi.
    rename x into m1. rename y into m2.
    destruct (Mem.alloc m1 lo hi) eqn: HA; try constructor.
    destruct p as (m1' & b1).
    destruct H.
    exploit Mem.alloc_flag_alloc1; eauto. intros A.
    inv mjoin_alloc_flag0; try congruence.
    edestruct Mem.alloc_succeed as [[m2' b2] HB].
    apply H1. rewrite HB. constructor.
    assert (HNB: Mem.nextblock m1 = Mem.nextblock m2).
    { apply Pos.max_r in H2. congruence. }
    assert (X: b1 = b2).
    {
      apply Mem.alloc_result in HA.
      apply Mem.alloc_result in HB.
      congruence.
    }
    subst; split; cbn; eauto.
    - constructor.
      + intros bx ox. specialize (mjoin_contents0 bx ox).
        inv mjoin_contents0.
        * apply contents_join_l; eauto.
          -- intros k p.
             destruct (peq bx b2).
             ++ subst. split; intros.
                ** exploit Mem.perm_alloc_inv. apply HA. eauto.
                   destruct eq_block; try easy.
                   intros. eauto with mem.
                ** exploit Mem.perm_alloc_inv. apply HB. eauto.
                   destruct eq_block; try easy.
                   intros. eauto with mem.
             ++ split; intros.
                ** exploit Mem.perm_alloc_4. apply HA. all: eauto.
                   intros. eapply Mem.perm_alloc_1; eauto.
                   apply H4. eauto.
                ** exploit Mem.perm_alloc_4. apply HB. all: eauto.
                   intros. eapply Mem.perm_alloc_1; eauto.
                   apply H4. eauto.
          -- unfold Mem.alloc in HA, HB.
             rewrite A in HA. inv HA.
             rewrite H1 in HB. inv HB. cbn.
             rewrite HNB.
             destruct (peq bx (Mem.nextblock m2)).
             ++ subst. rewrite !PMap.gss. reflexivity.
             ++ rewrite !PMap.gso; eauto.
          -- eauto with mem.
        * assert (bx <> b2).
          {
            intros X. subst. unfold Mem.valid_block, Plt in H7.
            apply Mem.alloc_result in HB. subst.
            rewrite HNB in *. lia.
          }
          apply contents_join_r; eauto.
          -- intros X. apply H3. eauto with mem.
          -- intros k p. rewrite H4.
             split; intros; eauto with mem.
          -- unfold Mem.alloc in HA. rewrite A in HA. inv HA.
             cbn. rewrite PMap.gso; eauto.
          -- rewrite H6.
             unfold Mem.alloc in HB. rewrite H1 in HB.
             inv HB. cbn. rewrite PMap.gso; eauto.
      + apply Mem.nextblock_alloc in HA.
        apply Mem.nextblock_alloc in HB.
        rewrite HA. rewrite HB. rewrite HNB.
        symmetry. apply Pos.max_r.
        etransitivity; eauto. rewrite HNB. lia.
      + apply alloc_flag_join_l; eauto.
        * apply Mem.alloc_flag_alloc2 in HA. easy.
        * apply Mem.alloc_flag_alloc2 in HB. easy.
        * apply Mem.nextblock_alloc in HA. rewrite HA.
          etransitivity; eauto. rewrite HNB. lia.
  Qed.

  Opaque Mem.alloc.

(*
  Lemma mse_store_unchanged_on m1 m2 ch b ofs v m1' m2':
    mem_same_except m1 m2 ->
    Mem.store ch m1 b ofs v = Some m1' ->
    Mem.store ch m2 b ofs v = Some m2' ->
    Mem.unchanged_on P m2 m2'.
  Proof.
    intros. eapply Mem.store_unchanged_on; eauto.
    intros i Hi contra.
    eapply diff_perm; eauto.
    exploit Mem.store_valid_access_3. apply H0. intros [A B].
    cut (Mem.perm m1 b i Cur Writable); eauto with mem.
  Qed.

  Lemma mse_storebytes_unchanged_on m1 m2 b ofs vs m1' m2':
    mem_same_except m1 m2 ->
    Mem.storebytes m1 b ofs vs = Some m1' ->
    Mem.storebytes m2 b ofs vs = Some m2' ->
    Mem.unchanged_on P m2 m2'.
  Proof.
    intros. eapply Mem.storebytes_unchanged_on; eauto.
    intros i Hi contra. eapply diff_perm; eauto.
    cut (Mem.perm m1 b i Cur Writable); eauto with mem.
    eapply Mem.storebytes_range_perm in H0. apply H0; eauto.
  Qed.

  Lemma mse_assign_loc_unchanged_on ce m1 ty b ofs bf v m1' m2 m2':
    mem_same_except m1 m2 ->
    assign_loc ce ty m1 b ofs bf v m1' ->
    assign_loc ce ty m2 b ofs bf v m2' ->
    Mem.unchanged_on P m2 m2'.
  Proof.
    intros. inv H0; inv H1; try congruence.
    - unfold Mem.storev in H2. eapply mse_store_unchanged_on; eauto.
      replace chunk with chunk0 by congruence. eauto.
    - eapply mse_storebytes_unchanged_on; eauto.
      replace bytes0 with bytes in *. eauto.
      transport H6. subst. congruence.
    - inv H2. inv H8. unfold Mem.storev in *.
      eapply mse_store_unchanged_on; eauto.
      replace c with c0. eauto.
      transport H5. congruence.
  Qed.

  Lemma assign_loc_determ ce ty m b ofs bf v m1 m2:
    assign_loc ce ty m b ofs bf v m1 ->
    assign_loc ce ty m b ofs bf v m2 ->
    m1 = m2.
  Proof.
    intros H1 H2. inv H1; inv H2; try congruence.
    inv H; inv H7; try congruence.
  Qed.

  Lemma mse_bind_parameters_unchanged_on ge e m1 ps vargs m1' m2 m2':
    mem_same_except m1 m2 ->
    bind_parameters ge e m1 ps vargs m1' ->
    bind_parameters ge e m2 ps vargs m2' ->
    Mem.unchanged_on P m2 m2'.
  Proof.
    intros. revert m2 H H1. induction H0.
    - intros. inv H1. apply Mem.unchanged_on_refl.
    - intros. inv H3.
      edestruct assign_loc_mse as (mx & A & B); eauto.
      rewrite H in H11. inv H11.
      exploit assign_loc_determ. eauto. apply H12. intros ->.
      eapply Mem.unchanged_on_trans; eauto.
      eapply mse_assign_loc_unchanged_on; eauto.
  Qed.

  Lemma mse_alloc_variables_unchanged_on ge e m1 l e' m1' m2 m2':
    mem_same_except m1 m2 ->
    alloc_variables ge e m1 l e' m1' ->
    alloc_variables ge e m2 l e' m2' ->
    Mem.unchanged_on P m2 m2'.
  Proof.
    intros. revert m2 H H1. induction H0.
    - intros. inv H1. apply Mem.unchanged_on_refl.
    - intros. inv H2.
      exploit alloc_mse. eauto. rewrite H. rewrite H10. intros (A & B).
      cbn in *. subst.
      eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
  Qed.
*)
End JOIN_PROP.
