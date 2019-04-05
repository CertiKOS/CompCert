Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Segment SegAsmGlobenv SegAsmBuiltin.
Require Import Asm RawAsm.
Require Import Num.
Require Globalenvs.

Ltac destr_if := 
  match goal with 
  | [ |- context [if ?b then _ else _] ] => 
    let eq := fresh "EQ" in
    (destruct b eqn:eq)
  end.

Ltac destr_match := 
  match goal with 
  | [ |- context [match ?b with _ => _ end] ] => 
    let eq := fresh "EQ" in
    (destruct b eqn:eq)
  end.

Ltac destr_match_in H := 
  match type of H with 
  | context [match ?b with _ => _ end] => 
    let eq := fresh "EQ" in
    (destruct b eqn:eq)
  end.


Definition undef_segid: segid_type := 1%positive.
Definition data_segid:  segid_type := 3%positive.
Definition code_segid:  segid_type := 4%positive.

Definition num_segments: nat := 3.


Section SEGPROG.

Context {I: Type}.
Context {D: Type}.

Definition instr_with_info:Type := I * segblock * ident.

Definition code := list instr_with_info.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code; (* fn_frame: frame_info; *) fn_range:segblock; fn_stacksize: Z; fn_pubrange: Z * Z}.
Definition fundef := AST.fundef function.
Definition gdef := globdef fundef D.

(* mapping from global identifiers to segment labels *)
Definition GID_MAP_TYPE := ident -> option seglabel.
(* mapping from local labels to segment labels *)
Definition LABEL_MAP_TYPE := ident -> ident -> option seglabel.

(* The SegAsm program *)
Record program : Type := {
  prog_defs: list (ident * option gdef * segblock);
  prog_public: list ident;
  prog_main: ident;
  data_seg: segment; (* The data segment *)
  code_seg: segment; (* The code segment *)
  glob_map: GID_MAP_TYPE;
  lbl_map: LABEL_MAP_TYPE;
  prog_senv : Globalenvs.Senv.t;
}.

Definition genv := Genv.t fundef D instr_with_info.

(** Initialization of the global environment *)
Definition add_global (ge:genv) (idg: ident * option gdef * segblock) : genv :=
  let '(gid,gdef,blk) := idg in
  let gsymbs := 
      match gdef with
      | None 
      | Some (Gfun (External _)) =>
        fun id => if ident_eq id gid then Some (Genv.genv_next ge, Ptrofs.zero) else (Genv.genv_symb ge) id
      | _ => Genv.genv_symb ge 
      end
  in
  let gdefs :=
      match gdef with
      | None
      | Some (Gfun (External _)) =>
        (fun (b:block) (ofs:ptrofs) => 
          if (eq_block b (Genv.genv_next ge)) && (Ptrofs.eq ofs Ptrofs.zero)
          then gdef else Genv.genv_defs ge b ofs)
      | _ => Genv.genv_defs ge
      end
  in
  Genv.mkgenv
    (Genv.genv_public ge)
    gsymbs
    gdefs
    (Genv.genv_instrs ge)
    (Genv.genv_internal_codeblock ge)
    (Genv.genv_lbl ge)
    (Pos.succ (Genv.genv_next ge))
    (Genv.genv_senv ge)
    (Genv.genv_smap ge).
  
                     
Fixpoint add_globals (ge:genv) (gl: list (ident * option gdef * segblock)) : genv :=
  match gl with
  | nil => ge
  | (idg::gl') => 
    let ge' := add_global ge idg in
    add_globals ge' gl'
  end. 

Lemma add_global_pres_genv_instrs: forall def ge ge',
  ge' = add_global ge def ->
  forall b ofs, Genv.genv_instrs ge b ofs = Genv.genv_instrs ge' b ofs.
Proof.
  intros def ge ge' H b ofs.
  subst. unfold add_global. destruct def. destruct p.
  destruct (Genv.genv_symb ge i) eqn:EQ.
  destruct p. auto. auto.
Qed.

Lemma add_globals_pres_genv_instrs: forall defs ge ge',
  ge' = add_globals ge defs ->
  forall b ofs, Genv.genv_instrs ge b ofs = Genv.genv_instrs ge' b ofs.
Proof.
  induction defs; simpl; intros.
  - subst. auto.
  - assert (Genv.genv_instrs ge b ofs = Genv.genv_instrs (add_global ge a) b ofs)
           by (eapply add_global_pres_genv_instrs; eauto).
    rewrite H0. apply IHdefs. auto.
Qed.

(* Lemma add_global_pres_genv_segblocks: forall def ge ge', *)
(*   ge' = add_global ge def -> *)
(*   forall id, Genv.genv_segblocks ge id = Genv.genv_segblocks ge' id. *)
(* Proof. *)
(*   intros def ge ge' H id. *)
(*   subst. unfold add_global. destruct def. destruct p. destruct o. *)
(*   destruct g. simpl. auto. auto. auto. *)
(* Qed. *)

(* Lemma add_globals_pres_genv_segblocks: forall defs ge ge', *)
(*   ge' = add_globals ge defs -> *)
(*   forall id, Genv.genv_segblocks ge id = Genv.genv_segblocks ge' id. *)
(* Proof. *)
(*   induction defs; simpl; intros. *)
(*   - subst. auto. *)
(*   - assert (Genv.genv_segblocks ge id = Genv.genv_segblocks (add_global ge a) id) *)
(*            by (eapply add_global_pres_genv_segblocks; eauto). *)
(*     rewrite H0. apply IHdefs. auto. *)
(* Qed. *)

Definition get_instr_ptr (smap:segid_type ->block) (i:instr_with_info): val :=
  let '(_,bi,_) := i in Genv.label_to_ptr smap (segblock_to_label bi).

Definition acc_instr_map (smap:segid_type -> block) (i:instr_with_info) map :
  block -> ptrofs -> option instr_with_info :=
  let ptr := get_instr_ptr smap i in
  fun b ofs => if Val.eq (Vptr b ofs) ptr then Some i else (map b ofs).

Fixpoint acc_instrs_map (smap:segid_type -> block) (c:code) map
  : block -> ptrofs -> option instr_with_info :=
  match c with
  | nil => map
  | i'::c' =>
    let map' := acc_instrs_map smap c' map in
    acc_instr_map smap i' map'
  end.

(* Get the segment labels of instructions *)
Definition code_labels (c:code) : list seglabel :=
  List.map (fun '(_,blk,_) => segblock_to_label blk) c.

Lemma incode_labels : forall i (c:code),
  In i c -> In (segblock_to_label (snd (fst i))) (code_labels c).
Proof.
  induction c; simpl; intros.
  - auto.
  - destruct H. subst. destruct i. destruct p. auto.
    right. apply IHc. auto.
Qed.

Definition code_labels_are_distinct (c: code) : Prop :=
  let labels := (map (fun '(_,blk,_) => segblock_to_label blk) c) in
  list_norepet labels.

Fixpoint pos_advance_N (p:positive) (n:nat) : positive :=
  match n with
  | O => p
  | Datatypes.S n' => pos_advance_N (Psucc p) n'
  end.

Lemma psucc_advance_Nsucc_eq : forall n p,
  pos_advance_N (Pos.succ p) n = Pos.succ (pos_advance_N p n).
Proof.
  induction n; intros.
  - simpl. auto.
  - simpl. rewrite IHn. auto.
Qed.

Lemma pos_advance_N_ple : forall p n,
  Ple p (pos_advance_N p n).
Proof.
  induction n; intros.
  - simpl. apply Ple_refl.
  - simpl.
    rewrite psucc_advance_Nsucc_eq.
    apply Ple_trans with (pos_advance_N p n); auto. apply Ple_succ.
Qed.


(* The following are definitions and properties for segment blocks *)
(*    and the mapping from segment ids to segment blocks. They are necessary *)
(*    for proving invariants of the transformation from RawAsm to SegAsm. *)
(*  *)
Section WITHSEGSLENGTH.

Variable init_block : block. (* The smallest segment block *)
Variable segs_length : nat.   (* The number of segments in a program *)


(* Definition of valid blocks for segments.  A segment block is valid if its id is  *)
(*    greater or equal to 'init_block' and less than 'init_block + segs_length' *)
Definition segblock_is_valid (b:block) : Prop :=
  Ple init_block b /\ Plt b (pos_advance_N init_block segs_length).

Lemma init_segblock_is_valid :
  (segs_length <> 0)%nat -> segblock_is_valid init_block.
Proof.
  clear. red. split. apply Ple_refl.
  destruct segs_length. congruence. simpl.
  rewrite psucc_advance_Nsucc_eq.
  apply Pos.le_lt_trans with (pos_advance_N init_block n).
  apply pos_advance_N_ple. apply Plt_succ.
Qed.

(* With its range restricted to valid blocks, a mapping from  *)
(*    segment ids to blocks is injective *)
Definition injective_on_valid_segs (sbmap: segid_type -> block) : Prop :=
  forall s1 s2, sbmap s1 = sbmap s2 -> segblock_is_valid (sbmap s1) -> s1 = s2.

(* A mapping from segment ids to blocks maps code labels to valid blocks *)
Definition code_labels_are_valid (sbmap: segid_type -> block) (c:code) : Prop :=
  forall i sblk fid, In (i,sblk,fid) c -> segblock_is_valid (sbmap (segblock_id sblk)).

Lemma code_labels_are_valid_cons_inv : forall sbmap a l,
    code_labels_are_valid sbmap (a :: l) ->
    segblock_is_valid (sbmap (segblock_id (snd (fst a))))
    /\ code_labels_are_valid sbmap l.
Proof.
  unfold code_labels_are_valid.
  intros sbmap a l VALID. split.
  - destruct a.  destruct p.  simpl. eapply VALID; eauto. apply in_eq.
  - intros i sblk fid IN. eapply VALID. apply in_cons. eauto.
Qed.

Lemma code_labels_are_valid_cons : forall sbmap a l,
    segblock_is_valid (sbmap (segblock_id (snd (fst a)))) ->
    code_labels_are_valid sbmap l ->
    code_labels_are_valid sbmap (a :: l).
Proof.
  unfold code_labels_are_valid.
  intros sbmap a l SVALID VALID i sblk fid IN. simpl in IN.
  destruct IN.
  - subst. simpl in *. auto.
  - eapply VALID; eauto.
Qed.
  
Lemma code_labels_are_valid_app : forall sbmap l1 l2,
    code_labels_are_valid sbmap l1 ->
    code_labels_are_valid sbmap l2 ->
    code_labels_are_valid sbmap (l1 ++ l2).
Proof.
  induction l1; intros; simpl in *.
  - auto.
  - apply code_labels_are_valid_cons_inv in H. destruct H.
    assert (code_labels_are_valid sbmap (l1 ++ l2))
      by (apply IHl1; auto).
    apply code_labels_are_valid_cons; auto.
Qed.

Lemma code_labels_are_valid_eq_map : forall sbmap sbmap' l,
    (forall id, sbmap id = sbmap' id) ->
    code_labels_are_valid sbmap l ->
    code_labels_are_valid sbmap' l.
Proof.
  induction l; simpl.
  - intros EQMAP VALID. red. intros. contradiction.
  - intros EQMAP VALID.
    apply code_labels_are_valid_cons_inv in VALID. destruct VALID.
    apply code_labels_are_valid_cons; auto.
    rewrite <- EQMAP. auto.
Qed.

End WITHSEGSLENGTH.

(* Given  *)
(*    - 'sbmap': a mapping that maps segment ids to blocks and that *)
(*               is injective for ids mapped on valid blocks *)
(*    - 'c':     a list of instructions residing in segments mapped into *)
(*               valid blocks by 'sbmap' *)
(*    - 'i':     an instruction in 'c' *)
   
(*    if the code labels for instructions in 'c' are all distinct, then *)
(*    the instruction mapping from pairs of segment blocks and offsets *)
(*    generated by 'acc_instrs_map' maps the pair of segment block  *)
(*    and offset for 'i' (determined by 'sbmap') to 'i' itself *)
(* *)
Lemma acc_instrs_map_self : forall init_block slen i c map map' sbmap,
  injective_on_valid_segs init_block slen sbmap ->
  In i c ->
  code_labels_are_distinct c ->
  code_labels_are_valid init_block slen sbmap c ->
  map' = acc_instrs_map sbmap c map ->
  map' (sbmap (segblock_id (snd (fst i)))) (segblock_start (snd (fst i))) = Some i.
Proof.
  induction c; simpl; intros.
  - contradiction.
  - destruct H0.
    + subst. unfold acc_instr_map.
      unfold get_instr_ptr. destruct i. simpl. unfold Genv.label_to_ptr.
      unfold segblock_to_label. simpl. destruct Val.eq. auto.
      destruct p. simpl in *. congruence.
    + subst. unfold acc_instr_map. destruct Val.eq.
      * unfold get_instr_ptr in e. destruct a. destruct p; simpl in *. 
        unfold Genv.label_to_ptr in e.
        unfold segblock_to_label in e. simpl in e.
        inv e. unfold injective_on_valid_segs in H.
        exploit H; eauto.
        unfold code_labels_are_valid in H2. 
        destruct i. destruct p. simpl in *. eapply H2.
        right. eauto. intros.
        destruct i. destruct p. simpl in *.
        assert (segblock_to_label s0 = segblock_to_label s).
        unfold segblock_to_label. f_equal; auto.
        simpl in H1. inv H1. rewrite <- H6 in *.
        apply incode_labels in H0. unfold code_labels in H0. 
        simpl in H0. congruence.
      * eapply IHc; eauto. inv H1. auto. destruct a. destruct p. inv H1.
        unfold code_labels_are_valid in *. intros i2 sblk fid H1.
        eapply H2. apply in_cons. eauto.
Qed.

Definition get_def_code (def: (ident * option gdef * segblock)) : code :=
  let '(_,def,_) := def in
  match def with
  | Some (Gfun (Internal f)) => fn_code f
  | _ => nil
  end.

Fixpoint get_defs_code (defs: list (ident * option gdef * segblock)) : code :=
  match defs with
  | nil => nil
  | def :: defs' => 
    (get_def_code def) ++ (get_defs_code defs')
  end.

Definition get_program_code (p:program) : code := 
  get_defs_code  (prog_defs p).

(* Generate a mapping from offsets to instructions *)
Definition gen_instrs_map (smap:segid_type -> block) (p:program)
  : block -> ptrofs -> option instr_with_info :=
  acc_instrs_map smap (get_program_code p) (fun b ofs => None).
  
(* Generate a function for checking if pc points to an internal instruction *)
Definition gen_internal_codeblock (smap:segid_type -> block) (p:program) : block -> bool:=
  let code_seg_id := segid p.(code_seg) in
  fun b => eq_block b (smap code_seg_id).

Fixpoint acc_segblocks (nextblock: block) (ids: list segid_type) (map: segid_type -> block)
  : (segid_type -> block) :=
  match ids with
  | nil => map
  | id::ids' =>
    let map' := acc_segblocks (Psucc nextblock) ids' map in
    (fun x => if ident_eq x id then nextblock else map' x)
  end.

Definition list_of_segments (p:program) : list segment  :=
  (p.(data_seg) :: (p.(code_seg)) :: nil).

Definition undef_seg_block := 1%positive.
Definition data_block := 2%positive.
Definition code_block := 3%positive.
Definition init_block := data_block.
(* Definition init_glob_block := 4%positive. *)

Definition gen_segblocks (p:program) : (segid_type -> block) :=
  let initmap := fun id => undef_seg_block in
  let ids := List.map segid (list_of_segments p) in
  acc_segblocks init_block ids initmap.

Lemma acc_segblocks_upper_bound : forall l i f,
  (forall id, Plt (f id) i) ->
  (forall id, Plt (acc_segblocks i l f id) (pos_advance_N i (length l))).
Proof.
  induction l; intros.
  - simpl in *. auto.
  - simpl in *. destruct ident_eq.
    + rewrite psucc_advance_Nsucc_eq. apply Pos.le_lt_trans with (pos_advance_N i (Datatypes.length l)).
      apply pos_advance_N_ple. apply Plt_succ.
    + apply IHl. intros. apply Plt_trans with i. apply H.
      apply Plt_succ.
Qed.

Lemma gen_segblocks_upper_bound : forall p id,
  Plt (gen_segblocks p id) (pos_advance_N init_block (length (list_of_segments p))).
Proof.
  intros. unfold gen_segblocks.
  eapply acc_segblocks_upper_bound; eauto.
  intros. unfold undef_seg_block, init_block. apply Plt_succ.
Qed.

(* The ids used to create a mapping from segment ids to blocks  *)
(*    are indeed mapped to valid blocks by the mapping*)
Lemma acc_segblocks_in_valid: forall ids id sbmap initb initmap,
  In id ids ->
  sbmap = acc_segblocks initb ids initmap ->
  segblock_is_valid initb (length ids) (sbmap id).
Proof.
  clear.
  induction ids. intros.
  - inv H.
  - intros id sbmap initb initmap H H0. simpl in H. destruct H.
    subst. simpl. destruct ident_eq.
    apply init_segblock_is_valid. omega. congruence.
    simpl in H0. subst. destruct ident_eq.
    apply init_segblock_is_valid. simpl. omega.
    exploit (IHids id (acc_segblocks (Pos.succ initb) ids initmap)); eauto.
    intros VALID. unfold segblock_is_valid in *.  destruct VALID.
    split. apply Ple_trans with (Pos.succ initb); auto.
    apply Ple_succ. simpl.
    auto.
Qed.
    
Lemma gen_segblocks_in_valid : forall p id sbmap,
  In id (map segid (list_of_segments p)) ->
  sbmap = gen_segblocks p ->
  segblock_is_valid init_block (length (list_of_segments p)) (sbmap id).
Proof.
  clear.
  intros p id sbmap H H0.
  assert (length (list_of_segments p) = length (map segid (list_of_segments p))).
  { rewrite list_length_map. auto. }
  rewrite H1. unfold gen_segblocks in H0.
  eapply acc_segblocks_in_valid; eauto.
Qed.

Lemma acc_segblocks_range: forall ids b initb initmap s,
  b = (acc_segblocks initb ids initmap s) ->
  b = (initmap s) \/ segblock_is_valid initb (length ids) b.
Proof.
  induction ids; simpl; intros.
  - auto.
  - destruct ident_eq; subst.
    + right. red. split. apply Ple_refl.
      simpl. rewrite psucc_advance_Nsucc_eq.
      apply Pos.le_lt_trans with (pos_advance_N initb (Datatypes.length ids)).
      apply pos_advance_N_ple. apply Plt_succ.
    + exploit (IHids (acc_segblocks (Pos.succ initb) ids initmap s)); eauto.
      intros [ACC | VALID].
      auto. right. unfold segblock_is_valid in *. destruct VALID.
      split. apply Ple_trans with (Pos.succ initb); auto. apply Ple_succ.
      simpl. auto.
Qed.

Lemma acc_segblocks_absurd : forall ids b initb initmap s,
  (forall s, Plt (initmap s) b) -> Plt b initb ->
  b = (acc_segblocks initb ids initmap s) -> False.
Proof.
  intros. apply acc_segblocks_range in H1. destruct H1.
  - subst. specialize (H s). specialize (Plt_strict (initmap s)).
    congruence.
  - red in H1. destruct H1. generalize (Plt_le_absurd b initb); eauto.
Qed.

Lemma acc_segblocks_injective : forall ids init_block0 initmap sbmap,
    (forall s, Plt (initmap s) init_block0) ->
    sbmap = acc_segblocks init_block0 ids initmap ->
    injective_on_valid_segs init_block0 (length ids) sbmap.
Proof.
  induction ids; intros.
  - simpl in *. subst. red.
    intros s1 s2 EQ VALID.
    red in VALID. simpl in VALID.
    destruct VALID as [VALID1 VALID2]. exfalso.
    generalize (Plt_le_absurd (initmap s1) init_block0); eauto.
  - simpl in H0. subst. red. intros. repeat destruct ident_eq.
    + subst. auto.
    + red in H1. destruct H1.
      exfalso. eapply (acc_segblocks_absurd ids init_block0 (Psucc init_block0)); eauto.
      apply Pos.lt_succ_r. apply Ple_refl.
    + red in H1. destruct H1.
      exfalso. eapply (acc_segblocks_absurd ids init_block0 (Psucc init_block0)); eauto.
      apply Pos.lt_succ_r. apply Ple_refl.
    + set (sbmap := acc_segblocks (Pos.succ init_block0) ids initmap) in *.
      generalize (IHids (Pos.succ init_block0) initmap sbmap). intros.
      exploit H2; eauto. intros. apply Plt_trans_succ. auto.
      set (b1 := sbmap s1) in *.
      assert (b1 = sbmap s2) by auto. subst sbmap.
      apply acc_segblocks_range in H3. destruct H3; auto.
      red in H1. destruct H1. specialize (H s2). rewrite <- H3 in H.
      exfalso. generalize (Plt_le_absurd b1 init_block0); eauto.
Qed.

Lemma gen_segblocks_injective : forall p,
    injective_on_valid_segs init_block (length (list_of_segments p)) (gen_segblocks p).
Proof.
  intros p. set (sbmap := gen_segblocks p) in *.
  unfold gen_segblocks in *.
  assert (length (list_of_segments p) = length (map segid (list_of_segments p))).
  symmetry. apply list_length_map. rewrite H.
  eapply acc_segblocks_injective; eauto.
  instantiate (1:=(fun _ : segid_type => undef_seg_block)). intros. simpl.
  apply Plt_succ. auto.
Qed.


Definition empty_genv (p:program): genv :=
  Genv.mkgenv (prog_public p) (fun id => None) (fun b ofs => None) (fun b ofs => None) (fun b => false)
              (fun fid lbl => None) 1%positive (prog_senv p) (gen_segblocks p).

Definition gidmap_to_symbmap (smap: segid_type -> block) (gmap:GID_MAP_TYPE) :=
  fun id =>
    match gmap id with
    | None => None
    | Some (sid,ofs) => Some (smap sid, ofs)
    end.

Definition lblmap_to_symbmap (smap: segid_type -> block) (lmap:LABEL_MAP_TYPE) :=
  fun fid lbl =>
    match lmap fid lbl with
    | None => None
    | Some (sid,ofs) => Some (smap sid, ofs)
    end.

Definition globalenv (p: program) : genv :=
  let smap := gen_segblocks p in
  let symbmap := gidmap_to_symbmap smap (glob_map p) in
  let lblmap := lblmap_to_symbmap smap (lbl_map p) in
  let imap := gen_instrs_map smap p in
  let nextblock := Pos.of_succ_nat num_segments in
  let cbmap := gen_internal_codeblock smap p in
  let genv := Genv.mkgenv (prog_public p) symbmap (fun b ofs => None) imap cbmap lblmap nextblock 
                          (prog_senv p) (gen_segblocks p) in
  add_globals genv p.(prog_defs).
  
(* (** Initialization of the memory *) *)
(* Definition mem_block_size : Z := *)
(*   if Archi.ptr64 then two_power_nat 64 else two_power_nat 32. *)

(* Lemma genv_gen_segblocks:  forall p sid, *)
(*   Genv.genv_segblocks (globalenv p) sid = gen_segblocks p sid. *)
(* Proof. *)
(*   unfold globalenv. intros p sid. *)
(*   erewrite <- add_globals_pres_genv_segblocks; eauto. simpl. auto. *)
(* Qed. *)

Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Section WITHGE.

Variable ge:genv.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof gloc ofs => Mem.store Mptr m b p (Genv.symbol_address ge gloc ofs)
  | Init_space n => Some m
  end.

Fixpoint store_init_data_list (m: mem) (b: block) (p: Z) (idl: list init_data)
                              {struct idl}: option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m b p id with
      | None => None
      | Some m' => store_init_data_list m' b (p + init_data_size id) idl'
      end
  end.

(* Allocate global definitions like in previous assembly language.
   Even though the internal function and data definitions will reside
   in data and code segments, we still allocate blocks for them to
   make the memory injection easy to define 
*)
Definition alloc_global (m: mem) (idg: ident * option gdef * segblock): option mem :=
  let '(id, gdef, sb) := idg in
  match gdef with
  | None => 
    let (m1, b) := Mem.alloc m 0 0 in
    Some m1
  | Some (Gfun f) =>
    (** The block allocated for the internal function is dummy.
        Internal function actually reside in the block for the code segment. *)
    let (m1, b) := Mem.alloc m 0 1 in
    (* Mem.drop_perm m1 b 0 1 Nonempty *)
    Some m1
  | Some (Gvar v) =>
    (** The block allocated for the data is dummy.
        Data actually reside in the block for the code segment. *)
    let (m1, b) := Mem.alloc m 0 0 in
    Some m1 
  end.

Fixpoint alloc_globals (m: mem) (gl: list (ident * option gdef * segblock))
                       {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_global m g with
      | None => None
      | Some m' => alloc_globals m' gl'
      end
  end.

Definition store_global n (smap:segid_type -> block) (m: mem) (idg: ident * option gdef * segblock): option mem :=
  let '(id, gdef, sb) := idg in
  let ofs := Ptrofs.unsigned (segblock_start sb) in
  let sz := Ptrofs.unsigned (segblock_size sb) in
  let b := smap (segblock_id sb) in
  match gdef with
  | None => Some m
  | Some (Gfun f) =>
    match f with
    | External _ => 
      Mem.drop_perm m (pos_advance_N (Pos.of_succ_nat num_segments) n) 0 1 Nonempty
    | Internal f =>
      Mem.drop_perm m b ofs (ofs + sz) Nonempty
    end
  | Some (Gvar v) =>
    let init := gvar_init v in
    let isz := init_data_list_size init in
    match Globalenvs.store_zeros m b ofs isz with
    | None => None
    | Some m1 =>
      match store_init_data_list m1 b ofs init with
      | None => None
      | Some m2 => Mem.drop_perm m2 b ofs (ofs+isz) (Globalenvs.Genv.perm_globvar v)
      end
    end
  end.

Fixpoint store_globals_iter n (smap:segid_type->block) (m: mem) (gl: list (ident * option gdef * segblock))
                       : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match store_global n smap m g with
      | None => None
      | Some m' => store_globals_iter (Datatypes.S n) smap m' gl'
      end
  end.

Definition store_globals (smap:segid_type->block) (m: mem) (gl: list (ident * option gdef * segblock))
                       : option mem :=
  store_globals_iter 0 smap m gl.

End WITHGE.

Fixpoint alloc_segments m (segs: list segment) :=
  match segs with
  | nil => m
  | s :: segs' =>
    match Mem.alloc m 0 (Ptrofs.unsigned (segsize s)) with
    | (m',_) => alloc_segments m' segs'
    end
  end.

Definition alloc_segment m seg := Mem.alloc m 0 (Ptrofs.unsigned (segsize seg)).

Definition init_mem (p: program) :=
  let ge := globalenv p in
  let (initm,_) := Mem.alloc Mem.empty 0 0 in (** *r A dummy block is allocated for undefined segments *)
  let m := alloc_segments initm (list_of_segments p) in
  (* let (m1,_) := alloc_segment initm (fst (code_seg p)) in *)
  (* let (m2,_) := alloc_segment m1 (data_seg p) in *)
  match alloc_globals m (prog_defs p) with
  | None => None
  | Some m3 =>
    store_globals ge (gen_segblocks p) m3 (prog_defs p)
  end.


Lemma store_init_data_perm : forall (ge:genv) m m' b b' p i q k prm,
  store_init_data ge m b p i = Some m' -> Mem.perm m' b' q k prm <-> Mem.perm m b' q k prm.
Proof.
  intros ge m m' b b' p i q k prm H.
  unfold store_init_data in H. destruct i; try now (eapply store_perm; eauto).
  inv H. split; auto.
Qed.

Lemma store_init_data_list_perm : forall idl (ge:genv) m m' b p  b' q k prm,
  store_init_data_list ge m b p idl = Some m' -> Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm.
Proof.
  induction idl; intros.
  - inv H. split; auto.
  - inv H. destr_match_in H1.
    + erewrite <- store_init_data_perm; eauto.
    + inv H1.
Qed.

Lemma store_init_data_stack : forall v (ge:genv) (m m' : mem) (b : block) (ofs : Z),
       store_init_data ge m b ofs v = Some m' -> Mem.stack m' = Mem.stack m.
Proof.
  intros v ge0 m m' b ofs H. destruct v; simpl in *; try (now eapply Mem.store_stack_blocks; eauto).
  inv H. auto.
Qed.

Lemma store_init_data_list_stack : forall l (ge:genv) (m m' : mem) (b : block) (ofs : Z),
       store_init_data_list ge m b ofs l = Some m' -> Mem.stack m' = Mem.stack m.
Proof.
  induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in H. destr_match_in H; inv H.
    exploit store_init_data_stack; eauto.
    exploit IHl; eauto.
    intros. congruence.
Qed.

Existing Instance inject_perm_all.

Lemma store_global_stack : forall (ge:genv) n smap m def m',
    store_global ge n smap m def = Some m' ->
    Mem.stack m' = Mem.stack m.
Proof.
  intros ge0 n smap m def m' H.
  destruct def. destruct p. destruct o. destruct g. destruct f.
  - simpl in H. exploit Mem.drop_perm_stack; eauto.
  - simpl in H. exploit Mem.drop_perm_stack; eauto.
  - simpl in H. destr_match_in H; inv H. destr_match_in H1; inv H1.
    exploit Globalenvs.Genv.store_zeros_stack; eauto.
    exploit store_init_data_list_stack; eauto.
    exploit Mem.drop_perm_stack; eauto. intros. congruence.
  - simpl in H. inv H. auto.
Qed.

Lemma store_globals_iter_stack : forall l (ge:genv) n smap m m',
    store_globals_iter ge n smap m l = Some m' ->
    Mem.stack m' = Mem.stack m.
Proof.
  induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in H. destr_match_in H; inv H.
    exploit store_global_stack; eauto. intros.
    exploit IHl; eauto. intros. congruence.
Qed.

Lemma store_globals_stack : forall l (ge:genv) smap m m',
    store_globals ge smap m l = Some m' ->
    Mem.stack m' = Mem.stack m.
Proof.
  unfold store_globals. intros.
  eapply store_globals_iter_stack; eauto.
Qed.

Lemma alloc_segments_perm_ofs : forall segs m1 m2
                                  (ALLOCSEGS : alloc_segments m1 segs = m2)
                                  (PERMOFS : forall b ofs k p, Mem.perm m1 b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned),
    (forall b ofs k p, Mem.perm m2 b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned).
Proof.
  induction segs. intros.
  - subst. simpl in H. eauto.
  - intros. simpl in ALLOCSEGS.
    destruct (Mem.alloc m1 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    eapply IHsegs; eauto.
    intros b1 ofs0 k0 p0 PERM.
    erewrite alloc_perm in PERM; eauto.
    destruct peq.
    generalize (Ptrofs.unsigned_range_2 (segsize a)). omega.
    eauto.
Qed.

Lemma one_le_ptrofs_max_unsigned : 1 <= Ptrofs.max_unsigned.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus.
  unfold Ptrofs.wordsize.
  generalize Wordsize_Ptrofs.wordsize_not_zero. intros.
  destruct Wordsize_Ptrofs.wordsize. congruence.
  rewrite two_power_nat_S.
  generalize (two_power_nat_pos n). intros. omega.
Qed.

Lemma alloc_globals_perm_ofs : forall defs m1 m2
                                  (ALLOC : alloc_globals m1 defs = Some m2)
                                  (PERMOFS : forall b ofs k p, Mem.perm m1 b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned),
    (forall b ofs k p, Mem.perm m2 b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned).
Proof.
  induction defs. intros.
  - simpl in ALLOC. inv ALLOC. eapply PERMOFS; eauto.
  - intros. destruct a. destruct p0. destruct o. destruct g. 
    + simpl in ALLOC.
      destruct (Mem.alloc m1 0 1) eqn:ALLOC1.
      eapply IHdefs; eauto.
      intros.
      erewrite alloc_perm in H0; eauto.
      destruct peq. subst. 
      generalize one_le_ptrofs_max_unsigned. omega.
      eapply PERMOFS; eauto.
    + simpl in ALLOC.
      destruct (Mem.alloc m1 0 0) eqn:ALLOC1.
      eapply IHdefs; eauto.
      intros.
      erewrite alloc_perm in H0; eauto.
      destruct peq. subst. omega.
      eapply PERMOFS; eauto.
    + simpl in ALLOC.
      destruct (Mem.alloc m1 0 0) eqn:ALLOC1.
      eapply IHdefs; eauto.
      intros.
      erewrite alloc_perm in H0; eauto.
      destruct peq. subst. omega.
      eapply PERMOFS; eauto.
Qed.


Lemma alloc_segments_stack: forall l m m',
    m' = alloc_segments m l -> Mem.stack m' = Mem.stack m.
Proof.
  induction l; intros.
  - simpl in H. subst. auto.
  - inv H. simpl. destruct (Mem.alloc m 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    exploit Mem.alloc_stack_blocks; eauto. intros H. rewrite <- H.
    erewrite IHl; eauto.
Qed.

Lemma alloc_segments_nextblock :  forall l m m',
  m' = alloc_segments m l -> Mem.nextblock m' = pos_advance_N (Mem.nextblock m) (length l).
Proof.
  induction l; intros.
  - inv H. simpl. auto.
  - inv H. simpl.
    destruct (Mem.alloc m 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    erewrite IHl; eauto. exploit Mem.nextblock_alloc; eauto. intros. rewrite H.
    rewrite psucc_advance_Nsucc_eq. auto.
Qed.

Lemma alloc_segment_stack: forall s m m' b,
    alloc_segment m s = (m',b) -> Mem.stack m' = Mem.stack m.
Proof. 
  unfold alloc_segment. intros.
  erewrite Mem.alloc_stack_blocks; eauto.
Qed.

Definition DEF : Type := ident * option gdef * segblock.


Lemma alloc_global_stack: forall (def: DEF)  m m',  
    alloc_global m def = Some m' -> Mem.stack m = Mem.stack m'.
Proof.
  intros. destruct def. destruct p. inv H.
  destruct o. destruct g.
  - destruct (Mem.alloc m 0 1) eqn:ALLOC.
    exploit Mem.alloc_stack_blocks; eauto. intros.
    congruence.
  - destruct (Mem.alloc m 0 0) eqn:ALLOC.
    inv H1.
    exploit Mem.alloc_stack_blocks; eauto. 
  - destruct (Mem.alloc m 0 0) eqn:ALLOC.
    inv H1.
    exploit Mem.alloc_stack_blocks; eauto. 
Qed.
    
Lemma alloc_globals_stack: forall (defs: list DEF) m m',  
    alloc_globals m defs = Some m' -> Mem.stack m = Mem.stack m'.
Proof.
  induction defs; inversion 1.
  - inv H. auto.
  - destr_match_in H1; inv H1.
    exploit alloc_global_stack; eauto. 
    intros STKEQ. rewrite STKEQ.
    erewrite IHdefs; eauto.
Qed.
    

Lemma init_mem_stack:
  forall p m,
    init_mem p = Some m ->
    Mem.stack m = nil.
Proof.
  intros. unfold init_mem in H.
  destruct (Mem.alloc Mem.empty 0 0) eqn:ALLOC.
  exploit Mem.alloc_stack_blocks; eauto. intros.
  destruct (alloc_segment m0 (code_seg p)) eqn:ALLOC_CODE.
  destruct (alloc_segment m1 (data_seg p)) eqn:ALLOC_DATA.
  destr_match_in H; inv H.
  exploit store_globals_stack; eauto. intros.
  apply alloc_segment_stack in ALLOC_CODE.
  apply alloc_segment_stack in ALLOC_DATA.
  rewrite H. erewrite <- alloc_globals_stack; eauto.
  erewrite alloc_segments_stack; eauto. 
  rewrite H0. erewrite Mem.empty_stack; eauto.
Qed.

Lemma store_init_data_nextblock : forall v (ge:genv) m b ofs m',
  store_init_data ge m b ofs v = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros. destruct v; simpl in *; try now (eapply Mem.nextblock_store; eauto).
  inv H. auto.
Qed.
    
Lemma store_init_data_list_nextblock : forall l (ge:genv) m b ofs m',
  store_init_data_list ge m b ofs l = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction l; intros.
  - inv H. auto.
  - inv H. destr_match_in H1; inv H1.
    exploit store_init_data_nextblock; eauto.
    exploit IHl; eauto. intros. congruence.
Qed.

Remark store_global_nextblock:
  forall v (ge: genv) n smap m m',
  store_global ge n smap m v = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros. destruct v. destruct p. destruct o. destruct g. destruct f.
  - simpl in H. eapply Mem.nextblock_drop; eauto.
  - simpl in H. eapply Mem.nextblock_drop; eauto.
  - simpl in H. destr_match_in H; inv H.
    destr_match_in H1; inv H1.
    exploit Globalenvs.Genv.store_zeros_nextblock; eauto.
    exploit store_init_data_list_nextblock; eauto.
    exploit Mem.nextblock_drop; eauto.
    intros. congruence.
  - simpl in H. inv H. auto.
Qed.

Remark store_globals_iter_nextblock:
  forall gl (ge: genv) n smap m m',
  store_globals_iter ge n smap m gl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction gl; intros.
  - inv H. auto.
  - inv H. destr_match_in H1; inv H1.
    exploit store_global_nextblock; eauto.
    exploit IHgl; eauto.
    intros. congruence.
Qed.

Remark store_globals_nextblock:
  forall gl (ge: genv) smap m m',
  store_globals ge smap m gl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold store_globals. intros.
  eapply store_globals_iter_nextblock; eauto.
Qed.

Lemma alloc_global_nextblock : forall (def:DEF) m m',
  alloc_global m def = Some m' -> 
  Mem.nextblock m' = Pos.succ (Mem.nextblock m).
Proof.
  intros. destruct def. destruct p. destruct o. destruct g.
  - simpl in H.
    destruct (Mem.alloc m 0 1) eqn:ALLOC.
    exploit Mem.nextblock_alloc; eauto. intros. rewrite <- H0.
    inv H. auto.
  - simpl in H.
    destruct (Mem.alloc m 0 0) eqn:ALLOC.
    inv H.
    exploit Mem.nextblock_alloc; eauto. 
  - simpl in H.
    destruct (Mem.alloc m 0 0) eqn:ALLOC.
    inv H.
    exploit Mem.nextblock_alloc; eauto. 
Qed.    

Lemma alloc_globals_nextblock : forall (defs: list DEF) m m',
  alloc_globals m defs = Some m' -> 
  Mem.nextblock m' = pos_advance_N (Mem.nextblock m) (List.length defs).
Proof.
  induction defs; intros; inv H.
  - auto.
  - destr_match_in H1; inv H1.
    simpl. 
    exploit alloc_global_nextblock; eauto.
    exploit IHdefs; eauto.
    intros. rewrite <- H1. auto.
Qed.
    
Lemma alloc_segment_nextblock : forall m s m' b,
    alloc_segment m s = (m', b) -> Mem.nextblock m' = Pos.succ (Mem.nextblock m).
Proof.
  unfold alloc_segment. intros.
  exploit Mem.nextblock_alloc; eauto.
Qed.

(* Lemma add_global_pres_genv_next : *)
(*   forall def (ge ge' : genv), *)
(*   ge' = add_global ge def -> Genv.genv_next ge = Genv.genv_next ge'. *)
(* Proof. *)
(*   intros. destruct def. destruct p. *)
(*   destruct o. destruct g. destruct f. *)
(*   - simpl in *. destruct (Genv.genv_symb ge i) eqn:GSYM. *)
(*     destruct p. subst. simpl. auto.  *)
(*     subst. auto. *)
(*   - simpl in *. destruct (Genv.genv_symb ge i) eqn:GSYM. *)
(*     destruct p. subst. simpl. auto.  *)
(*     subst. auto. *)
(*   - simpl in *. destruct (Genv.genv_symb ge i) eqn:GSYM. *)
(*     destruct p. subst. simpl. auto.  *)
(*     subst. auto. *)
(*   - simpl in *. destruct (Genv.genv_symb ge i) eqn:GSYM. *)
(*     destruct p. subst. simpl. auto.  *)
(*     subst. auto. *)
(* Qed. *)

(* Lemma add_globals_pres_genv_next : *)
(*   forall (defs : list (ident * option gdef * segblock)) (ge ge' : genv), *)
(*   ge' = add_globals ge defs -> Genv.genv_next ge = Genv.genv_next ge'. *)
(* Proof. *)
(*   induction defs; intros; simpl in *. *)
(*   - subst. auto. *)
(*   - exploit IHdefs; eauto. *)
(*     erewrite <- add_global_pres_genv_next; eauto. *)
(* Qed. *)

Lemma add_global_next_block: forall (ge:genv) def,
    Genv.genv_next (add_global ge def) = Pos.succ (Genv.genv_next ge).
Proof.
  intros. destruct def. destruct p. simpl. auto.
Qed.

Lemma add_globals_next_block: forall (defs: list DEF) ge,
  Genv.genv_next (add_globals ge defs) = pos_advance_N (Genv.genv_next ge) (List.length defs).
Proof.
  induction defs; intros; simpl.
  - auto.
  - rewrite IHdefs. 
    rewrite add_global_next_block. auto.
Qed.

Lemma alloc_segments_nextblock' : forall (l : list segment) (m: mem), 
  Mem.nextblock (alloc_segments m l) = pos_advance_N (Mem.nextblock m) (length l).
Proof.
  intros. apply alloc_segments_nextblock. auto.
Qed.

Lemma alloc_global_pres_perm :
  forall def m b ofs k p m'
  (PERM: Mem.perm m b ofs k p)
  (ALLOC: alloc_global m def = Some m'),
    Mem.perm m' b ofs k p.
Proof.
  intros. 
  exploit Mem.perm_valid_block; eauto. 
  unfold Mem.valid_block. intros.
  destruct def. destruct p0. destruct o. destruct g. 
  - simpl in ALLOC.
    destruct (Mem.alloc m 0 1) eqn:ALLOC1.
    exploit Mem.alloc_result; eauto. intros. subst.
    assert (b <> Mem.nextblock m).
    {
      destruct (peq b (Mem.nextblock m)); auto.
      subst. exfalso. eapply Plt_strict; eauto.
    }
    inv ALLOC.
    erewrite alloc_perm; eauto. 
    destruct peq. subst. contradiction.
    auto.
  - simpl in ALLOC.
    destruct (Mem.alloc m 0 0) eqn:ALLOC1. inv ALLOC.
    erewrite alloc_perm; eauto.
    exploit Mem.alloc_result; eauto. intros. subst.
    destruct peq.
    subst.
    exfalso. eapply Plt_strict; eauto.
    auto.
  - simpl in ALLOC.
    destruct (Mem.alloc m 0 0) eqn:ALLOC1. inv ALLOC.
    erewrite alloc_perm; eauto.
    exploit Mem.alloc_result; eauto. intros. subst.
    destruct peq.
    subst.
    exfalso. eapply Plt_strict; eauto.
    auto.
Qed.

Lemma alloc_globals_pres_perm :
  forall defs m b ofs k p m'
  (PERM: Mem.perm m b ofs k p)
  (ALLOC: alloc_globals m defs = Some m'),
    Mem.perm m' b ofs k p.
Proof.
  induction defs; intros; simpl in *.
  - inv ALLOC. auto.
  - destr_in ALLOC.
    eapply (IHdefs m0); eauto.
    eapply alloc_global_pres_perm; eauto.
Qed.

Lemma init_mem_genv_next: forall (p: program) m,
  init_mem p = Some m ->
  Genv.genv_next (globalenv p) = Mem.nextblock m.
Proof.
  unfold init_mem; intros.
  destruct (Mem.alloc Mem.empty 0 0) eqn:ALLOC.
  destr_match_in H; inv H.
  exploit alloc_globals_nextblock; eauto. 
  exploit Mem.nextblock_alloc; eauto. rewrite Mem.nextblock_empty. 
  erewrite alloc_segments_nextblock'; eauto. simpl.
  intros. rewrite H in H0. simpl in H0.
  erewrite store_globals_nextblock; eauto.
  rewrite H0. unfold globalenv. simpl.
  rewrite add_globals_next_block. simpl. auto.
Qed.

Lemma add_global_pres_instrs : forall ge def,
    Genv.genv_instrs (add_global ge def) = Genv.genv_instrs ge.
Proof.
  intros. destruct def.
  destruct p. simpl. auto.
Qed.

Lemma add_globals_pres_instrs : forall defs ge,
    Genv.genv_instrs (add_globals ge defs) = Genv.genv_instrs ge.
Proof.
  induction defs; simpl; intros.
  - auto.
  - rewrite IHdefs. 
    eapply add_global_pres_instrs; eauto.
Qed.

Definition def_is_var_or_internal_fun  (def: (ident * option gdef * segblock)) := 
  let '(_,d,_) := def in
  (exists v, d = Some (Gvar v)) \/ (exists f, d = (Some (Gfun (Internal f)))).

Definition defs_is_var_or_internal_fun (i:ident) (defs: list (ident * option gdef * segblock)) :=
  forall def sb, In (i, def, sb) defs -> def_is_var_or_internal_fun (i, def, sb).
                                                    
Lemma add_global_pres_find_symbol : forall def ge i,
  def_is_var_or_internal_fun def ->
  Genv.find_symbol (add_global ge def) i = Genv.find_symbol ge i.
Proof.
  intros. destruct def. destruct p. simpl.
  destruct o. destruct g. destruct f.
  - auto.
  - destruct ident_eq. 
    + subst. inv H. inv H0. inv H. inv H0. inv H.
    + auto.
  - auto.
  - destruct ident_eq.
    + subst. inv H. inv H0. inv H. inv H0. inv H.
    + auto.
Qed.

Lemma add_globals_pres_find_symbol : forall defs ge i,
  defs_is_var_or_internal_fun i defs ->
  Genv.find_symbol (add_globals ge defs) i = Genv.find_symbol ge i.
Proof.
  induction defs; intros; simpl.
  - auto.
  - assert (defs_is_var_or_internal_fun i defs).
    red. intros. apply H. apply in_cons. auto.
    exploit (IHdefs (add_global ge a) i); eauto.
    intros FS. rewrite FS.
    destruct a. destruct p.
    destruct (ident_eq i i0).
    + subst. 
      apply add_global_pres_find_symbol. 
      apply H. apply in_eq.
    + unfold add_global. simpl.
      destruct o. destruct g. destruct f.
      * auto.
      * destruct ident_eq. contradiction. auto.
      * auto.
      * destruct ident_eq. contradiction. auto.
Qed.

Lemma add_global_pres_internal_block : forall def ge b,
  Genv.genv_internal_codeblock (add_global ge def) b = Genv.genv_internal_codeblock ge b.
Proof.
  destruct def. destruct p. simpl. intros. auto.
Qed.

Lemma add_globals_pres_internal_block : forall defs ge ge' b,
  add_globals ge defs = ge' ->
  Genv.genv_internal_codeblock ge' b = Genv.genv_internal_codeblock ge b.
Proof.
  induction defs; intros; subst; simpl.
  - auto.
  - erewrite (IHdefs (add_global ge a)); eauto. erewrite add_global_pres_internal_block; eauto.
Qed.

Lemma add_global_pres_find_symbol_neq : forall ge i o s i1,
  i <> i1 ->
  Genv.find_symbol (add_global ge (i, o, s)) i1 = Genv.find_symbol ge i1.
Proof.
  intros. 
  destruct o; simpl. 
  destruct g; simpl. 
  destruct f; simpl.
  auto.
  rewrite peq_false; auto.
  auto.
  rewrite peq_false; auto.
Qed.

Lemma add_globals_pres_find_symbol_not_in : 
  forall defs i ge
    (NIN: ~In i (map (fun '(i,_,_) => i) defs)),
    Genv.find_symbol (add_globals ge defs) i = Genv.find_symbol ge i.
Proof.
  induction defs; simpl; intros. auto.
  destruct a. destruct p. destruct (peq i i0).
  - subst. exfalso. apply NIN. auto.
  - erewrite IHdefs; eauto. 
    eapply add_global_pres_find_symbol_neq; eauto.
Qed.

Definition def_is_none_or_external_fun  (def: (ident * option gdef * segblock)) := 
  let '(_,d,_) := def in
  d = None \/ (exists f, d = (Some (Gfun (External f)))).


Lemma add_global_find_symbol_eq:
  forall (ge : genv) (i : ident) (o : option gdef) (s : segblock) (i1 : ident)
  (NE: def_is_none_or_external_fun (i, o, s)),
  Genv.find_symbol (add_global ge (i, o, s)) i = Some (Genv.genv_next ge, Ptrofs.zero).
Proof.
  intros. destruct o. destruct g. destruct f.
  - simpl. inv NE. inv H. inv H. inv H0.
  - simpl. rewrite peq_true. eauto.
  - simpl. inv NE. inv H. inv H. inv H0.
  - simpl. rewrite peq_true. eauto.
Qed.

Inductive Nth {A :Type} : nat -> list A -> A -> Prop :=
| Nth_base: forall x l, Nth O (x::l) x
| Nth_cons: forall n x y l, Nth n l x -> Nth (Coq.Init.Datatypes.S n) (y::l) x.

Lemma add_globals_find_symbol_ne : forall defs x def sb n ge
    (NE: def_is_none_or_external_fun (x, def, sb))
    (NTH: Nth n defs (x,def,sb))
    (NPT: list_norepet (map (fun '(i,_,_) => i) defs)),
    Genv.find_symbol (add_globals ge defs) x = Some (pos_advance_N (Genv.genv_next ge) n, Ptrofs.zero).
Proof.
  induction defs; intros; simpl. inv NTH. inv NTH.
  - inv NPT.
    erewrite add_globals_pres_find_symbol_not_in; eauto.
    apply add_global_find_symbol_eq; eauto.
  - inv NPT.
    erewrite IHdefs; eauto. 
    rewrite add_global_next_block. auto.
Qed.
      

Lemma In_Nth: forall (A : Type) (l : list A) (x : A), 
    In x l -> exists n : nat, (n < length l)%nat /\ Nth n l x.
Proof.
  induction l; simpl; intros. contradiction. inv H.
  - exists O. split. omega. constructor.
  - apply IHl in H0. destruct H0 as (n' & LT & NTH).
    exists (Datatypes.S n'). split. omega. constructor. auto.
Qed.

Lemma add_global_pres_lbl:
  forall (def : ident * option gdef * segblock) (ge : genv) (b : block),
    Genv.genv_lbl (add_global ge def) b = Genv.genv_lbl ge b.
Proof.
  intros. destruct def. destruct p. destruct o. destruct g. destruct f.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
Qed.
    
Lemma add_globals_pres_lbl:
  forall (defs : list (ident * option gdef * segblock)) (ge : genv) (b : block),
    Genv.genv_lbl (add_globals ge defs) b = Genv.genv_lbl ge b.
Proof.
  induction defs; simpl; intros.
  - auto.
  - erewrite IHdefs; eauto. apply add_global_pres_lbl.
Qed.

Lemma genv_internal_codeblock_add_global:
  forall g def,
    Genv.genv_internal_codeblock (add_global g def) = Genv.genv_internal_codeblock g.
Proof.
  unfold add_global. intros. destruct def. destruct p. simpl. auto.
Qed.

Lemma genv_internal_codeblock_add_globals:
  forall l g,
    Genv.genv_internal_codeblock (add_globals g l) = Genv.genv_internal_codeblock g.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl. 
  rewrite genv_internal_codeblock_add_global.
  auto.
Qed.

Lemma add_global_pres_find_def_blt : forall b ge def ofs,
  Pos.lt b (Genv.genv_next ge) ->
  Genv.find_def (add_global ge def) b ofs = Genv.find_def ge b ofs.
Proof.
  intros. 
  destruct def; simpl.
  destruct p; simpl.
  destruct o; simpl. 
  destruct g; simpl.
  destruct f; simpl.
  - auto.
  - destruct eq_block. 
    + subst. exfalso. eapply Pos.lt_irrefl; eauto.
    + simpl. auto.
  - auto.
  - destruct eq_block. 
    + subst. exfalso. eapply Pos.lt_irrefl; eauto.
    + simpl. auto.
Qed.

Lemma add_globals_pres_find_def: forall defs ge b ofs,
    Pos.lt b (Genv.genv_next ge) ->
    Genv.find_def (add_globals ge defs) b ofs = Genv.find_def ge b ofs.
Proof.
  induction defs; simpl; intros. auto.
  erewrite IHdefs; eauto.
  eapply add_global_pres_find_def_blt; eauto.
  rewrite add_global_next_block.
  eapply Pos.lt_lt_succ; eauto.
Qed.

Lemma unique_def_is_internal_fun : forall defs i f sb
  (NPT: list_norepet (map (fun '(i,_,_) => i) defs))
  (IN: In (i, Some (Gfun (Internal f)), sb) defs),
  defs_is_var_or_internal_fun i defs.
Proof.
  induction defs; intros; simpl; inv IN.
  - inv NPT. red. intros def sb0 H.
    inv H. inv H0. red. eauto.
    generalize (in_map (fun '(i,_,_) => i) defs (i,def,sb0) H0). contradiction.
  - destruct a. destruct p. inv NPT.
    red. intros def sb0 IN. inv IN. 
    + inv H0.
      generalize (in_map (fun '(i,_,_) => i) defs (i,Some (Gfun (Internal f)),sb) H). contradiction.
    + exploit IHdefs; eauto.
Qed.

Lemma unique_def_is_var : forall defs i v sb
  (NPT: list_norepet (map (fun '(i,_,_) => i) defs))
  (IN: In (i, Some (Gvar v), sb) defs),
  defs_is_var_or_internal_fun i defs.
Proof.
  induction defs; intros; simpl; inv IN.
  - inv NPT. red. intros def sb0 H.
    inv H. inv H0. red. eauto.
    generalize (in_map (fun '(i,_,_) => i) defs (i,def,sb0) H0). contradiction.
  - destruct a. destruct p. inv NPT.
    red. intros def sb0 IN. inv IN. 
    + inv H0.
      generalize (in_map (fun '(i,_,_) => i) defs (i,Some (Gvar v),sb) H). contradiction.
    + exploit IHdefs; eauto.
Qed.


End WITHEXTERNALCALLS.

End SEGPROG.
