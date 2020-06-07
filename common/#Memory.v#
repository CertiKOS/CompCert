(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Export Memdata.
Require Export MemPerm.
Require Export Memtype.
Require Export StackADT.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Module Mem <: MEM.

(*SACC:*)
Parameter stack_limit' : Z.
Definition stack_limit := 
  Z.max 8 ((align stack_limit' 8) mod (Ptrofs.modulus - align (size_chunk Mptr) 8)).

(* Original CompCert *)
(*X*)
Definition perm_order' (po: option permission) (p: permission) :=
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

(*X*)
Definition perm_order'' (po1 po2: option permission) :=
  match po1, po2 with
  | Some p1, Some p2 => perm_order p1 p2
  | _, None => True
  | None, Some _ => False
 end.

(*SACC: Stack Invariant*)
Record stack_inv (s: StackADT.stack) (thr: block) (P: perm_type) : Prop :=
  {
    stack_inv_valid': forall b, in_stack_all s b -> Plt b thr;
    stack_inv_norepet: nodup s;
    stack_inv_perms: stack_agree_perms P s;
    stack_inv_below_limit: size_stack s < stack_limit;
    stack_inv_wf: wf_stack P s;
  }.

(*SACC: Weakening of stack_inv_valid'*)
Lemma stack_inv_valid s thr P (SI: stack_inv s thr P): forall b, in_stack s b -> Plt b thr.
Proof.
  intros; eapply stack_inv_valid'; eauto using in_stack_in_stack_all.
Qed.

(*SACC:*)
Definition in_bounds (o: Z) (bnds: Z*Z) :=
  fst bnds <= o < snd bnds.

(*X*)
Record mem' : Type := mkmem {
  (*Original CompCert:*)
  mem_contents: PMap.t (ZMap.t memval);  (**r [block -> offset -> memval] *)
  mem_access: PMap.t (Z -> perm_kind -> option permission); (**r [block -> offset -> kind -> option permission] *)

  nextblock: block;
  access_max:
    forall b ofs, perm_order'' (mem_access#b ofs Max) (mem_access#b ofs Cur);
  nextblock_noaccess:
    forall b ofs k, ~(Plt b nextblock) -> mem_access#b ofs k = None;
  contents_default:
    forall b, fst mem_contents#b = Undef;

  (*SACC:*)
  contents_default':
    fst mem_contents = ZMap.init Undef;
  stack:
    StackADT.stack;
  mem_stack_inv:
    stack_inv stack nextblock (fun b o k p => perm_order' ((mem_access#b) o k) p);
  mem_bounds: PMap.t (Z*Z);
  mem_bounds_perm: forall b o k p,
      perm_order' ((mem_access#b) o k) p ->
      in_bounds o (mem_bounds#b);
}.

(*X*)
Definition mem := mem'.

(*X*)
Lemma mkmem_ext:
 forall cont1 cont2 acc1 acc2 next1 next2 a1 a2 b1 b2 c1 c2
  c1' c2' adt1 adt2 sinv1 sinv2 bnd1 bnd2 bndpf1 bndpf2,
  cont1=cont2 -> acc1=acc2 -> next1=next2 ->
  adt1 = adt2 -> bnd1 = bnd2 ->
  mkmem cont1 acc1 next1 a1 b1 c1 c1' adt1 sinv1 bnd1 bndpf1 = 
  mkmem cont2 acc2 next2 a2 b2 c2 c2' adt2 sinv2 bnd2 bndpf2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

(** * Validity of blocks and accesses *)

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

(*X*)
Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

(*X*)
Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Local Hint Resolve valid_not_valid_diff: mem.

(** Permissions *)

Definition perm (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission) : Prop :=
   perm_order' (m.(mem_access)#b ofs k) p.

(*X*)
Theorem perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (m.(mem_access)#b ofs k); auto.
  eapply perm_order_trans; eauto.
Qed.

Local Hint Resolve perm_implies: mem.

(*X*)
Theorem perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Proof.
  assert (forall po1 po2 p,
          perm_order' po2 p -> perm_order'' po1 po2 -> perm_order' po1 p).
  unfold perm_order', perm_order''. intros.
  destruct po2; try contradiction.
  destruct po1; try contradiction.
  eapply perm_order_trans; eauto.
  unfold perm; intros.
  generalize (access_max m b ofs). eauto.
Qed.

(*X*)
Theorem perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

(*X*)
Theorem perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Local Hint Resolve perm_cur perm_max: mem.

(*X*)
Theorem perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.
Proof.
  unfold perm; intros.
  destruct (plt b m.(nextblock)).
  auto.
  assert (m.(mem_access)#b ofs k = None).
  eapply nextblock_noaccess; eauto.
  rewrite H0 in H.
  contradiction.
Qed.

Local Hint Resolve perm_valid_block: mem.

(*X*)
Remark perm_order_dec:
  forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
Proof.
  intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
Defined.

(*X*)
Remark perm_order'_dec:
  forall op p, {perm_order' op p} + {~perm_order' op p}.
Proof.
  intros. destruct op; unfold perm_order'.
  apply perm_order_dec.
  right; tauto.
Defined.

(*X*)
Theorem perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Defined.

(*X*)
Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

(*X*)
Theorem range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

(*X*)
Theorem range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

(*X*)
Theorem range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Local Hint Resolve range_perm_implies range_perm_cur range_perm_max: mem.

(*X*)
Lemma range_perm_dec:
  forall m b lo hi k p, {range_perm m b lo hi k p} + {~ range_perm m b lo hi k p}.
Proof.
  intros.
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi).
  destruct (perm_dec m b lo k p).
  destruct (H (lo + 1)). red. omega.
  left; red; intros. destruct (zeq lo ofs). congruence. apply r. omega.
  right; red; intros. elim n. red; intros; apply H0; omega.
  right; red; intros. elim n. apply H0. omega.
  left; red; intros. omegaContradiction.
Defined.

(* SACC Prelude *)

(*SACC: Alignement properties of stack_limit*)

Remark zle_zlt:
  forall lo hi o,
    zle lo o && zlt o hi = true <-> lo <= o < hi.
Proof.
  intros.
  destruct (zle lo o), (zlt o hi); intuition; try congruence; try omega.
Qed.

Theorem stack_limit_range: 0 < stack_limit <= Ptrofs.max_unsigned.
Proof.
  unfold stack_limit.
  rewrite Zmax_spec. destr. vm_compute. intuition congruence.
  split. omega.
  eapply Z.lt_le_incl, Z.lt_le_trans. apply Z_mod_lt. unfold Mptr; destr; vm_compute; auto.
  unfold Ptrofs.max_unsigned. apply Z.sub_le_mono_l. unfold Mptr; destr; simpl; vm_compute; congruence.
Qed.

Theorem stack_limit_range': stack_limit + align (size_chunk Mptr) 8 <= Ptrofs.max_unsigned.
Proof.
  unfold stack_limit.
  rewrite Zmax_spec. destr. vm_compute. intuition congruence.
  generalize (Z_mod_lt (align stack_limit' 8) (Ptrofs.modulus - align (size_chunk Mptr) 8)).
  intro A; trim A. vm_compute. auto. unfold Ptrofs.max_unsigned. omega.
Qed.

Remark mod_divides:
  forall a b c,
    c <> 0 ->
    (a | c) ->
    (a | b) ->
    (a | b mod c).
Proof.
  intros.
  rewrite Zmod_eq_full.
  apply Z.divide_sub_r. auto.
  apply Z.divide_mul_r. auto. auto.
Qed.

Theorem stack_limit_aligned: (8 | stack_limit).
Proof.
  unfold stack_limit.
  rewrite Zmax_spec. destr. exists 1; omega.
  apply mod_divides. vm_compute. congruence.
  apply Z.divide_sub_r.
  rewrite Ptrofs.modulus_power.
  exists (two_p (Ptrofs.zwordsize - 3)). change 8 with (two_p 3). rewrite <- two_p_is_exp. f_equal. vm_compute. congruence. omega.
  apply align_divides. omega.
  apply align_divides. omega.
Qed.

(* SACC: Basic Stack Properties *)

Theorem stack_norepet:
  forall m,
  nodup (stack m).
Proof.
  intros. apply (mem_stack_inv m).
Qed.

Theorem stack_perm:
  forall m,
  stack_agree_perms (perm m) (stack m).
Proof.
  destruct m. simpl. 
  eapply stack_inv_perms; eauto.
Qed.

Hint Resolve stack_norepet stack_perm.

Theorem in_stack_valid:
  forall m b, in_stack (stack m) b -> valid_block m b.
Proof.
  intros; eapply stack_inv_valid; eauto using mem_stack_inv.
Qed.

Remark in_tframes_in_stack_all:
  forall s f a b,
    In f (snd a) ->
    In a s ->
    in_frame f b ->
    in_stack_all s b.
Proof.
  induction s; simpl; intros; eauto.
  destruct H0; subst.
  - left. red. right. eauto.
  - right; eauto.
Qed.

Lemma stack_inv_alloc:
  forall m lo hi,
    stack_inv (stack m) (Pos.succ (nextblock m))
              (fun (b : block) (o : Z) (k : perm_kind) (p : permission) =>
                 perm_order'
                   ((PMap.set (nextblock m) (fun (ofs : Z) (_ : perm_kind) => if zle lo ofs && zlt ofs hi then Some Freeable else None) (mem_access m))
                      # b o k) p).
Proof.
  intros m lo hi.
  destruct (mem_stack_inv m).
  constructor; simpl; intros; eauto.
  - eapply stack_inv_valid'0 in H. xomega.
  - generalize (stack_perm m). unfold stack_agree_perms.
    intros F x IN f AIN b fi o k p INB PERM.
    rewrite PMap.gso in PERM; eauto.
    + eapply F; eauto.
    + intro; subst. 
      exploit in_frames_in_stack; eauto.
      eapply in_frame_in_frames; eauto.
      eapply in_frame_blocks_in_frame; eauto.
      intro INS. apply in_stack_valid in INS.
      unfold valid_block in INS.
      xomega.
  - eapply Forall_impl. 2: apply stack_inv_wf0.
    red; intros. intro P. rewrite PMap.gso in P; eauto. eapply H0; eauto.
    intro; subst.
    rewrite PMap.gss in P.
    destr_in P.
    exploit stack_inv_valid'0.
    eapply in_tframes_in_stack_all; eauto. xomega.
Qed.

Remark stack_inv_free:
  forall m (P: perm_type),
    (forall b o k p, P b o k p -> perm m b o k p) ->
    stack_inv (stack m) (nextblock m) P.
Proof.
  intros m P PERMS.
  destruct (mem_stack_inv m).
  constructor; auto.
  - red.
    red.
    intros tf INS f AIN b fi o k p INFR PERM.
    eapply stack_inv_perms0; eauto.
    eapply PERMS; eauto.
  - eapply Forall_impl. 2: eauto.
    intros a INS WTF b fr IFRS INFR o k p PERM.
    eapply WTF; eauto.
    eapply PERMS; eauto.
Qed.

(** [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with current permissions [p].
    This means:
- The range of bytes accessed all have current permission [p].
- The offset [ofs] is aligned.
*)

(*X*)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs).

(*X*)
Theorem valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.
Proof.
  intros. inv H. constructor; eauto with mem.
Qed.

(*X*)
Theorem valid_access_freeable_any:
  forall m chunk b ofs p,
  valid_access m chunk b ofs Freeable ->
  valid_access m chunk b ofs p.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Local Hint Resolve valid_access_implies: mem.

(*X*)
Theorem valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.
Proof.
  intros. destruct H.
  assert (perm m b ofs Cur Nonempty).
    apply H. generalize (size_chunk_pos chunk). omega.
  eauto with mem.
Qed.

Local Hint Resolve valid_access_valid_block: mem.

(*X*)
Lemma valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p.
Proof.
  intros. destruct H. apply perm_cur. apply H. generalize (size_chunk_pos chunk). omega.
Qed.

(*X*)
Lemma valid_access_compat:
  forall m chunk1 chunk2 b ofs p,
  size_chunk chunk1 = size_chunk chunk2 ->
  align_chunk chunk2 <= align_chunk chunk1 ->
  valid_access m chunk1 b ofs p->
  valid_access m chunk2 b ofs p.
Proof.
  intros. inv H1. rewrite H in H2. constructor; auto.
  eapply Zdivide_trans; eauto. eapply align_le_divides; eauto.
Qed.

(*X*)
Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Proof.
  intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur p).
  destruct (Zdivide_dec (align_chunk chunk) ofs (align_chunk_pos chunk)).
  left; constructor; auto.
  right; red; intro V; inv V; contradiction.
  right; red; intro V; inv V; contradiction.
Defined.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
(*X*)
Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool :=
  perm_dec m b ofs Cur Nonempty.

(*X*)
Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Proof.
  intros. unfold valid_pointer.
  destruct (perm_dec m b ofs Cur Nonempty); simpl;
  intuition congruence.
Qed.

(*X*)
Theorem valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.
Proof.
  intros. rewrite valid_pointer_nonempty_perm.
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by omega. auto.
  simpl. apply Zone_divide.
  destruct H. apply H. simpl. omega.
Qed.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

(*X*)
Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

(*X*)
Lemma weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Proof.
  intros. unfold weak_valid_pointer. now rewrite orb_true_iff.
Qed.
(*X*)
Lemma valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.
Proof.
  intros. apply weak_valid_pointer_spec. auto.
Qed.

(** * Operations over memory stores *)

(** The initial store *)

(*X*)
Program Definition empty: mem :=
  mkmem (PMap.init (ZMap.init Undef))
        (PMap.init (fun ofs k => None))
        1%positive _ _ _ _ nil _ (PMap.init (0,0)) _.
Next Obligation.
  repeat rewrite PMap.gi. red; auto.
Qed.
Next Obligation.
  rewrite PMap.gi. auto.
Qed.
Next Obligation.
  rewrite PMap.gi. auto.
Qed.
Next Obligation.
  repeat constructor; try easy.
  apply stack_limit_range.
Qed.
Next Obligation.
  rewrite PMap.gi in H. inv H.
Qed.

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

(*X*)
Program Definition alloc (m: mem) (lo hi: Z) :=
  (mkmem (PMap.set m.(nextblock)
                   (ZMap.init Undef)
                   m.(mem_contents))
         (PMap.set m.(nextblock)
                   (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                   m.(mem_access))
         (Psucc m.(nextblock))
         _ _ _ _ (stack m) _ (PMap.set m.(nextblock) (lo, hi) m.(mem_bounds)) _,
   m.(nextblock)).
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b (nextblock m)).
  subst b. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
  apply access_max.
Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b (nextblock m)).
  subst b. elim H. apply Plt_succ.
  apply nextblock_noaccess. red; intros; elim H.
  apply Plt_trans_succ; auto.
Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b (nextblock m)). auto. apply contents_default.
Qed.
Next Obligation.
  apply contents_default'.
Qed.
Next Obligation.
  apply stack_inv_alloc.
Qed.
Next Obligation.
  rewrite PMap.gsspec in *.
  destr. destr_in H. apply zle_zlt in Heqb0. red. simpl. apply Heqb0.
  inv H.
  eapply mem_bounds_perm; eauto.
Qed.

(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires freeable permission on the given range. *)


(*X*)
Program Definition unchecked_free (m: mem) (b: block) (lo hi: Z): mem :=
  mkmem m.(mem_contents)
        (PMap.set b
                (fun ofs k => if zle lo ofs && zlt ofs hi then None else m.(mem_access)#b ofs k)
                m.(mem_access))
        m.(nextblock) _ _ _ _ (stack m) _ m.(mem_bounds) _.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b).
  destruct (zle lo ofs && zlt ofs hi). red; auto. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst.
  destruct (zle lo ofs && zlt ofs hi). auto. apply nextblock_noaccess; auto.
  apply nextblock_noaccess; auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  apply contents_default'.
Qed.
Next Obligation.
  apply stack_inv_free.
  unfold perm.
  intros b0 o k p P.
  rewrite PMap.gsspec in P. destr_in P. subst.
  repeat destr_in P.
Qed.
Next Obligation.
  rewrite PMap.gsspec in *. repeat destr_in H. subst.
  eapply mem_bounds_perm; eauto.
  eapply mem_bounds_perm; eauto.
Qed.

(*X*)
Definition free (m: mem) (b: block) (lo hi: Z): option mem :=
  if range_perm_dec m b lo hi Cur Freeable
  then Some(unchecked_free m b lo hi)
  else None.

(*X*)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

(*X*)
Fixpoint getN (n: nat) (p: Z) (c: ZMap.t memval) {struct n}: list memval :=
  match n with
  | O => nil
  | S n' => ZMap.get p c :: getN n' (p + 1) c
  end.

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. *)

(*X*)
Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option val :=
  if valid_access_dec m chunk b ofs Readable
  then Some(decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)))
  else None.

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

(*X*)
Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end.

(** [loadbytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

(*X*)
Definition loadbytes (m: mem) (b: block) (ofs n: Z): option (list memval) :=
  if range_perm_dec m b ofs (ofs + n) Cur Readable
  then Some (getN (nat_of_Z n) ofs (m.(mem_contents)#b))
  else None.

(** Memory stores. *)

(** Writing N adjacent bytes in a block content. *)

(*X*)
Fixpoint setN (vl: list memval) (p: Z) (c: ZMap.t memval) {struct vl}: ZMap.t memval :=
  match vl with
  | nil => c
  | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)
  end.

(*X*)
Remark setN_other:
  forall vl c p q,
  (forall r, p <= r < p + Z_of_nat (length vl) -> r <> q) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  induction vl; intros; simpl.
  auto.
  simpl length in H. rewrite inj_S in H.
  transitivity (ZMap.get q (ZMap.set p a c)).
  apply IHvl. intros. apply H. omega.
  apply ZMap.gso. apply not_eq_sym. apply H. omega.
Qed.

(*X*)
Remark setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z_of_nat (length vl) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  intros. apply setN_other.
  intros. omega.
Qed.

(*X*)
Remark getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq.
  rewrite setN_outside. apply ZMap.gss. omega.
  apply IHvl.
Qed.

(*X*)
Remark getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z_of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite inj_S in H. simpl. decEq.
  apply H. omega. apply IHn. intros. apply H. omega.
Qed.

(*X*)
Remark getN_setN_disjoint:
  forall vl q c n p,
  Intv.disjoint (p, p + Z_of_nat n) (q, q + Z_of_nat (length vl)) ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_exten. intros. apply setN_other.
  intros; red; intros; subst r. eelim H; eauto.
Qed.

(*X*)
Remark getN_setN_outside:
  forall vl q c n p,
  p + Z_of_nat n <= q \/ q + Z_of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_setN_disjoint. apply Intv.disjoint_range. auto.
Qed.

(*X*)
Remark setN_default:
  forall vl q c, fst (setN vl q c) = fst c.
Proof.
  induction vl; simpl; intros. auto. rewrite IHvl. auto.
Qed.

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

(*X*)
Program Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val): option mem :=
  if valid_access_dec m chunk b ofs Writable then
    Some (mkmem (PMap.set b
                          (setN (encode_val chunk v) ofs (m.(mem_contents)#b))
                          m.(mem_contents))
                m.(mem_access)
                m.(nextblock)
                _ _ _ _ (stack m) _ m.(mem_bounds) _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation.
  apply contents_default'.
Qed.
Next Obligation.
  destruct m; eauto.
Qed.
Next Obligation.
  eapply mem_bounds_perm; eauto.
Qed.

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

(*X*)
Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => None
  end.

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

(*X*)
Program Definition storebytes (m: mem) (b: block) (ofs: Z) (bytes: list memval) : option mem :=
  if range_perm_dec m b ofs (ofs + Z_of_nat (length bytes)) Cur Writable then
    Some (mkmem
             (PMap.set b (setN bytes ofs (m.(mem_contents)#b)) m.(mem_contents))
             m.(mem_access)
             m.(nextblock)
             _ _ _ _ (stack m) _ m.(mem_bounds) _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation.
  apply contents_default'.
Qed.
Next Obligation.
  destruct m; auto.
Qed.
Next Obligation.
  eapply mem_bounds_perm; eauto.
Qed.

(** [drop_perm m b lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

(*X*)
Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m b lo hi Cur Freeable then
    Some (mkmem m.(mem_contents)
                (PMap.set b
                        (fun ofs k => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access)#b ofs k)
                        m.(mem_access))
                m.(nextblock) _ _ _ _ (stack m) _ m.(mem_bounds) _)
  else None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs && zlt ofs hi). red; auto with mem. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  specialize (nextblock_noaccess m b0 ofs k H0). intros.
  rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi).
  assert (perm m b ofs k Freeable). apply perm_cur. apply H; auto.
  unfold perm in H2. rewrite H1 in H2. contradiction.
  auto. auto. auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  apply contents_default'.
Qed.
Next Obligation.
  apply stack_inv_free; auto.
  unfold perm.
  intros b0 o k pp P.
  rewrite PMap.gsspec in P. destr_in P. subst.
  destr_in P.
  eapply perm_cur,perm_implies. apply H. apply zle_zlt; auto. constructor.
Qed.
Next Obligation.
  rewrite PMap.gsspec in H0.
  destr_in H0. destr_in H0. subst. eapply mem_bounds_perm; eauto. apply H.
  apply zle_zlt; auto.
  subst. eapply mem_bounds_perm; eauto.
  eapply mem_bounds_perm; eauto.
Qed.

(** * Properties of the memory operations *)

(** Properties of the empty store. *)

(*X*)
Theorem nextblock_empty: nextblock empty = 1%positive.
Proof. reflexivity. Qed.

(*X*)
Theorem perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Proof.
  intros. unfold perm, empty; simpl. rewrite PMap.gi. simpl. tauto.
Qed.

(*X*)
Theorem valid_access_empty: forall chunk b ofs p, ~valid_access empty chunk b ofs p.
Proof.
  intros. red; intros. elim (perm_empty b ofs Cur p). apply H.
  generalize (size_chunk_pos chunk); omega.
Qed.

(** ** Properties related to [load] *)

(*X*)
Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto.
Qed.

(*X*)
Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  auto.
  congruence.
Qed.

(*X*)
Lemma load_result:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  v = decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)).
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  congruence.
  congruence.
Qed.

Local Hint Resolve load_valid_access valid_access_load: mem.

(*X*)
Theorem load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_type.
Qed.

(*X*)
Theorem load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs m.(mem_contents)#b).
  intros. subst v. apply decode_val_cast.
Qed.

(*X*)
Theorem load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := getN (size_chunk_nat Mint8unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint8signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

(*X*)
Theorem load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint16signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

(** ** Properties related to [loadbytes] *)

(*X*)
Theorem range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto.
Qed.

(*X*)
Theorem loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.
Proof.
  intros until bytes. unfold loadbytes.
  destruct (range_perm_dec m b ofs (ofs + len) Cur Readable). auto. congruence.
Qed.

(*X*)
Theorem loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur Readable);
  try congruence.
  inv H. rewrite pred_dec_true. auto.
  split; auto.
Qed.

(*X*)
Theorem load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.
Proof.
  intros. exploit load_valid_access; eauto. intros [A B].
  exploit load_result; eauto. intros.
  exists (getN (size_chunk_nat chunk) ofs m.(mem_contents)#b); split.
  unfold loadbytes. rewrite pred_dec_true; auto.
  auto.
Qed.

(*X*)
Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

(*X*)
Theorem loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable); try congruence.
  inv H. apply getN_length.
Qed.

(*X*)
Theorem loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil.
Proof.
  intros. unfold loadbytes. rewrite pred_dec_true. rewrite nat_of_Z_neg; auto.
  red; intros. omegaContradiction.
Qed.

(*X*)
Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z_of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. omega.
  rewrite inj_S. simpl. decEq.
  replace (p + Zsucc (Z_of_nat n1)) with ((p + 1) + Z_of_nat n1) by omega.
  auto.
Qed.

(*X*)
Theorem loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n1) Cur Readable); try congruence.
  destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Cur Readable); try congruence.
  rewrite pred_dec_true. rewrite nat_of_Z_plus; auto.
  rewrite getN_concat. rewrite nat_of_Z_eq; auto.
  congruence.
  red; intros.
  assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by omega.
  destruct H4. apply r; omega. apply r0; omega.
Qed.

(*X*)
Theorem loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable);
  try congruence.
  rewrite nat_of_Z_plus in H; auto. rewrite getN_concat in H.
  rewrite nat_of_Z_eq in H; auto.
  repeat rewrite pred_dec_true.
  econstructor; econstructor.
  split. reflexivity. split. reflexivity. congruence.
  red; intros; apply r; omega.
  red; intros; apply r; omega.
Qed.

(*X*)
Theorem load_rep:
 forall ch m1 m2 b ofs v1 v2,
  (forall z, 0 <= z < size_chunk ch -> ZMap.get (ofs + z) m1.(mem_contents)#b = ZMap.get (ofs + z) m2.(mem_contents)#b) ->
  load ch m1 b ofs = Some v1 ->
  load ch m2 b ofs = Some v2 ->
  v1 = v2.
Proof.
  intros.
  apply load_result in H0.
  apply load_result in H1.
  subst.
  f_equal.
  rewrite size_chunk_conv in H.
  remember (size_chunk_nat ch) as n; clear Heqn.
  revert ofs H; induction n; intros; simpl; auto.
  f_equal.
  rewrite inj_S in H.
  replace ofs with (ofs+0) by omega.
  apply H; omega.
  apply IHn.
  intros.
  rewrite <- Zplus_assoc.
  apply H.
  rewrite inj_S. omega.
Qed.

(*X*)
Theorem load_int64_split:
  forall m b ofs v,
  load Mint64 m b ofs = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     load Mint32 m b ofs = Some (if Archi.big_endian then v1 else v2)
  /\ load Mint32 m b (ofs + 4) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros.
  exploit load_valid_access; eauto. intros [A B]. simpl in *.
  exploit load_loadbytes. eexact H. simpl. intros [bytes [LB EQ]].
  change 8 with (4 + 4) in LB.
  exploit loadbytes_split. eexact LB. omega. omega.
  intros (bytes1 & bytes2 & LB1 & LB2 & APP).
  change 4 with (size_chunk Mint32) in LB1.
  exploit loadbytes_load. eexact LB1.
  simpl. apply Zdivides_trans with 8; auto. exists 2; auto.
  intros L1.
  change 4 with (size_chunk Mint32) in LB2.
  exploit loadbytes_load. eexact LB2.
  simpl. apply Zdivide_plus_r. apply Zdivides_trans with 8; auto. exists 2; auto. exists 1; auto.
  intros L2.
  exists (decode_val Mint32 (if Archi.big_endian then bytes1 else bytes2));
  exists (decode_val Mint32 (if Archi.big_endian then bytes2 else bytes1)).
  split. destruct Archi.big_endian; auto.
  split. destruct Archi.big_endian; auto.
  rewrite EQ. rewrite APP. apply decode_val_int64; auto.
  erewrite loadbytes_length; eauto. reflexivity.
  erewrite loadbytes_length; eauto. reflexivity.
Qed.

(*X*)
Lemma addressing_int64_split:
  forall i,
  Archi.ptr64 = false ->
  (8 | Ptrofs.unsigned i) ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4.
Proof.
  intros.
  rewrite Ptrofs.add_unsigned.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 4))) with (Int.unsigned (Int.repr 4))
    by (symmetry; apply Ptrofs.agree32_of_int; auto).
  change (Int.unsigned (Int.repr 4)) with 4. 
  apply Ptrofs.unsigned_repr.
  exploit (Zdivide_interval (Ptrofs.unsigned i) Ptrofs.modulus 8).
  omega. apply Ptrofs.unsigned_range. auto.
  exists (two_p (Ptrofs.zwordsize - 3)).
  unfold Ptrofs.modulus, Ptrofs.zwordsize, Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64; reflexivity.
  unfold Ptrofs.max_unsigned. omega.
Qed.

(*X*)
Theorem loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros. destruct a; simpl in H; inv H.
  exploit load_int64_split; eauto. intros (v1 & v2 & L1 & L2 & EQ).
  unfold Val.add; rewrite H0.
  assert (NV: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4).
  { apply addressing_int64_split; auto. 
    exploit load_valid_access. eexact H2. intros [P Q]. auto. }
  exists v1, v2.
Opaque Ptrofs.repr.
  split. auto.
  split. simpl. rewrite NV. auto.
  auto.
Qed.

(** ** Properties related to [store] *)

(*X*)
Theorem valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros.
  unfold store.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  eauto.
  contradiction.
Defined.

Local Hint Resolve valid_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.

(*X*)
Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

(*X*)
Lemma store_mem_contents:
  mem_contents m2 = PMap.set b (setN (encode_val chunk v) ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

(*X*)
Theorem perm_store_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros.
 unfold perm in *. rewrite store_access; auto.
Qed.

(*X*)
Theorem perm_store_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.

(*X*)
Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

(*X*)
Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store; auto.
Qed.

(*X*)
Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store in H; auto.
Qed.

Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.

(*X*)
Theorem store_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

(*X*)
Theorem store_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

(*X*)
Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable).
  auto.
  congruence.
Qed.

Local Hint Resolve store_valid_access_1 store_valid_access_2 store_valid_access_3: mem.

(*X*)
Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk').
    eapply valid_access_compat. symmetry; eauto. auto. eauto with mem.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B. rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general.
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H.
  apply inj_eq_rev; auto.
Qed.

(*X*)
Theorem load_store_similar_2:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v).
Proof.
  intros. destruct (load_store_similar chunk') as [v' [A B]]; auto.
  rewrite A. decEq. eapply decode_encode_val_similar with (chunk1 := chunk); eauto.
Qed.

(*X*)
Theorem load_store_same:
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Proof.
  apply load_store_similar_2; auto. omega.
Qed.

(*X*)
Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk' b' ofs' Readable).
  rewrite pred_dec_true.
  decEq. decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

(*X*)
Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable) by eauto with mem.
  unfold loadbytes. rewrite pred_dec_true. rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (nat_of_Z (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  apply H.
Qed.

(*X*)
Theorem loadbytes_store_other:
  forall b' ofs' n,
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Cur Readable).
  rewrite pred_dec_true.
  decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  destruct H. congruence.
  destruct (zle n 0) as [z | n0].
  rewrite (nat_of_Z_neg _ z). auto.
  destruct H. omegaContradiction.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite nat_of_Z_eq. auto. omega.
  auto.
  red; intros. eauto with mem.
  rewrite pred_dec_false. auto.
  red; intro; elim n0; red; intros; eauto with mem.
Qed.

(*X*)
Lemma setN_in:
  forall vl p q c,
  p <= q < p + Z_of_nat (length vl) ->
  In (ZMap.get q (setN vl p c)) vl.
Proof.
  induction vl; intros.
  simpl in H. omegaContradiction.
  simpl length in H. rewrite inj_S in H. simpl.
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite ZMap.gss.
  auto with coqlib. omega.
  right. apply IHvl. omega.
Qed.

(*X*)
Lemma getN_in:
  forall c q n p,
  p <= q < p + Z_of_nat n ->
  In (ZMap.get q c) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; omegaContradiction.
  rewrite inj_S in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. omega.
Qed.

End STORE.

Local Hint Resolve perm_store_1 perm_store_2: mem.
Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.
Local Hint Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

(*X*)
Lemma load_store_overlap:
  forall chunk m1 b ofs v m2 chunk' ofs' v',
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b ofs' = Some v' ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  exists mv1 mvl mv1' mvl',
      shape_encoding chunk v (mv1 :: mvl)
  /\  shape_decoding chunk' (mv1' :: mvl') v'
  /\  (   (ofs' = ofs /\ mv1' = mv1)
       \/ (ofs' > ofs /\ In mv1' mvl)
       \/ (ofs' < ofs /\ In mv1 mvl')).
Proof.
  intros.
  exploit load_result; eauto. erewrite store_mem_contents by eauto; simpl.
  rewrite PMap.gss.
  set (c := (mem_contents m1)#b). intros V'.
  destruct (size_chunk_nat_pos chunk) as [sz SIZE].
  destruct (size_chunk_nat_pos chunk') as [sz' SIZE'].
  destruct (encode_val chunk v) as [ | mv1 mvl] eqn:ENC.
  generalize (encode_val_length chunk v); rewrite ENC; simpl; congruence.
  set (c' := setN (mv1::mvl) ofs c) in *.
  exists mv1, mvl, (ZMap.get ofs' c'), (getN sz' (ofs' + 1) c').
  split. rewrite <- ENC. apply encode_val_shape.
  split. rewrite V', SIZE'. apply decode_val_shape.
  destruct (zeq ofs' ofs).
- subst ofs'. left; split. auto. unfold c'. simpl.
  rewrite setN_outside by omega. apply ZMap.gss.
- right. destruct (zlt ofs ofs').
(* If ofs < ofs':  the load reads (at ofs') a continuation byte from the write.
       ofs   ofs'   ofs+|chunk|
        [-------------------]       write
             [-------------------]  read
*)
+ left; split. omega. unfold c'. simpl. apply setN_in.
  assert (Z.of_nat (length (mv1 :: mvl)) = size_chunk chunk).
  { rewrite <- ENC; rewrite encode_val_length. rewrite size_chunk_conv; auto. }
  simpl length in H3. rewrite inj_S in H3. omega.
(* If ofs > ofs':  the load reads (at ofs) the first byte from the write.
       ofs'   ofs   ofs'+|chunk'|
               [-------------------]  write
         [----------------]           read
*)
+ right; split. omega. replace mv1 with (ZMap.get ofs c').
  apply getN_in.
  assert (size_chunk chunk' = Zsucc (Z.of_nat sz')).
  { rewrite size_chunk_conv. rewrite SIZE'. rewrite inj_S; auto. }
  omega.
  unfold c'. simpl. rewrite setN_outside by omega. apply ZMap.gss.
Qed.

(*X*)
Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

(*X*)
Lemma compat_pointer_chunks_true:
  forall chunk1 chunk2,
  (chunk1 = Mint32 \/ chunk1 = Many32 \/ chunk1 = Mint64 \/ chunk1 = Many64) ->
  (chunk2 = Mint32 \/ chunk2 = Many32 \/ chunk2 = Mint64 \/ chunk2 = Many64) ->
  quantity_chunk chunk1 = quantity_chunk chunk2 ->
  compat_pointer_chunks chunk1 chunk2.
Proof.
  intros. destruct H as [P|[P|[P|P]]]; destruct H0 as [Q|[Q|[Q|Q]]];
  subst; red; auto; discriminate.
Qed.

(*X*)
Theorem load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  intros.
  destruct (peq b' b); auto. subst b'.
  destruct (zle (ofs' + size_chunk chunk') ofs); auto.
  destruct (zle (ofs + size_chunk chunk) ofs'); auto.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  inv DEC; try contradiction.
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- (* Same offset *)
  subst. inv ENC.
  assert (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64)
  by (destruct chunk; auto || contradiction).
  left; split. rewrite H3.
  destruct H4 as [P|[P|[P|P]]]; subst chunk'; destruct v0; simpl in H3;
  try congruence; destruct Archi.ptr64; congruence.
  split. apply compat_pointer_chunks_true; auto.
  auto.
- (* ofs' > ofs *)
  inv ENC.
  + exploit H10; eauto. intros (j & P & Q). inv P. congruence.
  + exploit H8; eauto. intros (n & P); congruence.
  + exploit H2; eauto. congruence.
- (* ofs' < ofs *)
  exploit H7; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
Qed.

(*X*)
Theorem load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- congruence.
- inv ENC.
  + exploit H9; eauto. intros (j & P & Q). subst mv1'. inv DEC. congruence. auto.
  + contradiction.
  + exploit H5; eauto. intros; subst. inv DEC; auto.
- inv DEC.
  + exploit H10; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
  + exploit H8; eauto. intros (n & P). subst mv1. inv ENC. contradiction.
  + auto.
Qed.

(*X*)
Theorem load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  generalize (size_chunk_pos chunk'); omega.
  generalize (size_chunk_pos chunk); omega.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]]; try omegaContradiction.
  inv ENC; inv DEC; auto.
- elim H1. apply compat_pointer_chunks_true; auto.
- contradiction.
Qed.

(*X*)
Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 m b ofs,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  align_chunk chunk1 = align_chunk chunk2 ->
  store chunk1 m b ofs v1 = store chunk2 m b ofs v2.
Proof.
  intros. unfold store.
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v2).
    congruence.
  unfold store.
  destruct (valid_access_dec m chunk1 b ofs Writable);
  destruct (valid_access_dec m chunk2 b ofs Writable); auto.
  f_equal. apply mkmem_ext; auto. congruence.
  elim n. apply valid_access_compat with chunk1; auto. omega.
  elim n. apply valid_access_compat with chunk2; auto. omega.
Qed.

(*X*)
Theorem store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. auto. Qed.

(*X*)
Theorem store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. auto. Qed.

(*X*)
Theorem store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_zero_ext. auto. Qed.

(*X*)
Theorem store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_sign_ext. auto. Qed.

(*X*)
Theorem store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_zero_ext. auto. Qed.

(*X*)
Theorem store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_sign_ext. auto. Qed.

(*
Theorem store_float64al32:
  forall m b ofs v m',
  store Mfloat64 m b ofs v = Some m' -> store Mfloat64al32 m b ofs v = Some m'.
Proof.
  unfold store; intros.
  destruct (valid_access_dec m Mfloat64 b ofs Writable); try discriminate.
  destruct (valid_access_dec m Mfloat64al32 b ofs Writable).
  rewrite <- H. f_equal. apply mkmem_ext; auto.
  elim n. apply valid_access_compat with Mfloat64; auto. simpl; omega.
Qed.

Theorem storev_float64al32:
  forall m a v m',
  storev Mfloat64 m a v = Some m' -> storev Mfloat64al32 m a v = Some m'.
Proof.
  unfold storev; intros. destruct a; auto. apply store_float64al32; auto.
Qed.
*)

(** ** Properties related to [storebytes]. *)

(*X*)
Theorem range_perm_storebytes:
  forall m1 b ofs bytes,
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
  exists m2, storebytes m1 b ofs bytes = Some m2.
Proof.
  intros. unfold storebytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable).
  econstructor; reflexivity.
  contradiction.
Defined.

(*X*)
Theorem storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length (encode_val chunk v))) Cur Writable); inv H.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  f_equal. apply mkmem_ext; auto.
  elim n. constructor; auto.
  rewrite encode_val_length in r. rewrite size_chunk_conv. auto.
Qed.

(*X*)
Theorem store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (valid_access_dec m1 chunk b ofs Writable); inv H.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length (encode_val chunk v))) Cur Writable).
  f_equal. apply mkmem_ext; auto.
  destruct v0.  elim n.
  rewrite encode_val_length. rewrite <- size_chunk_conv. auto.
Qed.

Section STOREBYTES.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable bytes: list memval.
Variable m2: mem.
Hypothesis STORE: storebytes m1 b ofs bytes = Some m2.

(*X*)
Lemma storebytes_access: mem_access m2 = mem_access m1.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

(*X*)
Lemma storebytes_mem_contents:
   mem_contents m2 = PMap.set b (setN bytes ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

(*X*)
Theorem perm_storebytes_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access; auto.
Qed.

(*X*)
Theorem perm_storebytes_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access in H; auto.
Qed.

Local Hint Resolve perm_storebytes_1 perm_storebytes_2: mem.

(*X*)
Theorem storebytes_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

(*X*)
Theorem storebytes_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.

(*X*)
Theorem nextblock_storebytes:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

(*X*)
Theorem storebytes_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes; auto.
Qed.

(*X*)
Theorem storebytes_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes in H; auto.
Qed.

Local Hint Resolve storebytes_valid_block_1 storebytes_valid_block_2: mem.

(*X*)
Theorem storebytes_range_perm:
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

(*X*)
Theorem loadbytes_storebytes_same:
  loadbytes m2 b ofs (Z_of_nat (length bytes)) = Some bytes.
Proof.
  intros. assert (STORE2:=STORE). unfold storebytes in STORE2. unfold loadbytes. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  try discriminate.
  rewrite pred_dec_true.
  decEq. inv STORE2; simpl. rewrite PMap.gss. rewrite nat_of_Z_of_nat.
  apply getN_setN_same.
  red; eauto with mem.
Qed.

(*X*)
Theorem loadbytes_storebytes_disjoint:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z_of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + len) Cur Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_disjoint. rewrite nat_of_Z_eq; auto. intuition congruence.
  auto.
  red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. red; auto with mem.
Qed.

(*X*)
Theorem loadbytes_storebytes_other:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. apply loadbytes_storebytes_disjoint; auto.
  destruct H0; auto. right. apply Intv.disjoint_range; auto.
Qed.

(*X*)
Theorem load_storebytes_other:
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk b' ofs' Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence.
  auto.
  destruct v; split; auto. red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. destruct H0. split; auto. red; auto with mem.
Qed.

End STOREBYTES.

(*X*)
Lemma setN_concat:
  forall bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z_of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. omega.
  simpl length. rewrite inj_S. simpl. rewrite IHbytes1. decEq. omega.
Qed.

(*X*)
Theorem storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  intros. generalize H; intro ST1. generalize H0; intro ST2.
  unfold storebytes; unfold storebytes in ST1; unfold storebytes in ST2.
  destruct (range_perm_dec m b ofs (ofs + Z_of_nat(length bytes1)) Cur Writable); try congruence.
  destruct (range_perm_dec m1 b (ofs + Z_of_nat(length bytes1)) (ofs + Z_of_nat(length bytes1) + Z_of_nat(length bytes2)) Cur Writable); try congruence.
  destruct (range_perm_dec m b ofs (ofs + Z_of_nat (length (bytes1 ++ bytes2))) Cur Writable).
  inv ST1; inv ST2; simpl. decEq. apply mkmem_ext; auto.
  rewrite PMap.gss.  rewrite setN_concat. symmetry. apply PMap.set2.
  elim n.
  rewrite app_length. rewrite inj_plus. red; intros.
  destruct (zlt ofs0 (ofs + Z_of_nat(length bytes1))).
  apply r. omega.
  eapply perm_storebytes_2; eauto. apply r0. omega.
Qed.

(*X*)
Theorem storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2.
Proof.
  intros.
  destruct (range_perm_storebytes m b ofs bytes1) as [m1 ST1].
  red; intros. exploit storebytes_range_perm; eauto. rewrite app_length.
  rewrite inj_plus. omega.
  destruct (range_perm_storebytes m1 b (ofs + Z_of_nat (length bytes1)) bytes2) as [m2' ST2].
  red; intros. eapply perm_storebytes_1; eauto. exploit storebytes_range_perm.
  eexact H. instantiate (1 := ofs0). rewrite app_length. rewrite inj_plus. omega.
  auto.
  assert (Some m2 = Some m2').
  rewrite <- H. eapply storebytes_concat; eauto.
  inv H0.
  exists m1; split; auto.
Qed.

(*X*)
Theorem store_int64_split:
  forall m b ofs v m',
  store Mint64 m b ofs v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     store Mint32 m b ofs (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ store Mint32 m1 b (ofs + 4) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros.
  exploit store_valid_access_3; eauto. intros [A B]. simpl in *.
  exploit store_storebytes. eexact H. intros SB.
  rewrite encode_val_int64 in SB by auto.
  exploit storebytes_split. eexact SB. intros [m1 [SB1 SB2]].
  rewrite encode_val_length in SB2. simpl in SB2.
  exists m1; split.
  apply storebytes_store. exact SB1.
  simpl. apply Zdivides_trans with 8; auto. exists 2; auto.
  apply storebytes_store. exact SB2.
  simpl. apply Zdivide_plus_r. apply Zdivides_trans with 8; auto. exists 2; auto. exists 1; auto.
Qed.

(*X*)
Theorem storev_int64_split:
  forall m a v m',
  storev Mint64 m a v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros. destruct a; simpl in H; inv H. rewrite H2.
  exploit store_int64_split; eauto. intros [m1 [A B]].
  exists m1; split.
  exact A.
  unfold storev, Val.add. rewrite H0.
  rewrite addressing_int64_split; auto.
  exploit store_valid_access_3. eexact H2. intros [P Q]. exact Q.
Qed.

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 lo hi = (m2, b).

(*X*)
Theorem nextblock_alloc:
  nextblock m2 = Psucc (nextblock m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

(*X*)
Theorem alloc_result:
  b = nextblock m1.
Proof.
  injection ALLOC; auto.
Qed.

(*X*)
Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_alloc.
  apply Plt_trans_succ; auto.
Qed.

(*X*)
Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. apply Plt_strict.
Qed.

(*X*)
Theorem valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite nextblock_alloc. apply Plt_succ.
Qed.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

(*X*)
Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros.
  rewrite nextblock_alloc in H. rewrite alloc_result.
  exploit Plt_succ_inv; eauto. tauto.
Qed.

(*X*)
Theorem perm_alloc_1:
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gsspec. destruct (peq b' (nextblock m1)); auto.
  rewrite nextblock_noaccess in H. contradiction. subst b'. apply Plt_strict.
Qed.

(*X*)
Theorem perm_alloc_2:
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. omega. omega.
Qed.

(*X*)
Theorem perm_alloc_inv:
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
  rewrite PMap.gsspec. unfold eq_block. destruct (peq b' (nextblock m1)); intros.
  destruct (zle lo ofs); try contradiction. destruct (zlt ofs hi); try contradiction.
  split; auto.
  auto.
Qed.

(*X*)
Theorem perm_alloc_3:
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto.
Qed.

(*X*)
Theorem perm_alloc_4:
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4: mem.

(*X*)
Theorem valid_access_alloc_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

(*X*)
Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. omega.
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

(*X*)
Theorem valid_access_alloc_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b' b). subst b'.
  assert (perm m2 b ofs Cur p). apply H0. omega.
  assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply H0. omega.
  exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro.
  intuition omega.
  split; auto. red; intros.
  exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto.
Qed.

(*X*)
Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite PMap.gso. auto. rewrite H1. apply sym_not_equal; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

(*X*)
Theorem load_alloc_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

(*X*)
Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  rewrite PMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. apply decode_val_undef. 
Qed.

(*X*)
Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. omega. auto with mem.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

(*X*)
Theorem loadbytes_alloc_unchanged:
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  rewrite pred_dec_false; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem.
Qed.

(*X*)
Theorem loadbytes_alloc_same:
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. rewrite PMap.gss.
  generalize (nat_of_Z n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H0. destruct H0; eauto.
Qed.

End ALLOC.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

(** ** Properties related to [free]. *)

(*X*)
Theorem range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto.
Defined.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi = Some m2.

(*X*)
Theorem free_range_perm:
  range_perm m1 bf lo hi Cur Freeable.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable); auto.
  congruence.
Qed.

(*X*)
Lemma free_result:
  m2 = unchecked_free m1 bf lo hi.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable).
  congruence. congruence.
Qed.

(*X*)
Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Proof.
  rewrite free_result; reflexivity.
Qed.

(*X*)
Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  intros. rewrite free_result. assumption.
Qed.

(*X*)
Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  intros. rewrite free_result in H. assumption.
Qed.

Local Hint Resolve valid_block_free_1 valid_block_free_2: mem.

(*X*)
Theorem perm_free_1:
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

(*X*)
Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true.
  simpl. tauto. omega. omega.
Qed.

(*X*)
Theorem perm_free_3:
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  auto. auto. auto.
Qed.

(*X*)
Theorem perm_free_inv:
  forall b ofs k p,
  perm m1 b ofs k p ->
  (b = bf /\ lo <= ofs < hi) \/ perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf); auto. subst b.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.

(*X*)
Theorem valid_access_free_1:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. omega.
Qed.

(*X*)
Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Proof.
  intros; red; intros. inv H2.
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo Cur p).
  omega. apply H3. omega.
  elim (perm_free_2 ofs Cur p).
  omega. apply H3. omega.
Qed.

(*X*)
Theorem valid_access_free_inv_1:
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Proof.
  intros. destruct H. split; auto.
  red; intros. generalize (H ofs0 H1).
  rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl.
  tauto. auto. auto. auto.
Qed.

(*X*)
Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto.
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. omega.
Qed.

(*X*)
Theorem load_free:
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto.
Qed.

(*X*)
Theorem load_free_2:
  forall chunk b ofs v,
  load chunk m2 b ofs = Some v -> load chunk m1 b ofs = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ H). rewrite free_result; auto.
  apply valid_access_free_inv_1. eauto with mem.
Qed.

(*X*)
Theorem loadbytes_free:
  forall b ofs n,
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  red; intros. eapply perm_free_3; eauto.
  rewrite pred_dec_false; auto.
  red; intros. elim n0; red; intros.
  eapply perm_free_1; eauto. destruct H; auto. right; omega.
Qed.

(*X*)
Theorem loadbytes_free_2:
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  rewrite pred_dec_true. rewrite free_result; auto.
  red; intros. apply perm_free_3; auto.
Qed.

End FREE.

Local Hint Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

(*X*)
Theorem range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' -> range_perm m b lo hi Cur Freeable.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). auto. discriminate.
Qed.

(*X*)
Theorem range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> 
  exists m', drop_perm m b lo hi p = Some m'.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). econstructor. eauto. contradiction.
Defined.

Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p = Some m'.

(*X*)
Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP; auto.
Qed.

(*X*)
Theorem drop_perm_valid_block_1:
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

(*X*)
Theorem drop_perm_valid_block_2:
  forall b', valid_block m' b' -> valid_block m b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

(*X*)
Theorem perm_drop_1:
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm. simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  omega. omega.
Qed.

(*X*)
Theorem perm_drop_2:
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H0. unfold perm; simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. auto.
  omega. omega.
Qed.

(*X*)
Theorem perm_drop_3:
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  byContradiction. intuition omega.
  auto. auto. auto.
Qed.

(*X*)
Theorem perm_drop_4:
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H. unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b).
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur.
  apply r. tauto. auto with mem. auto.
  auto. auto. auto.
Qed.

(*X*)
Lemma valid_access_drop_1:
  forall chunk b' ofs p',
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk b' ofs p' -> valid_access m' chunk b' ofs p'.
Proof.
  intros. destruct H0. split; auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. omega.
  generalize (size_chunk_pos chunk); intros. intuition.
  eapply perm_drop_3; eauto.
Qed.

(*X*)
Lemma valid_access_drop_2:
  forall chunk b' ofs p',
  valid_access m' chunk b' ofs p' -> valid_access m chunk b' ofs p'.
Proof.
  intros. destruct H; split; auto.
  red; intros. eapply perm_drop_4; eauto.
Qed.

(*X*)
Theorem load_drop:
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  eapply valid_access_drop_1; eauto.
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

(*X*)
Theorem loadbytes_drop:
  forall b' ofs n,
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n.
Proof.
  intros.
  unfold loadbytes.
  destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. omega. intuition.
  eapply perm_drop_3; eauto.
  rewrite pred_dec_false; eauto.
  red; intros; elim n0; red; intros.
  eapply perm_drop_4; eauto.
Qed.

End DROP.

(*SACC:*)
Local Hint Resolve range_perm_drop_1 range_perm_drop_2: mem.
Local Hint Resolve perm_drop_1 perm_drop_2 perm_drop_3 perm_drop_4: mem.
Local Hint Resolve drop_perm_valid_block_1 drop_perm_valid_block_2: mem.
Local Hint Resolve valid_access_drop_1 valid_access_drop_2 : mem.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

(*X*)
Record mem_inj (f: meminj) (*SACC:*) (g : frameinj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_perm:
      forall b1 b2 delta ofs k p,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs k p ->
      perm m2 b2 (ofs + delta) k p;
    mi_align:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | delta);
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Cur Readable ->
      memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2);
    mi_stack_blocks:
      stack_inject f (perm m1) g (stack m1) (stack m2)
  }.

(** Preservation of permissions *)

(*X*)
Lemma perm_inj:
  forall f g m1 m2 b1 ofs k p b2 delta,
  mem_inj f g m1 m2 ->
  perm m1 b1 ofs k p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p.
Proof.
  intros. eapply mi_perm; eauto.
Qed.

(*X*)
Lemma range_perm_inj:
  forall f g m1 m2 b1 lo hi k p b2 delta,
  mem_inj f g m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  f b1 = Some(b2, delta) ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros; red; intros.
  replace ofs with ((ofs - delta) + delta) by omega.
  eapply perm_inj; eauto. apply H0. omega.
Qed.

(*X*)
Lemma valid_access_inj:
  forall f g m1 m2 b1 b2 delta chunk ofs p,
  mem_inj f g m1 m2 ->
  f b1 = Some(b2, delta) ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. destruct H1 as [A B]. constructor.
  replace (ofs + delta + size_chunk chunk)
     with ((ofs + size_chunk chunk) + delta) by omega.
  eapply range_perm_inj; eauto.
  apply Z.divide_add_r; auto. eapply mi_align; eauto with mem.
Qed.

(** Preservation of loads. *)

(*X*)
Lemma getN_inj:
  forall f g m1 m2 b1 b2 delta,
  mem_inj f g m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z_of_nat n) Cur Readable ->
  list_forall2 (memval_inject f)
               (getN n ofs (m1.(mem_contents)#b1))
               (getN n (ofs + delta) (m2.(mem_contents)#b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite inj_S in H1.
  constructor.
  eapply mi_memval; eauto.
  apply H1. omega.
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by omega.
  apply IHn. red; intros; apply H1; omega.
Qed.

(*X*)
Lemma load_inj:
  forall f g m1 m2 chunk b1 ofs b2 delta v1,
  mem_inj f g m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros.
  exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents)#b2))).
  split. unfold load. apply pred_dec_true.
  eapply valid_access_inj; eauto with mem.
  exploit load_result; eauto. intro. rewrite H2.
  apply decode_val_inject. apply (getN_inj f g _ _ _ _ _); auto.
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
Qed.

(*X*)
Lemma loadbytes_inj:
  forall f g m1 m2 len b1 ofs b2 delta bytes1,
  mem_inj f g m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m1 b1 ofs (ofs + len) Cur Readable); inv H0.
  exists (getN (nat_of_Z len) (ofs + delta) (m2.(mem_contents)#b2)).
  split. apply pred_dec_true.
  replace (ofs + delta + len) with ((ofs + len) + delta) by omega.
  eapply range_perm_inj; eauto with mem.
  apply (getN_inj f g _ _ _ _ _); auto.
  destruct (zle 0 len). rewrite nat_of_Z_eq; auto. omega.
  rewrite nat_of_Z_neg. simpl. red; intros; omegaContradiction. omega.
Qed.

(** Preservation of stores. *)

(*X*)
Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) ->
  (forall q, access q -> memval_inject f (ZMap.get q (setN vl1 p c1))
                                         (ZMap.get (q + delta) (setN vl2 (p + delta) c2))).
Proof.
  induction 1; intros; simpl.
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by omega.
  apply IHlist_forall2; auto.
  intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
  rewrite ZMap.gss. auto.
  rewrite ZMap.gso. auto. unfold ZIndexed.t in *. omega.
Qed.

(*X*)
Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Lemma store_stack_unchanged:
  forall chunk m1 b1 ofs v1 n1,
    store chunk m1 b1 ofs v1 = Some n1 ->
    stack n1 = stack m1.
Proof.
  unfold store. intros.
  destruct (valid_access_dec m1 chunk b1 ofs Writable); try discriminate.
  inv H; auto.
Qed.

(*X*)
Lemma store_mapped_inj:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f g n1 n2.
Proof.
  intros.
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply valid_access_inj; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE].
  exists n2; split. auto.
  constructor.
(* perm *)
  intros. eapply perm_store_1; [eexact STORE|].
  eapply mi_perm; eauto.
  eapply perm_store_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  rewrite ! PMap.gsspec.
  destruct (peq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite peq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable).
  apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem.
  destruct (peq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. eapply mi_memval; eauto. eauto with mem.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto. eauto 6 with mem.
    exploit store_valid_access_3. eexact H0. intros [A B].
    eapply perm_implies. apply perm_cur_max. apply A. omega. auto with mem.
  destruct H8. congruence. omega.
  (* block <> b1, block <> b2 *)
  eapply mi_memval; eauto. eauto with mem.
  (*stack_inject f (perm n1) g (stack n1) (stack n2)*)
  rewrite (store_stack_unchanged _ _ _ _ _ _ STORE).
  rewrite (store_stack_unchanged _ _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong.
  2: apply mi_stack_blocks; auto.
  intros; eapply perm_store_2; eauto.
Qed.

(*X*)
Lemma store_unmapped_inj:
  forall f g chunk m1 b1 ofs v1 n1 m2,
  mem_inj f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f g n1 m2.
Proof.
  intros. constructor.
(* perm *)
  intros. eapply mi_perm; eauto with mem.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite PMap.gso. eapply mi_memval; eauto with mem.
  congruence.
(* stack_inject f (perm n1) g (stack n1) (stack m2) *)
  rewrite (store_stack_unchanged _ _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong.
  intros; eapply perm_store_2; eauto.
  apply mi_stack_blocks; auto.
Qed.

(*X*)
Lemma store_outside_inj:
  forall f g m1 m2 chunk b ofs v m2',
  mem_inj f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f g m1 m2'.
Proof.
  intros. inv H. constructor.
(* perm *)
  eauto with mem.
(* access *)
  intros; eapply mi_align0; eauto.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
  rewrite setN_outside. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)). omega.
  byContradiction. eapply H0; eauto. omega.
  eauto with mem.
(*stack_inject f (perm m1) g (stack m1) (stack m2') *)
  rewrite (store_stack_unchanged _ _ _ _ _ _ H1).
  eapply stack_inject_invariant_strong.
  2: eauto. tauto.
Qed.

(*SACC:*)
Lemma storebytes_stack_unchanged:
  forall m1 b o v m2,
    storebytes m1 b o v = Some m2 ->
    stack m2 = stack m1.
Proof.
  unfold storebytes.
  intros.
  destruct (range_perm_dec m1 b o (o + Z.of_nat (length v)) Cur Writable).
  inv H; simpl; tauto.
  inv H.
Qed.

(*X*)
Lemma storebytes_mapped_inj:
  forall f g m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  mem_inj f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ mem_inj f g n1 n2.
Proof.
  intros. inversion H.
  assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z_of_nat (length bytes2)) Cur Writable).
    replace (ofs + delta + Z_of_nat (length bytes2))
       with ((ofs + Z_of_nat (length bytes1)) + delta).
    eapply range_perm_inj; eauto with mem.
    eapply storebytes_range_perm; eauto.
    rewrite (list_forall2_length H3). omega.
  destruct (range_perm_storebytes _ _ _ _ H4) as [n2 STORE].
  exists n2; split. eauto.
  constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; [apply STORE |].
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ STORE).
  rewrite ! PMap.gsspec. destruct (peq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite peq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable); auto.
  destruct (peq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto 6 with mem.
    exploit storebytes_range_perm. eexact H0.
    instantiate (1 := r - delta).
    rewrite (list_forall2_length H3). omega.
    eauto 6 with mem.
  destruct H9. congruence. omega.
  (* block <> b1, block <> b2 *)
  eauto.
(* stack_inject f (perm n1) g (stack n1) (stack n2) *)
  rewrite (storebytes_stack_unchanged _ _ _ _ _ STORE).
  rewrite (storebytes_stack_unchanged _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong.
  2: apply mi_stack_blocks; auto.
  intros; eapply perm_storebytes_2; eauto.
Qed.

(*X*)
Lemma storebytes_unmapped_inj:
  forall f g m1 b1 ofs bytes1 n1 m2,
  mem_inj f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  mem_inj f g n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite PMap.gso. eapply mi_memval0; eauto. eapply perm_storebytes_2; eauto.
  congruence.
(* stack_inject f (perm n1) g (stack n1) (stack m2) *)
  rewrite (storebytes_stack_unchanged _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong.
  2: apply mi_stack_blocks; auto.
  intros; eapply perm_storebytes_2; eauto.
Qed.

(*X*)
Lemma storebytes_outside_inj:
  forall f g m1 m2 b ofs bytes2 m2',
  mem_inj f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  mem_inj f g m1 m2'.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. eapply perm_storebytes_1; eauto with mem.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
  rewrite setN_outside. auto.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + Z_of_nat (length bytes2)) (ofs0 + delta)). omega.
  byContradiction. eapply H0; eauto. omega.
  eauto with mem.
(* stack_inject f (perm m1) g (stack m1) (stack m2') *)
  rewrite (storebytes_stack_unchanged _ _ _ _ _ H1).
  eapply stack_inject_invariant_strong.
  2: apply mi_stack_blocks; eauto. tauto.
Qed.

(*X*)
Lemma storebytes_empty_inj:
  forall f g m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  mem_inj f g m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  mem_inj f g m1' m2'.
Proof.
  intros. destruct H. constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; eauto.
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  simpl. rewrite ! PMap.gsspec.
  destruct (peq b0 b1); destruct (peq b3 b2); subst; eapply mi_memval0; eauto.
(* stack_inject f (perm m1') g (stack m1') (stack m2') *)
  rewrite (storebytes_stack_unchanged _ _ _ _ _ H1).
  rewrite (storebytes_stack_unchanged _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong.
  2: apply mi_stack_blocks0; auto. 
  intros; eapply perm_storebytes_2; eauto.
Qed.

(** Preservation of allocations *)

(*X*)
Lemma alloc_right_inj:
  forall f g m1 m2 lo hi b2 m2',
  mem_inj f g m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f g m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* perm *)
  intros. eapply perm_alloc_1; eauto.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  assert (perm m2 b0 (ofs + delta) Cur Readable).
    eapply mi_perm0; eauto.
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. rewrite PMap.gso. eauto with mem.
  rewrite NEXT. eauto with mem.
(* stack_inject f (perm m1) g (stack m1) (stack m2') *)
  subst. simpl; auto.
Qed.

(*SACC:*)
Theorem alloc_stack_unchanged:
  forall m1 lo hi m2 b,
  alloc m1 lo hi = (m2, b) ->
  stack m2 = stack m1.
Proof.
  intros m1 m2 lo hi b ALLOC; unfold alloc in ALLOC; inv ALLOC. reflexivity.
Qed.

(*X*)
Lemma alloc_left_unmapped_inj:
  forall f g m1 m2 lo hi m1' b1,
  mem_inj f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f g m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. exploit perm_alloc_inv; eauto. intros.
  destruct (eq_block b0 b1). congruence. eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. exploit perm_alloc_inv; eauto.
  destruct (eq_block b0 b1); auto. congruence.
(* mem_contents *)
  injection H0; intros NEXT MEM. intros.
  rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite PMap.gsspec. unfold eq_block in H4. destruct (peq b0 b1).
  rewrite ZMap.gi. constructor. eauto.
(* stack_inject f (perm m1') g (stack m1') (stack m2) *)
  rewrite (alloc_stack_unchanged _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong. 2: eauto.
  intros; eapply perm_alloc_4; eauto. congruence.
Qed.

(*X*)
Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

(*X*)
Lemma alloc_left_mapped_inj:
  forall f g m1 m2 lo hi m1' b1 b2 delta,
  mem_inj f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  inj_offset_aligned delta (hi-lo) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  f b1 = Some(b2, delta) ->
  mem_inj f g m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros.
  exploit perm_alloc_inv; eauto. intros. destruct (eq_block b0 b1). subst b0.
  rewrite H4 in H5; inv H5. eauto. eauto.
(* align *)
  intros. destruct (eq_block b0 b1).
  subst b0. assert (delta0 = delta) by congruence. subst delta0.
  assert (lo <= ofs < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); omega. }
  assert (lo <= ofs + size_chunk chunk - 1 < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); omega. }
  apply H2. omega.
  eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_alloc_4; eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM.
  intros. rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite PMap.gsspec. unfold eq_block in H7.
  destruct (peq b0 b1). rewrite ZMap.gi. constructor. eauto.
(* stack_inject f (perm m1') g (stack m1') (stack m2) *)
  rewrite (alloc_stack_unchanged _ _ _ _ _ H0).
  eapply stack_inject_invariant. 2: eauto.
  intros.
  exploit perm_alloc_inv; eauto. destr. subst. exfalso.
  exploit alloc_result; eauto. intro; subst.
  eapply stack_inv_valid' in H5. eelim Plt_strict. apply H5.
  apply (mem_stack_inv m1).
Qed.

(*SACC:*)
Lemma free_stack_unchanged: 
  forall m1 bf lo hi m2,
  free m1 bf lo hi = Some m2 ->
  stack m2 = stack m1.
Proof.
  intros m1 bf lo hi m2 FREE.
  unfold free in FREE.
  unfold unchecked_free in FREE.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable);
    inversion FREE.
  simpl. reflexivity.
Qed.

(*X*)
Lemma free_left_inj:
  forall f g m1 m2 b lo hi m1',
  mem_inj f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  mem_inj f g m1' m2.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* perm *)
  intros. eauto with mem.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros; eapply perm_free_3; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto with mem.
(* stack *)
  rewrite (free_stack_unchanged _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong. 2: eauto.
  intros. eapply perm_free_3; eauto.
Qed.

(*X*)
Lemma free_right_inj:
  forall f g m1 m2 b lo hi m2',
  mem_inj f g m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  mem_inj f g m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H.
  assert (PERM:
    forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    perm m1 b1 ofs k p -> perm m2' b2 (ofs + delta) k p).
  intros.
  intros. eapply perm_free_1; eauto.
  destruct (eq_block b2 b); auto. subst b. right.
  assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto.
  omega.
  constructor.
(* perm *)
  auto.
(* align *)
  eapply mi_align0; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto.
(* stack *)
  rewrite (free_stack_unchanged _ _ _ _ _ H0). auto.
Qed.

(** Preservation of [drop_perm] operations. *)

(*SACC:*)
Lemma drop_perm_stack_unchanged:
  forall m1 b lo hi p m1',
    drop_perm m1 b lo hi p = Some m1' ->
    stack m1' = stack m1.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m1 b lo hi Cur Freeable); try discriminate. inv H; reflexivity.
Qed.

(*X*)
Lemma drop_unmapped_inj:
  forall f g m1 m2 b lo hi p m1',
  mem_inj f g m1 m2 ->
  drop_perm m1 b lo hi p = Some m1' ->
  f b = None ->
  mem_inj f g m1' m2.
Proof.
  intros. inv H. constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* contents *)
  intros.
  replace (ZMap.get ofs m1'.(mem_contents)#b1) with (ZMap.get ofs m1.(mem_contents)#b1).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b lo hi Cur Freeable); inv H0; auto.
(* stack *)
  rewrite (drop_perm_stack_unchanged _ _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong. 2: eauto.
  intros. eapply perm_drop_4; eauto.
Qed.

(*X*)
Lemma drop_mapped_inj:
  forall f g m1 m2 b1 b2 delta lo hi p m1',
  mem_inj f g m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  meminj_no_overlap f m1 ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ mem_inj f g m1' m2'.
Proof.
  intros.
  assert (exists m2', drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2') as X.
  apply range_perm_drop_2. red; intros.
  replace ofs with ((ofs - delta) + delta) by omega.
  eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. omega.
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H.
  constructor.
(* perm *)
  intros.
  assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
  destruct (eq_block b1 b0).
  (* b1 = b0 *)
  subst b0. rewrite H2 in H; inv H.
  destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto.
  destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto.
  assert (perm_order p p0).
    eapply perm_drop_2. eexact H0. instantiate (1 := ofs). omega. eauto.
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. omega.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  destruct (eq_block b3 b2); auto.
  destruct (zlt (ofs + delta0) (lo + delta)); auto.
  destruct (zle (hi + delta) (ofs + delta0)); auto.
  exploit H1; eauto.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable.
  eapply range_perm_drop_1; eauto. omega. auto with mem.
  eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.
  eauto with mem.
  intuition.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* memval *)
  intros.
  replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
  replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in DROP; destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) Cur Freeable); inv DROP; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b1 lo hi Cur Freeable); inv H0; auto.
(* stack *)
  rewrite (drop_perm_stack_unchanged _ _ _ _ _ _ H0).
  rewrite (drop_perm_stack_unchanged _ _ _ _ _ _ DROP).
  eapply stack_inject_invariant_strong. 2: eauto.
  intros. eapply perm_drop_4; eauto.
Qed.

(*X*)
Lemma drop_outside_inj: forall f g m1 m2 b lo hi p m2',
  mem_inj f g m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs' k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs' k p ->
    lo <= ofs' + delta < hi -> False) ->
  mem_inj f g m1 m2'.
Proof.
  intros. inv H. constructor.
  (* perm *)
  intros. eapply perm_drop_3; eauto.
  destruct (eq_block b2 b); auto. subst b2. right.
  destruct (zlt (ofs + delta) lo); auto.
  destruct (zle hi (ofs + delta)); auto.
  byContradiction. exploit H1; eauto. omega.
  (* align *)
  eapply mi_align0; eauto.
  (* contents *)
  intros.
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
  apply mi_memval0; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m2 b lo hi Cur Freeable); inv H0; auto.
  (* stack *)
  rewrite (drop_perm_stack_unchanged _ _ _ _ _ _ H0). auto.
Qed.

(** * Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. *)

(*X*)
Record extends' (m1 m2: mem) : Prop :=
  mk_extends {
    mext_next: nextblock m1 = nextblock m2;
  (*SACC:*)
    mext_inj:  mem_inj inject_id (flat_frameinj (length (stack m1))) m1 m2;
    mext_perm_inv: forall b ofs k p,
      perm m2 b ofs k p ->
      perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty;
  (*SACC:*)
    mext_length_stack:
      length (stack m2) = length (stack m1)
  }.

(*X*)
Definition extends := extends'.

(*X*)
Theorem extends_refl:
  forall m, extends m m.
Proof.
  intros. constructor. auto. constructor.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega. auto.
  intros. unfold inject_id in H; inv H. apply Z.divide_0_r.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega.
  apply memval_lessdef_refl.
  apply stack_inject_id.
  eapply stack_inv_wf. apply mem_stack_inv.
  auto.
  tauto.
Qed.

(*X*)
Theorem load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H. exploit load_inj; eauto. unfold inject_id; reflexivity.
  intros [v2 [A B]]. exists v2; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  rewrite val_inject_id in B. auto.
Qed.

(*X*)
Theorem loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  unfold loadv; intros. inv H1.
  destruct addr2; try congruence. eapply load_extends; eauto.
  congruence.
Qed.

(*X*)
Theorem loadbytes_extends:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.
Proof.
  intros. inv H.
  replace ofs with (ofs + 0) by omega. eapply loadbytes_inj; eauto.
Qed.

(*SACC:*)
Lemma storev_stack_unchanged:
  forall m chunk addr v m',
  storev chunk m addr v = Some m' ->
  stack m' = stack m.
Proof.
  intros chunk m1 addr v m2 H; unfold storev in H; destr_in H.
  eapply store_stack_unchanged; eauto.
Qed.

(*SACC:*)
Ltac rewrite_stack_backwards :=
  repeat match goal with
         | H: store _ ?m1 _ _ _ = Some ?m2 |- context [stack ?m2] =>
           rewrite (store_stack_unchanged _ _ _ _ _ _ H)
         | H: storev _ ?m1 _ _ = Some ?m2 |- context [stack ?m2] =>
           rewrite (storev_stack_unchanged _ _ _ _ _ H)
         | H: storebytes ?m1 _ _ _ = Some ?m2 |- context [stack ?m2] =>
           rewrite (storebytes_stack_unchanged _ _ _ _ _ H)
         | H: alloc ?m1 _ _ = (?m2,_) |- context [stack ?m2] =>
           rewrite (alloc_stack_unchanged _ _ _ _ _ H)
         | H: free ?m1 _ _ _ = Some ?m2 |- context [stack ?m2] =>
           rewrite (free_stack_unchanged _ _ _ _ _ H)
         | H: drop_perm ?m1 _ _ _ _ = Some ?m2 |- context [stack ?m2] =>
           rewrite (drop_perm_stack_unchanged _ _ _ _ _ _ H)
         end.

(*X*)
Theorem store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    rewrite val_inject_id. eauto.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  constructor; auto.
  rewrite (nextblock_store _ _ _ _ _ _ H0).
  rewrite (nextblock_store _ _ _ _ _ _ A).
  auto.
  erewrite store_stack_unchanged; eauto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_1, perm_store_2.
  rewrite_stack_backwards; auto.
Qed.

(*X*)
Theorem store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_store _ _ _ _ _ _ H0). auto.
  eapply store_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. omega.
  intros. eauto using perm_store_2.
  rewrite_stack_backwards. auto.
Qed.

(*X*)
Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  unfold storev; intros. inv H1.
  destruct addr2; try congruence. eapply store_within_extends; eauto.
  congruence.
Qed.

(*X*)
Theorem storebytes_within_extends:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  constructor; auto.
  rewrite (nextblock_storebytes _ _ _ _ _ H0).
  rewrite (nextblock_storebytes _ _ _ _ _ A).
  auto.
  erewrite storebytes_stack_unchanged; eauto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_storebytes_1, perm_storebytes_2.
  rewrite_stack_backwards; auto.
Qed.

(*SACC:*)
Theorem storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z_of_nat (length bytes2) -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_storebytes _ _ _ _ _ H0). auto.
  eapply storebytes_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. omega.
  intros. eauto using perm_storebytes_2.
  rewrite_stack_backwards; auto.
Qed.

(*X*)
Theorem alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Proof.
  intros. inv H.
  case_eq (alloc m2 lo2 hi2); intros m2' b' ALLOC.
  assert (b' = b).
  {
    rewrite (alloc_result _ _ _ _ _ H0).
    rewrite (alloc_result _ _ _ _ _ ALLOC).
    auto.
  }
  subst b'.
  exists m2'; split; auto.
  constructor.
  - rewrite (nextblock_alloc _ _ _ _ _ H0).
    rewrite (nextblock_alloc _ _ _ _ _ ALLOC).
    congruence.
  - eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto.
    + eapply alloc_right_inj; eauto.
      erewrite alloc_stack_unchanged; eauto.
    + eauto with mem.
    + red. intros. apply Zdivide_0.
    + intros.
      eapply perm_implies with Freeable; auto with mem.
      eapply perm_alloc_2; eauto.
      omega.
  - intros. eapply perm_alloc_inv in H; eauto.
    generalize (perm_alloc_inv _ _ _ _ _ H0 b0 ofs Max Nonempty); intros PERM.
    destruct (eq_block b0 b).
    subst b0. 
    assert (EITHER: lo1 <= ofs < hi1 \/ ~(lo1 <= ofs < hi1)) by omega.
    destruct EITHER.
    left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
    right; tauto.
    exploit mext_perm_inv0; intuition eauto using perm_alloc_1, perm_alloc_4.
  - rewrite_stack_backwards; auto.
Qed.

(*X*)
Theorem free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_left_inj; eauto.
  erewrite free_stack_unchanged; eauto.
  intros. exploit mext_perm_inv0; eauto. intros [A|A]. 
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  intuition eauto using perm_free_3.
  rewrite_stack_backwards; auto.
Qed.

(*X*)
Theorem free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_right_inj; eauto.
  unfold inject_id; intros. inv H. eapply H1; eauto. omega.
  intros. eauto using perm_free_3.
  rewrite_stack_backwards; auto.
Qed.

(*X*)
Theorem free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  assert ({ m2': mem | free m2 b lo hi = Some m2' }).
    apply range_perm_free. red; intros.
    replace ofs with (ofs + 0) by omega.
    eapply perm_inj with (b1 := b); eauto.
    eapply free_range_perm; eauto.
  destruct X as [m2' FREE]. exists m2'; split; auto.
  constructor.
  rewrite (nextblock_free _ _ _ _ _ H0).
  rewrite (nextblock_free _ _ _ _ _ FREE). auto.
  eapply free_right_inj with (m1 := m1'); eauto.
  eapply free_left_inj; eauto.
  erewrite free_stack_unchanged; eauto.
  unfold inject_id; intros. inv H1.
  eapply perm_free_2. eexact H0. instantiate (1 := ofs); omega. eauto.
  intros. exploit mext_perm_inv0; eauto using perm_free_3. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  right; intuition eauto using perm_free_3.
  rewrite_stack_backwards; auto.
Qed.

(*X*)
Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Proof.
  intros. inv H. unfold valid_block. rewrite mext_next0. tauto.
Qed.

(*X*)
Theorem perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by omega.
  eapply perm_inj; eauto.
Qed.

(*X*)
Theorem perm_extends_inv:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m2 b ofs k p -> perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty.
Proof.
  intros. inv H; eauto.
Qed.

(*X*)
Theorem valid_access_extends:
  forall m1 m2 chunk b ofs p,
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by omega.
  eapply valid_access_inj; eauto. auto.
Qed.

(*X*)
Theorem valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in *.
  eapply valid_access_extends; eauto.
Qed.

(*X*)
Theorem weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.
Proof.
  intros until 1. unfold weak_valid_pointer. rewrite !orb_true_iff.
  intros []; eauto using valid_pointer_extends.
Qed.

(** * Memory injections *)

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
*)

(*X*)
Record inject' (f: meminj) (g : frameinj) (m1 m2: mem) : Prop :=
  mk_inject {
    (* SACC: Modified *)
    mi_inj:
      mem_inj f g m1 m2;
    (* Original CompCert: *)
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    (*SACC:*)
    mi_representable:
      forall b b' delta,
      f b = Some(b', delta) ->
      delta >= 0
      /\
      forall ofs,
        perm m1 b (Ptrofs.unsigned ofs) Max Nonempty
        \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
        0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mi_perm_inv:
      forall b1 ofs b2 delta k p,
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
  }.
(*X*)
Definition inject := inject'.

Local Hint Resolve mi_mappedblocks: mem.

(** Preservation of access validity and pointer validity *)

(*X*)
Theorem valid_block_inject_1:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m1 b1.
Proof.
  intros. inv H. destruct (plt b1 (nextblock m1)). auto.
  assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
Qed.

(*X*)
Theorem valid_block_inject_2:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m2 b2.
Proof.
  intros. eapply mi_mappedblocks; eauto.
Qed.

Local Hint Resolve valid_block_inject_1 valid_block_inject_2: mem.

(*X*)
Theorem perm_inject:
  forall f g m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.
Proof.
  intros. inv H0. eapply perm_inj; eauto.
Qed.

(*X*)
Theorem perm_inject_inv:
  forall f g m1 m2 b1 ofs b2 delta k p,
  inject f g m1 m2 ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p ->
  perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty.
Proof.
  intros. eapply mi_perm_inv; eauto.
Qed.

(*X*)
Theorem range_perm_inject:
  forall f g m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  range_perm m1 b1 lo hi k p -> range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros. inv H0. eapply range_perm_inj; eauto.
Qed.

(*X*)
Theorem valid_access_inject:
  forall f g m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. eapply valid_access_inj; eauto. apply mi_inj; eauto.
Qed.

(*X*)
Theorem valid_pointer_inject:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access.
  eapply valid_access_inject; eauto.
Qed.

(*X*)
Theorem weak_valid_pointer_inject:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros until 2. unfold weak_valid_pointer. rewrite !orb_true_iff.
  replace (ofs + delta - 1) with ((ofs - 1) + delta) by omega.
  intros []; eauto using valid_pointer_inject.
Qed.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f g m1 m2 b1 ofs1 b2 delta p,
  inject f g m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  assert (perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem.
  exploit mi_representable; eauto. intros [A B].
  exploit B; eauto. clear B; intro B.
  assert (0 <= delta <= Ptrofs.max_unsigned).
    generalize (Ptrofs.unsigned_range ofs1). omega.
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; omega.
Qed.

(*X*)
Lemma address_inject':
  forall f g m1 m2 chunk b1 ofs1 b2 delta,
  inject f g m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto.
  apply H0. generalize (size_chunk_pos chunk). omega.
Qed.

(*X*)
Theorem weak_valid_pointer_inject_no_overflow:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. 
  intros [A B]. exploit B; eauto.
  destruct H0; eauto with mem.
  pose proof (Ptrofs.unsigned_range ofs). intro.
  rewrite Ptrofs.unsigned_repr. auto.
  omega.
Qed.

(*X*)
Theorem valid_pointer_inject_no_overflow:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  eauto using weak_valid_pointer_inject_no_overflow, valid_pointer_implies.
Qed.

(*X*)
Theorem valid_pointer_inject_val:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  erewrite address_inject'; eauto.
  eapply valid_pointer_inject; eauto.
  rewrite valid_pointer_valid_access in H0. eauto.
Qed.

(*X*)
Theorem weak_valid_pointer_inject_val:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  exploit weak_valid_pointer_inject; eauto. intros W.
  rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. 
  intros [A B]. exploit B; eauto.
  destruct H0; eauto with mem. intros.
  pose proof (Ptrofs.unsigned_range ofs).
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; auto; omega.
Qed.

(*X*)
Theorem inject_no_overlap:
  forall f g m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f g m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. inv H. eapply mi_no_overlap0; eauto.
Qed.

(*X*)
Theorem different_pointers_inject:
  forall f g m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f g m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access in H2.
  rewrite (address_inject' _ _ _ _ _ _ _ _ _ H H1 H3).
  rewrite (address_inject' _ _ _ _ _ _ _ _ _ H H2 H4).
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply mi_no_overlap; eauto.
  apply perm_cur_max. apply (H5 (Ptrofs.unsigned ofs1)). omega.
  apply perm_cur_max. apply (H1 (Ptrofs.unsigned ofs2)). omega.
Qed.

(*X*)
Theorem disjoint_or_equal_inject:
  forall f g m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f g m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2
             \/ ofs2 + delta2 + sz <= ofs1 + delta1.
Proof.
  intros.
  destruct (eq_block b1 b2).
  assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst.
  destruct H5. congruence. right. destruct H5. left; congruence. right. omega.
  destruct (eq_block b1' b2'); auto. subst. right. right.
  set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz)).
  set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz)).
  change (snd i1 <= fst i2 \/ snd i2 <= fst i1).
  apply Intv.range_disjoint'; simpl; try omega.
  unfold Intv.disjoint, Intv.In; simpl; intros. red; intros.
  exploit mi_no_overlap; eauto.
  instantiate (1 := x - delta1). apply H2. omega.
  instantiate (1 := x - delta2). apply H3. omega.
  intuition.
Qed.

(*X*)
Theorem aligned_area_inject:
  forall f g m m' b ofs al sz b' delta,
  inject f g m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta).
Proof.
  intros.
  assert (P: al > 0) by omega.
  assert (Q: Zabs al <= Zabs sz). apply Zdivide_bounds; auto. omega.
  rewrite Zabs_eq in Q; try omega. rewrite Zabs_eq in Q; try omega.
  assert (R: exists chunk, al = align_chunk chunk /\ al = size_chunk chunk).
    destruct H0. subst; exists Mint8unsigned; auto.
    destruct H0. subst; exists Mint16unsigned; auto.
    destruct H0. subst; exists Mint32; auto.
    subst; exists Mint64; auto.
  destruct R as [chunk [A B]].
  assert (valid_access m chunk b ofs Nonempty).
    split. red; intros; apply H3. omega. congruence.
  exploit valid_access_inject; eauto. intros [C D].
  congruence.
Qed.

(** Preservation of loads *)

(*X*)
Theorem load_inject:
  forall f g m1 m2 chunk b1 ofs b2 delta v1,
  inject f g m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H. eapply load_inj; eauto.
Qed.

(*X*)
Theorem loadv_inject:
  forall f g m1 m2 chunk a1 a2 v1,
  inject f g m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. unfold loadv.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
     with (Ptrofs.unsigned ofs1 + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

(*X*)
Theorem loadbytes_inject:
  forall f g m1 m2 b1 ofs len b2 delta bytes1,
  inject f g m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. inv H. eapply loadbytes_inj; eauto.
Qed.

(** Preservation of stores *)

(*X*)
Theorem store_mapped_inject:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f g n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. exploit mi_representable; try eassumption.
  intros [A B]; split; eauto. intros ofs0 P. eapply B.
  destruct P; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2. 
  intuition eauto using perm_store_1, perm_store_2.
Qed.

(*X*)
Theorem store_unmapped_inject:
  forall f g chunk m1 b1 ofs v1 n1 m2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply store_unmapped_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. exploit mi_representable; try eassumption.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H3; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2. 
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_outside_inject:
  forall f g m1 m2 chunk b ofs v m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f g m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply store_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  eauto with mem.
(* perm inv *)
  intros. eauto using perm_store_2.
Qed.

(*X*)
Theorem storev_mapped_inject:
  forall f g chunk m1 a1 v1 n1 m2 a2 v2,
  inject f g m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f g n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  unfold storev.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
    with (Ptrofs.unsigned ofs1 + delta).
  eapply store_mapped_inject; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.

(*X*)
Theorem storebytes_mapped_inject:
  forall f g m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f g n1 n2.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H3; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. exploit mi_representable0; eauto.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H4; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2. 
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

(*X*)
Theorem storebytes_unmapped_inject:
  forall f g m1 b1 ofs bytes1 n1 m2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply storebytes_unmapped_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. exploit mi_representable0; eauto.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

(*X*)
Theorem storebytes_outside_inject:
  forall f g m1 m2 b ofs bytes2 m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f g m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply storebytes_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply mi_perm_inv0; eauto using perm_storebytes_2.
Qed.

(*X*)
Theorem storebytes_empty_inject:
  forall f g m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f g m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f g m1' m2'.
Proof.
  intros. inversion H. constructor; intros.
(* inj *)
  eapply storebytes_empty_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. exploit mi_representable0; eauto.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2. 
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

(* Preservation of allocations *)

(*X*)
Theorem alloc_right_inject:
  forall f g m1 m2 lo hi b2 m2',
  inject f g m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f g m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* inj *)
  eapply alloc_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply perm_alloc_inv in H2; eauto. destruct (eq_block b0 b2).
  subst b0. eelim fresh_block_alloc; eauto. 
  eapply mi_perm_inv0; eauto.
Qed.

(*X*)
Theorem alloc_left_unmapped_inject:
  forall f g m1 m2 lo hi m1' b1,
  inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' g m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then None else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' g m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    apply memval_inject_incr with f; auto.
    eapply stack_inject_incr; eauto.
    unfold f'; intros b b' delta NONE SOME.
    destr_in SOME.
  exists f'; split. constructor.
(* inj *)
  eapply alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  intros. unfold f'. destruct (eq_block b b1). auto.
  apply mi_freeblocks0. red; intro; elim H3. eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* no overlap *)
  unfold f'; red; intros.
  destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
  eapply mi_no_overlap0. eexact H3. eauto. eauto.
  exploit perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
  exploit perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1); try discriminate.
  exploit mi_representable0; try eassumption.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H4; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate.
  exploit mi_perm_inv0; eauto. 
  intuition eauto using perm_alloc_1, perm_alloc_4.
(* incr *)
  split. auto.
(* image *)
  split. unfold f'; apply dec_eq_true.
(* incr *)
  intros; unfold f'; apply dec_eq_false; auto.
Qed.

(*X*)
Theorem alloc_left_mapped_inject:
  forall f g m1 m2 lo hi m1' b1 b2 delta,
  inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f',
     inject f' g m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' g m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0).
      eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); omega.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
      eapply stack_inject_incr; eauto.
      unfold f'. intros b b' delta0 NONE SOME. destr_in SOME. inv SOME.
      intro IFR. apply fresh_block_alloc in H0.
        apply H0. eapply in_stack_valid. auto.
  exists f'. split. constructor.
(* inj *)
  eapply alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1).
  congruence.
  inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. omega.
  inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. omega.
  eauto.
(* representable *)
  {
    unfold f'; intros b b' delta0 FB.
    destruct (eq_block b b1).
    - subst. injection FB; intros; subst b' delta0.
      split. omega.
      intros.
      destruct H9.
      exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
      exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
      generalize (Ptrofs.unsigned_range_2 ofs). omega.
      exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
      exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
      generalize (Ptrofs.unsigned_range_2 ofs). omega.
    - exploit mi_representable0; try eassumption.
      intros [A B]; split; auto.
      intros; eapply B; eauto.
      destruct H9; eauto using perm_alloc_4.
  }
(* perm inv *)
  intros. unfold f' in H9; destruct (eq_block b0 b1).
  inversion H9; clear H9; subst b0 b3 delta0.
  assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by omega.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
  exploit mi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold f'; apply dec_eq_true.
(* image of others *)
  intros. unfold f'; apply dec_eq_false; auto.
Qed.

(*X*)
Theorem alloc_parallel_inject:
  forall f g m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f g m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' g m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros.
  case_eq (alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject.
  eapply alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  instantiate (1 := 0). unfold Ptrofs.max_unsigned. generalize Ptrofs.modulus_pos; omega.
  auto.
  intros. apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. omega.
  red; intros. apply Zdivide_0.
  intros. apply (valid_not_valid_diff m2 b2 b2); eauto with mem.
  intros [f' [A [B [C D]]]].
  exists f'; exists m2'; exists b2; auto.
Qed.

(** Preservation of [free] operations *)

(*X*)
Lemma free_left_inject:
  forall f g m1 m2 b lo hi m1',
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f g m1' m2.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_left_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  auto.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros.   exploit mi_representable0; try eassumption.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H2; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto. intuition eauto using perm_free_3.
  eapply perm_free_inv in H4; eauto. destruct H4 as [[A B] | A]; auto.
  subst b1. right; eapply perm_free_2; eauto. 
Qed.

(*X*)
Lemma free_list_left_inject:
  forall f g m2 l m1 m1',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f g m1' m2.
Proof.
  induction l; simpl; intros.
  inv H0. auto.
  destruct a as [[b lo] hi].
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
  apply IHl with m11; auto. eapply free_left_inject; eauto.
Qed.

(*X*)
Lemma free_right_inject:
  forall f g m1 m2 b lo hi m2',
  inject f g m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eauto using perm_free_3.
Qed.

(*X*)
Lemma perm_free_list:
  forall l m m' b ofs k p,
  free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; simpl; intros.
  inv H. auto.
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split. eauto with mem.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

(*X*)
Theorem free_inject:
  forall f g m1 l m1' m2 b lo hi m2',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) ->
    perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f g m1' m2'.
Proof.
  intros.
  eapply free_right_inject; eauto.
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

(*X*)
Theorem free_parallel_inject:
  forall f g m1 m2 b lo hi m1' b' delta,
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f g m1' m2'.
Proof.
  intros.
  destruct (range_perm_free m2 b' (lo + delta) (hi + delta)) as [m2' FREE].
  eapply range_perm_inject; eauto. eapply free_range_perm; eauto.
  exists m2'; split; auto.
  eapply free_inject with (m1 := m1) (l := (b,lo,hi)::nil); eauto.
  simpl; rewrite H0; auto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H2; inv H2.
  exists lo, hi; split; auto with coqlib. omega.
  exploit mi_no_overlap. eexact H. eexact n. eauto. eauto.
  eapply perm_max. eapply perm_implies. eauto. auto with mem.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable; auto with mem.
  eapply free_range_perm; eauto. omega.
  intros [A|A]. congruence. omega.
Qed.

(*X*)
Lemma drop_outside_inject: forall f g m1 m2 b lo hi p m2',
  inject f g m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2'.
Proof.
  intros. destruct H. constructor; eauto.
  eapply drop_outside_inj; eauto.
  intros. unfold valid_block in *. erewrite nextblock_drop; eauto.
  intros. eapply mi_perm_inv0; eauto using perm_drop_4.
Qed.

(** Composing two memory injections. *)

(*X*)
Lemma mem_inj_compose:
  forall f f' g g' m1 m2 m3,
  mem_inj f g m1 m2 -> mem_inj f' g' m2 m3 -> 
  forall g'', compose_frameinj g g' = Some g'' ->
  mem_inj (compose_meminj f f') g'' m1 m3.
Proof.
  intros. unfold compose_meminj. inv H; inv H0; constructor; intros.
  (* perm *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by omega.
  eauto.
  (* align *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  apply Z.divide_add_r.
  eapply mi_align0; eauto.
  eapply mi_align1 with (ofs := ofs + delta') (p := p); eauto.
  red; intros. replace ofs0 with ((ofs0 - delta') + delta') by omega.
  eapply mi_perm0; eauto. apply H0. omega.
  (* memval *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by omega.
  eapply memval_inject_compose; eauto.
  (* stack_inject *)
  eapply stack_inject_compose; eauto.
Qed.

(*X*)
Theorem inject_compose:
  forall f f' g g' m1 m2 m3,
  inject f g m1 m2 -> inject f' g' m2 m3 ->
  forall g'', compose_frameinj g g' = Some g'' ->
  inject (compose_meminj f f') g'' m1 m3.
Proof.
  unfold compose_meminj; intros.
  inv H; inv H0. constructor.
(* inj *)
  eapply mem_inj_compose; eauto.
(* unmapped *)
  intros. erewrite mi_freeblocks0; eauto.
(* mapped *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  eauto.
(* no overlap *)
  red; intros.
  destruct (f b1) as [[b1x delta1x] |] eqn:?; try discriminate.
  destruct (f' b1x) as [[b1y delta1y] |] eqn:?; inv H0.
  destruct (f b2) as [[b2x delta2x] |] eqn:?; try discriminate.
  destruct (f' b2x) as [[b2y delta2y] |] eqn:?; inv H2.
  exploit mi_no_overlap0; eauto. intros A.
  destruct (eq_block b1x b2x).
  subst b1x. destruct A. congruence.
  assert (delta1y = delta2y) by congruence. right; omega.
  exploit mi_no_overlap1. eauto. eauto. eauto.
    eapply perm_inj. eauto. eexact H3. eauto.
    eapply perm_inj. eauto. eexact H4. eauto.
  intuition omega.
(* representable *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  exploit mi_representable0; eauto. intros [A B].
  exploit mi_representable1. eauto. intros [C D]. 
  split; auto. omega.
  intros.
  set (ofs' := Ptrofs.repr (Ptrofs.unsigned ofs + delta1)).
  assert (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs + delta1).
    unfold ofs'; apply Ptrofs.unsigned_repr. auto.
    exploit D. instantiate (1 := ofs').
  rewrite H0.
  replace (Ptrofs.unsigned ofs + delta1 - 1) with
    ((Ptrofs.unsigned ofs - 1) + delta1) by omega.
  destruct H; eauto using perm_inj.
  rewrite H0. omega.
(* perm inv *)
  intros. 
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; try discriminate.
  inversion H; clear H; subst b'' delta.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') in H0 by omega.
  exploit mi_perm_inv1; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros. elim A. eapply perm_inj; eauto.
Qed.

(*X*)
Lemma val_lessdef_inject_compose:
  forall f v1 v2 v3,
  Val.lessdef v1 v2 -> Val.inject f v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H. auto. auto.
Qed.

(*X*)
Lemma val_inject_lessdef_compose:
  forall f v1 v2 v3,
  Val.inject f v1 v2 -> Val.lessdef v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H0. auto. inv H. auto.
Qed.

(*SACC:*)
Lemma take_flat_frameinj:
  forall a b,
    take a (flat_frameinj (a + b)) = Some (flat_frameinj a).
Proof.
  induction a; simpl; intros; eauto.
  setoid_rewrite IHa. reflexivity.
Qed.

(*SACC:*)
Remark drop_flat_frameinj:
  forall a b,
    drop a (flat_frameinj (a + b)) = flat_frameinj b.
Proof.
  induction a; simpl; intros; eauto.
Qed.

(*SACC:*)
Remark sum_list_flat:
  forall a,
    sum_list (flat_frameinj a) = a.
Proof.
  induction a; simpl; intros; eauto.
Qed.

(*SACC*)
Remark compose_frameinj_flat:
  forall g,
    compose_frameinj (flat_frameinj (sum_list g)) g = Some g.
Proof.
  induction g; simpl; intros. auto.
  rewrite take_flat_frameinj.
  rewrite drop_flat_frameinj. rewrite IHg.
  rewrite sum_list_flat. reflexivity.
Qed.

(*SACC:*)
Remark compose_frameinj_flat':
  forall g,
    compose_frameinj g (flat_frameinj (length g)) = Some g.
Proof.
  induction g; simpl; intros. auto.
  setoid_rewrite IHg. rewrite Nat.add_0_r. reflexivity.
Qed.

(*SACC:*)
Lemma compose_frameinj_same:
  forall g,
    compose_frameinj (flat_frameinj g) (flat_frameinj g) = Some (flat_frameinj g).
Proof.
  induction g; simpl; intros. auto.
  setoid_rewrite IHg. reflexivity.
Qed.

(*X* SACC: Needed by Stackingproof, with Linear2 to Mach,
   to compose extends (in Linear2) and inject. *)
Lemma extends_inject_compose:
  forall f g m1 m2 m3,
  extends m1 m2 -> inject f g m2 m3 -> inject f g m1 m3.
Proof.
  intros. inversion H; inv H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj inject_id f). eapply mem_inj_compose; eauto.
  inv mi_inj0. apply stack_inject_length_l in mi_stack_blocks0.
  rewrite <- mext_length_stack0, <- mi_stack_blocks0.
  apply compose_frameinj_flat.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto.
(* unmapped *)
  eapply mi_freeblocks0. erewrite <- valid_block_extends; eauto.
(* mapped *)
  eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_extends; eauto.
(* representable *)
  exploit mi_representable0; try eassumption.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H1; [left|right]; eapply perm_extends; eauto.
(* perm inv *)
  exploit mi_perm_inv0; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
Qed.

(*X*)
Lemma inject_extends_compose:
  forall f g m1 m2 m3,
  inject f g m1 m2 -> extends m2 m3 -> inject f g m1 m3.
Proof.
  intros. inv H; inversion H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj f inject_id). eapply mem_inj_compose; eauto.
  inv mi_inj0. apply stack_inject_length_r in mi_stack_blocks0.
  rewrite <- mi_stack_blocks0.
  apply compose_frameinj_flat'.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto. decEq. decEq. omega.
(* unmapped *)
  eauto.
(* mapped *)
  erewrite <- valid_block_extends; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto.
(* representable *)
  eapply mi_representable0; eauto.
(* perm inv *)
  exploit mext_perm_inv0; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_inj; eauto.
Qed.

(*X*)
Lemma extends_extends_compose:
  forall m1 m2 m3,
  extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof.
  intros. inversion H; subst; inv H0; constructor; intros.
  (* nextblock *)
  congruence.
  (* meminj *)
  replace inject_id with (compose_meminj inject_id inject_id).
  eapply mem_inj_compose; eauto.
  rewrite mext_length_stack0.
  apply compose_frameinj_same.
  apply extensionality; intros. unfold compose_meminj, inject_id. auto.
  (* perm inv *)
  exploit mext_perm_inv1; eauto. intros [A|A]. 
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
  (* stack length *)
  congruence.
Qed.

(** Injecting a memory into itself. *)

(*X*)
Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Definition inject_neutral (thr: block) (m: mem) :=
  mem_inj (flat_inj thr) (*SACC:*) (flat_frameinj (length (stack m))) m m.

Remark flat_inj_no_overlap:
  forall thr m, meminj_no_overlap (flat_inj thr) m.
Proof.
  unfold flat_inj; intros; red; intros.
  destruct (plt b1 thr); inversion H0; subst.
  destruct (plt b2 thr); inversion H1; subst.
  auto.
Qed.

(*X*)
Theorem neutral_inject:
  forall m, inject_neutral (nextblock m) m -> inject (flat_inj (nextblock m)) (flat_frameinj (length (stack m))) m m.
Proof.
  intros. constructor.
(* meminj *)
  auto.
(* freeblocks *)
  unfold flat_inj, valid_block; intros.
  apply pred_dec_false. auto.
(* mappedblocks *)
  unfold flat_inj, valid_block; intros.
  destruct (plt b (nextblock m)); inversion H0; subst. auto.
(* no overlap *)
  apply flat_inj_no_overlap.
(* range *)
  unfold flat_inj; intros.
  destruct (plt b (nextblock m)); inv H0. split; auto. omega. intros. generalize (Ptrofs.unsigned_range_2 ofs); omega.
(* perm inv *)
  unfold flat_inj; intros.
  destruct (plt b1 (nextblock m)); inv H0.
  rewrite Zplus_0_r in H1; auto.
Qed.

(*X*)
Theorem empty_inject_neutral:
  forall thr, inject_neutral thr empty.
Proof.
  intros; red; constructor.
(* perm *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H.
  replace (ofs + 0) with ofs by omega; auto.
(* align *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H. apply Z.divide_0_r.
(* mem_contents *)
  intros; simpl. rewrite ! PMap.gi. rewrite ! ZMap.gi. constructor.
(* stack adt *)
  apply stack_inject_nil.
Qed.

(*X*)
Theorem alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m'.
Proof.
  intros; red.
  erewrite alloc_stack_unchanged; eauto.
  eapply alloc_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0).
  eapply alloc_right_inj; eauto. eauto. eauto with mem.
  red. intros. apply Zdivide_0.
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. omega.
  unfold flat_inj. apply pred_dec_true.
  rewrite (alloc_result _ _ _ _ _ H). auto.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  intros; red.
  exploit store_mapped_inj. eauto. eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; auto. eauto.
  replace (ofs + 0) with ofs by omega.
  intros [m'' [A B]]. 
  erewrite store_stack_unchanged; eauto. congruence.
Qed.

(*X*)
Theorem drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  unfold inject_neutral; intros.
  exploit drop_mapped_inj; eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; eauto.
  repeat rewrite Zplus_0_r. intros [m'' [A B]]. 
  erewrite drop_perm_stack_unchanged; eauto.
  congruence.
Qed.

(** * Invariance properties between two memory states *)

Section UNCHANGED_ON.

(*X*)
Variable P: block -> Z -> Prop.

(*X*)
Record unchanged_on' (m_before m_after: mem) : Prop := mk_unchanged_on {
  unchanged_on_nextblock:
    Ple (nextblock m_before) (nextblock m_after);
  unchanged_on_perm:
    forall b ofs k p,
    P b ofs -> valid_block m_before b ->
    (perm m_before b ofs k p <-> perm m_after b ofs k p);
  unchanged_on_contents:
    forall b ofs,
    P b ofs -> perm m_before b ofs Cur Readable ->
    ZMap.get ofs (PMap.get b m_after.(mem_contents)) =
    ZMap.get ofs (PMap.get b m_before.(mem_contents))
}.

Definition unchanged_on := unchanged_on'.

(*X*)
Lemma unchanged_on_refl:
  forall m, unchanged_on m m.
Proof.
  intros; constructor. apply Ple_refl. tauto. tauto.
Qed.

(*X*)
Lemma valid_block_unchanged_on:
  forall m m' b,
  unchanged_on m m' -> valid_block m b -> valid_block m' b.
Proof.
  unfold valid_block; intros. apply unchanged_on_nextblock in H. xomega.
Qed.

(*X*)
Lemma perm_unchanged_on:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto. eapply perm_valid_block; eauto. 
Qed.

(*X*)
Lemma perm_unchanged_on_2:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto.
Qed.

(*X*)
Lemma unchanged_on_trans:
  forall m1 m2 m3, unchanged_on m1 m2 -> unchanged_on m2 m3 -> unchanged_on m1 m3.
Proof.
  intros; constructor.
- apply Ple_trans with (nextblock m2); apply unchanged_on_nextblock; auto.
- intros. transitivity (perm m2 b ofs k p); apply unchanged_on_perm; auto.
  eapply valid_block_unchanged_on; eauto.
- intros. transitivity (ZMap.get ofs (mem_contents m2)#b); apply unchanged_on_contents; auto.
  eapply perm_unchanged_on; eauto. 
Qed.

(*X*)
Lemma loadbytes_unchanged_on_1:
  forall m m' b ofs n,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite ! loadbytes_empty by assumption. auto.
+ unfold loadbytes. destruct H.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true. f_equal.
  apply getN_exten. intros. rewrite nat_of_Z_eq in H by omega.
  apply unchanged_on_contents0; auto.
  red; intros. apply unchanged_on_perm0; auto.
  rewrite pred_dec_false. auto.
  red; intros; elim n0; red; intros. apply <- unchanged_on_perm0; auto.
Qed.

(*X*)
Lemma loadbytes_unchanged_on:
  forall m m' b ofs n bytes,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m b ofs n = Some bytes ->
  loadbytes m' b ofs n = Some bytes.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite loadbytes_empty in * by assumption. auto.
+ rewrite <- H1. apply loadbytes_unchanged_on_1; auto.
  exploit loadbytes_range_perm; eauto. instantiate (1 := ofs). omega.
  intros. eauto with mem.
Qed.

(*X*)
Lemma load_unchanged_on_1:
  forall m m' chunk b ofs,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable).
  destruct v. rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros.
  rewrite <- size_chunk_conv in H4. eapply unchanged_on_contents; eauto.
  split; auto. red; intros. eapply perm_unchanged_on; eauto.
  rewrite pred_dec_false. auto.
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
Qed.

(*X*)
Lemma load_unchanged_on:
  forall m m' chunk b ofs v,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs = Some v ->
  load chunk m' b ofs = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_1; eauto with mem.
Qed.

(*X*)
Lemma store_unchanged_on:
  forall chunk m b ofs v m',
  store chunk m b ofs v = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_store _ _ _ _ _ _ H). apply Ple_refl.
- split; intros; eauto with mem.
- erewrite store_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). omega. auto.
Qed.

(*X*)
Lemma storebytes_unchanged_on:
  forall m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_storebytes _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_storebytes_1; eauto. eapply perm_storebytes_2; eauto.
- erewrite storebytes_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + Z_of_nat (length bytes))); auto.
  elim (H0 ofs0). omega. auto.
Qed.

(*X*)
Lemma alloc_unchanged_on:
  forall m lo hi m' b,
  alloc m lo hi = (m', b) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_alloc _ _ _ _ _ H). apply Ple_succ.
- split; intros.
  eapply perm_alloc_1; eauto.
  eapply perm_alloc_4; eauto.
  eapply valid_not_valid_diff; eauto with mem.
- injection H; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso; auto. rewrite A.  eapply valid_not_valid_diff; eauto with mem.
Qed.

(*X*)
Lemma free_unchanged_on:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_free _ _ _ _ _ H). apply Ple_refl.
- split; intros.
  eapply perm_free_1; eauto.
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
  subst b0. elim (H0 ofs). omega. auto.
  eapply perm_free_3; eauto.
- unfold free in H. destruct (range_perm_dec m b lo hi Cur Freeable); inv H.
  simpl. auto.
Qed.

(*X*)
Lemma drop_perm_unchanged_on:
  forall m b lo hi p m',
  drop_perm m b lo hi p = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_drop _ _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_drop_3; eauto.
  destruct (eq_block b0 b); auto.
  subst b0. 
  assert (~ (lo <= ofs < hi)). { red; intros; eelim H0; eauto. }
  right; omega.
  eapply perm_drop_4; eauto. 
- unfold drop_perm in H. 
  destruct (range_perm_dec m b lo hi Cur Freeable); inv H; simpl. auto.
Qed. 

End UNCHANGED_ON.

(*X*)
Lemma unchanged_on_implies:
  forall (P Q: block -> Z -> Prop) m m',
  unchanged_on P m m' ->
  (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
  unchanged_on Q m m'.
Proof.
  intros. destruct H. constructor; intros.
- auto.
- apply unchanged_on_perm0; auto. 
- apply unchanged_on_contents0; auto. 
  apply H0; auto. eapply perm_valid_block; eauto. 
Qed.

(************************************************************)
(************************************************************)
(***** Stack-Aware CompCert Addendum to the Memory Spec *****)
(************************************************************)
(************************************************************)

(* Decidability proofs to define stack operations *)

Definition zle_zlt_dec:
  forall (a b c: Z), {a <= b < c} + { ~ a <= b < c }.
Proof.
  intros a b c; destruct (zle a b), (zlt b c);[left; omega|right; omega..].
Qed.

Section FORALL.

  Variables P: Z -> Prop.
  Variable f: forall (x: Z), {P x} + {~ P x}.
  Variable lo: Z.

  Program Fixpoint forall_rec (hi: Z) {wf (Zwf lo) hi}:
    {forall x, lo <= x < hi -> P x}
    + {~ forall x, lo <= x < hi -> P x} :=
    if zlt lo hi then
      match f (hi - 1) with
      | left _ =>
        match forall_rec (hi - 1) with
        | left _ => left _ _
        | right _ => right _ _
        end
      | right _ => right _ _
      end
    else
      left _ _
  .
  Next Obligation.
    red. omega.
  Qed.
  Next Obligation.
    assert (x = hi - 1 \/ x < hi - 1) by omega.
    destruct H2. congruence. auto.
  Qed.
  Next Obligation.
    intro F. apply wildcard'. intros; apply F; eauto. omega.
  Qed.
  Next Obligation.
    intro F. apply wildcard'. apply F. omega.
  Qed.
  Next Obligation.
    omegaContradiction.
  Defined.

End FORALL.

Definition dec (P: Prop) := {P} + {~ P}.

Lemma dec_eq:
  forall (P Q: Prop) (EQ: P <-> Q), dec P -> dec Q.
Proof.
  intros P Q EQ D.
  destruct D; [left|right]; tauto.
Qed.

Lemma dec_impl:
  forall (A: Type) (P Q R: A -> Prop)
    (IMPL: forall x, P x -> Q x)
    (DECR: dec (forall x, Q x -> P x -> R x)),
    dec (forall x, P x -> R x).
Proof.
  intros A P Q R IMPL.
  apply dec_eq.
  split; intros; eauto.
Qed.

Lemma perm_impl_prop_dec m b (P: Z -> Prop) (Pdec: forall o, dec (P o)):
  dec (forall o k p, perm m b o k p -> P o).
Proof.
  apply dec_eq with (P := Forall (fun k => forall o p, perm m b o k p -> P o) (Cur::Max::nil)).
  {
    rewrite Forall_forall.
    split; intros; eauto.
    eapply H; eauto.
    destruct k; simpl; auto.
  }
  apply Forall_dec. intro k.
  apply dec_eq with (P := Forall (fun p => forall o, perm m b o k p -> P o) (Nonempty::Readable::Writable::Freeable::nil)).
  {
    rewrite Forall_forall.
    split; intros; eauto.
    eapply H; eauto.
    destruct p; simpl; auto.
  }
  apply Forall_dec. intro p.
  set (PP := fun o : Z => perm m b o k p).
  set (Q := fun o => in_bounds o (mem_bounds m) # b).
  apply (dec_impl _ PP Q P).
  - unfold PP, Q. intros; eapply mem_bounds_perm; eauto.
  - unfold dec, Q. unfold in_bounds. apply forall_rec.
    intro o. unfold PP.
    destruct (Pdec o).
    + left; auto.
    + destruct (perm_dec m b o k p); auto.
      left; intuition.
Defined.

Definition top_frame_no_perm m := 
  top_tframe_prop
    (fun tf =>
       forall b,
         in_frames tf b ->
         forall o k p,
           ~ perm m b o k p) (stack m).

Definition top_tframe_prop_dec (P: tframe_adt -> Prop) (Pdec: forall t, {P t} + { ~ P t}):
  forall s, { top_tframe_prop P s } + { ~ top_tframe_prop P s }.
Proof.
  intros.
  destruct s. right; inversion 1.
  destruct (Pdec t);[left;constructor; auto|right;inversion 1; congruence].
Defined.

Definition top_frame_no_perm_dec m2: { top_frame_no_perm m2 } + { ~ top_frame_no_perm m2}.
Proof.
  apply top_tframe_prop_dec. intros.
  unfold in_frames. destruct (fst t); simpl.
  eapply dec_eq with (Forall (fun b => forall o k p, ~ perm m2 b o k p) (map fst (frame_adt_blocks f))).
  rewrite Forall_forall. unfold in_frame, get_frame_blocks. split; intuition; eauto.
  apply Forall_dec.
  intro. apply perm_impl_prop_dec. right. inversion 1.
  left; inversion 1.
Defined.

Definition valid_frame f m :=
  forall b, in_frame f b -> valid_block m b.

Definition valid_block_dec m b: { valid_block m b } + { ~ valid_block m b }.
Proof.
  apply plt.
Qed.

Definition valid_block_list_dec m l:  { forall b, In b l -> valid_block m b } + { ~ (forall b, In b l -> valid_block m b) }.
Proof.
  induction l; simpl; intros.
  left; tauto.
  destruct IHl, (valid_block_dec m a); intuition.
  left; intros; intuition subst; auto.
Qed.

Definition valid_frame_dec f m: { valid_frame f m } + { ~ valid_frame f m }.
Proof.
  unfold valid_frame; simpl; auto.
  apply valid_block_list_dec.
Qed.

Definition sumbool_not {A} (x: {A} + {~A}): {~A} + {~ (~A)}.
Proof.
  destruct x. right; intro NA. apply NA. apply a.
  left; auto.
Defined.

Definition frame_agree_perms_forall (P: block -> Z -> perm_kind -> permission -> Prop) f :=
  Forall (fun bfi =>
            let '(b,fi) := bfi in
            forall o k p,
              P b o k p -> 0 <= o < frame_size fi
         )(frame_adt_blocks f).

Definition frame_agree_perms_forall_dec m f:
  {frame_agree_perms_forall (perm m) f} + { ~ frame_agree_perms_forall (perm m) f}.
Proof.
  apply Forall_dec. intros [b fi].
  apply perm_impl_prop_dec.
  intro; apply (zle_zlt_dec).
Defined.

Lemma frame_agree_perms_rew:
  forall P f,
    frame_agree_perms P f <-> frame_agree_perms_forall P f.
Proof.
  unfold frame_agree_perms, frame_agree_perms_forall; split; intros; rewrite ? Forall_forall in *; intros.
  - destruct x as [b fi]; intros; eauto.
  - eapply H in H0; eapply H0; eauto.
Qed.

(*X* [push_new_stage] definition *)

Program Definition push_new_stage (m: mem) : mem :=
  (mkmem (mem_contents m)
         (mem_access m)
         (nextblock m)
         (access_max m)
         (nextblock_noaccess m)
         (contents_default m)
         (contents_default' m)
         ((None,nil)::stack m)
         _
         (mem_bounds m)
         (mem_bounds_perm m)).
Next Obligation.
  destruct (mem_stack_inv m).
  constructor.
  - simpl. intuition. contradict H0. unfold in_frames_all; cbn. intuition.
    destruct H0; intuition.
  - constructor; auto.
  - intros tf IN f INN.
    destruct IN; subst; eauto. easy.
  - simpl. change (size_frames (None,nil)) with 0. omega.
  - constructor;auto. intro b. simpl; easy.
Qed.

(*X* [taillcall_stage] definition *)

Definition tailcall_stage_stack (m: mem) : option StackADT.stack :=
  if top_frame_no_perm_dec m
  then Some ((None, opt_cons (fst (hd (None,nil) (stack m))) (snd (hd (None,nil) (stack m))))::tl (stack m))
  else None.

Program Definition tailcall_stage (m: mem) : option mem :=
  match tailcall_stage_stack m with
  | None => None
  | Some s' => Some (mkmem (mem_contents m)
                          (mem_access m)
                          (nextblock m)
                          (access_max m)
                          (nextblock_noaccess m)
                          (contents_default m)
                          (contents_default' m)
                          s'
                          _
                          (mem_bounds m)
                          (mem_bounds_perm m))
  end.
Next Obligation. 
  destruct (mem_stack_inv m).
  unfold tailcall_stage_stack in Heq_anonymous. repeat destr_in Heq_anonymous.
  inv t. rewrite <- H in *.
  constructor.
  - simpl. intros. eapply stack_inv_valid'0. simpl. destruct H1; auto.
    revert H1. unfold in_frames_all. intuition.
    decompose [ex and] H2; simpl in *.
    apply In_opt_cons in H3. destruct H3; eauto. rewrite H1. simpl. eauto.
  - inv stack_inv_norepet0; constructor; simpl; auto.
  - simpl.
    intros tf0 EQ ff INN. simpl in EQ. destruct EQ as [EQ|EQ]. subst. inv INN.
    eapply stack_inv_perms0. right; eauto. eauto.
  - simpl.
    simpl in stack_inv_below_limit0.
    rewrite <- size_frames_eq. auto.
  - inv stack_inv_wf0. constructor;auto. intro b. simpl.
    intros. apply In_opt_cons in H1. destruct H1; eauto.
    eapply H0. eapply in_frame_in_frames; eauto.
Qed.

(** [record_stack_blocks] definition *)

Definition prepend_to_current_stage a (l: StackADT.stack) : option StackADT.stack :=
  match l with
  | (None,b)::r => Some ((Some a,b)::r)
  | _ => None
  end.

Definition mem_stack_wf_plus f m s':
  prepend_to_current_stage f (stack m) = Some s' ->
  wf_stack (perm m) s' .
Proof.
  intros PREP.
  unfold prepend_to_current_stage in PREP; repeat destr_in PREP.
  generalize (mem_stack_inv m); rewrite Heqs. inversion 1. inv stack_inv_wf0.
  constructor; eauto.
Qed.

Lemma mem_stack_inv_plus f m s':
  valid_frame f m ->
  (* (forall b, in_frame f b -> Plt b (nextblock m)) -> *)
  (forall b, in_frame f b -> ~ in_stack (stack m) b) ->
  frame_agree_perms (perm m) f ->
  size_stack (tl (stack m)) + align (frame_adt_size f) 8 < stack_limit ->
  prepend_to_current_stage f (stack m) = Some s' ->
  stack_inv s' (nextblock m) (perm m).
Proof.
  intros VALID NIS FAP SZ PREP.
  generalize (mem_stack_wf_plus _ _ _ PREP). intro WF.
  unfold prepend_to_current_stage in PREP; repeat destr_in PREP. 
  destruct (mem_stack_inv m). rewrite Heqs in *; simpl in *.
  constructor; auto.
  - intro b. simpl. unfold in_frames_all. 
    specialize (stack_inv_valid'0 b). simpl in stack_inv_valid'0. intros.
    simpl in *. intuition eauto.
    apply VALID. auto.
    destruct H as (ff & INFL & IFR). apply H0. red. simpl. right.  eauto.
  - inv stack_inv_norepet0; constructor; auto.
  - intros tf INTF. simpl in *.
    destruct INTF as [INTF|INTF]; eauto. subst.
    simpl in *.
    inversion 1; subst. eauto. 
    eapply stack_inv_perms0; eauto. right; auto.
  - simpl; unfold size_frames in *; simpl in *.
    rewrite Zmax_spec. destr. unfold size_frame at 2 in g. rewrite Z.max_r in stack_inv_below_limit0.
    omega.
    clear.
    induction l; simpl; intros; eauto. omega. apply Z.max_le_iff.
    right; eauto.
Qed.

Program Definition record_stack_blocks (m: mem) (f: frame_adt) : option mem :=
  if valid_frame_dec f m
  then if (Forall_dec _ (fun x => sumbool_not (in_stack_dec (stack m) (fst x))) (frame_adt_blocks f))
       then if (zlt (size_stack (tl (stack m)) + align (Z.max 0 (frame_adt_size f)) 8) stack_limit)
            then if frame_agree_perms_forall_dec m f
                 then
                   match prepend_to_current_stage f (stack m) with
                   | Some s =>
                     Some
                       (mkmem (mem_contents m)
                              (mem_access m)
                              (nextblock m)
                              (access_max m)
                              (nextblock_noaccess m)
                              (contents_default m)
                              (contents_default' m)
                              s
                              _
                              (mem_bounds m)
                              (mem_bounds_perm m))
                   | _ => None
                   end
                 else None
            else None
       else None
  else None.
Next Obligation.
  eapply mem_stack_inv_plus.
  eauto.
  intros; rewrite Forall_forall in H0.
  edestruct in_frame_info as (fi & IN); eauto.
  eapply H0 in IN; eauto.
  apply frame_agree_perms_rew; auto.
  rewrite Z.max_r in H1; auto. destruct f; auto. auto.
Qed.

(* [unrecord_stack_block] definition *)

Lemma mem_stack_inv_tl:
  forall m, stack_inv (tl (stack m)) (nextblock m) (perm m).
Proof.
  intro m. destruct (mem_stack_inv m).
  constructor; auto.
  - intros; eapply stack_inv_valid'0.
    destruct (stack m); simpl in *; auto.
  - apply nodup_tl; auto.
  - apply stack_agree_perms_tl; auto.
  - eapply Z.le_lt_trans. apply size_stack_tl; auto. auto.
  - eauto using wf_stack_tl.
Qed.

Definition unrecord_stack_block (m: mem) : option mem :=
  match stack m with
    nil => None
  | a::r => Some ((mkmem (mem_contents m)
                        (mem_access m)
                        (nextblock m)
                        (access_max m)
                        (nextblock_noaccess m)
                        (contents_default m)
                        (contents_default' m)
                        (tl (stack m))
                        (mem_stack_inv_tl _)
                        (mem_bounds m)
                        (mem_bounds_perm m)
                ))
  end.


(* [record_init_sp] definition *)

Definition record_init_sp m :=
  let (m1, b1) := Mem.alloc (Mem.push_new_stage m) 0 0 in
  Mem.record_stack_blocks m1 (make_singleton_frame_adt b1 0 0).

(* [loadbytesv] definition *)

Definition is_ptr (v: val) :=
  match v with Vptr _ _ => Some v | _ => None end.
  
Definition encoded_ra (l: list memval) : option val :=
  match proj_bytes l with
  | Some bl => Some (Vptrofs (Ptrofs.repr (decode_int bl)))
  | None => is_ptr (Val.load_result Mptr (proj_value (quantity_chunk Mptr) l))
  end.

Definition loadbytesv chunk m addr :=
  match addr with
    Vptr b o =>
    match Mem.loadbytes m b (Ptrofs.unsigned o) (size_chunk chunk) with
      | Some bytes => encoded_ra bytes
      | None => None
    end
  | _ => None
  end.

(** Basic Stack Properties*)

Theorem empty_stack:
  stack empty = nil.
Proof.
reflexivity.
Qed.

Theorem size_stack_below:
  forall m, size_stack (stack m) < stack_limit.
Proof.
  intros. eapply stack_inv_below_limit, mem_stack_inv.
Qed.

Theorem wf_stack_mem:
  forall m,
  wf_stack (perm m) (stack m).
Proof.
  intros. eapply stack_inv_wf, mem_stack_inv.
Qed.

Theorem get_frame_info_valid:
  forall m b f, get_frame_info (stack m) b = Some f -> valid_block m b.
Proof.
  intros. eapply in_stack_valid. eapply get_frame_info_in_stack; eauto.
Qed.

Lemma stack_top_valid:
  forall m b, is_stack_top (stack m) b -> valid_block m b.
Proof.
  intros.
  eapply stack_top_in_frames in H.
  inversion H. 
  apply in_stack_valid. destruct H0. apply (in_frames_in_stack (stack m) x b).
  - assumption.
  - assumption.
Qed.

(* Original operations don't modify the stack. *)

Lemma freelist_stack_unchanged:
  forall bl m m',
  free_list m bl = Some m' ->
  stack m' = stack m.
Proof.
  induction bl; simpl; intros; autospe. 
  reflexivity.
  eapply free_stack_unchanged in Heqo. congruence.
Qed.

(* Properties of [storebytes] *)

Lemma storebytes_get_frame_info:
  forall m1 b o v m2,
    storebytes m1 b o v = Some m2 ->
    forall b', get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.
Proof.
  unfold storebytes.
  intros.
  destruct (range_perm_dec m1 b o (o + Z.of_nat (length v)) Cur Writable); 
  try discriminate. inv H.
  unfold get_frame_info. reflexivity. 
Qed.

Lemma storebytes_is_stack_top:
  forall m1 b o v m2,
    storebytes m1 b o v = Some m2 ->
    forall b', is_stack_top (stack m2) b' <-> is_stack_top (stack m1) b'.
Proof.
  unfold storebytes.
  intros.
  destruct (range_perm_dec m1 b o (o + Z.of_nat (length v)) Cur Writable); try discriminate. 
  inv H.
  unfold is_stack_top, get_stack_top_blocks. simpl. tauto.
Qed.


(* Properties of [alloc] *)

Lemma alloc_get_frame_info:
  forall m1 lo hi m2 b, 
  alloc m1 lo hi = (m2, b) ->
  forall b', get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.
Proof.
  intros m1 lo hi m2 b ALLOC.
  unfold alloc in ALLOC. inv ALLOC. reflexivity.
Qed.

Lemma alloc_is_stack_top:
  forall m1 lo hi m2 b,
  alloc m1 lo hi = (m2, b) ->
  forall b', is_stack_top (stack m2) b' <-> is_stack_top (stack m1) b'.
Proof.
  intros m1 lo hi m2 b ALLOC.
  unfold alloc in ALLOC. inv ALLOC. reflexivity.
Qed.

Lemma alloc_get_frame_info_fresh:
  forall m1 lo hi m2 b, 
  alloc m1 lo hi = (m2, b) ->
  get_frame_info (stack m2) b = None.
Proof.
  intros; eapply not_in_stack_get_assoc; auto.
  rewrite (alloc_stack_unchanged _ _ _ _ _ H); eauto.
  intro IN; apply in_stack_valid in IN.
  eapply fresh_block_alloc in IN; eauto.
Qed.

(* Properties of [free]*)

Lemma free_get_frame_info:
  forall m1 b lo hi m2 b',
    free m1 b lo hi = Some m2 ->
    get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.
Proof.
  intros; erewrite free_stack_unchanged; eauto.
Qed.

Lemma perm_free:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  forall b' o' k p,
  perm m' b' o' k p <-> ((~ (b' = b /\ lo <= o' < hi)) /\ perm m b' o' k p).
Proof.
  intros m b lo hi m' H b' o' k p.
  assert (~ (b' = b /\ lo <= o' < hi) -> perm m b' o' k p -> perm m' b' o' k p) as H0.
  {
    intro H0.
    eapply perm_free_1; eauto.
    destruct (peq b' b); try tauto.
    subst.
    intuition xomega.
  }
  assert (b' = b /\ lo <= o' < hi -> ~ perm m' b' o' k p) as H1.
  destruct 1; subst; eapply perm_free_2; eauto.
  generalize (perm_free_3 _ _ _ _ _ H b' o' k p).
  tauto.
Qed.

Lemma free_no_perm_stack:
  forall m b sz m',
  free m b 0 sz = Some m' ->
  forall bi,
  in_stack' (stack m) (b, bi) ->
  frame_size bi = Z.max 0 sz ->
  forall o k p,
    ~ perm m' b o k p.
Proof.
  intros. rewrite perm_free. 2: eauto.
  intros (NORANGE & P).
  apply NORANGE. split; auto.
  rewrite in_stack'_rew in H0. destruct H0 as (tf & IFR & INS).
  rewrite in_frames'_rew in IFR. destruct IFR as (fr & IFR & EQfr).
  exploit stack_perm. apply INS. eauto. apply IFR. eauto. rewrite H1.
  rewrite Zmax_spec. destr. omega.
Qed.

(* Properties of [free_list] *)

Lemma free_no_perm_stack':
  forall m b sz m',
  free m b 0 sz = Some m' ->
  forall bi f0 r s0 l,
  stack m = (Some f0, r) :: s0 ->
  frame_adt_blocks f0 = (b, bi) :: l ->
  frame_size bi = Z.max 0 sz ->
  forall o k p,
  ~ perm m' b o k p.
Proof.
  intros; eapply free_no_perm_stack; eauto.
  rewrite H0; left. red; simpl; red. rewrite H1. left; reflexivity.
Qed.

Lemma free_top_tframe_no_perm:
  forall m b sz m' bi f0 r s0,
  free m b 0 sz = Some m' ->
  stack m = (Some f0, r) :: s0 ->
  frame_adt_blocks f0 = (b, bi) :: nil ->
  frame_size bi = Z.max 0 sz ->
  top_frame_no_perm m'.
Proof.
  intros.
  red. erewrite free_stack_unchanged; eauto.
  rewrite H0.
  constructor.
  generalize (wf_stack_mem m). rewrite H0. intro A; inv A.
  unfold in_frames. simpl. unfold get_frame_blocks. rewrite H1.
  simpl. intros bb [EQ|[]].
  subst. simpl in *.
  intros; eapply free_no_perm_stack'; eauto.
Qed.

Lemma free_top_tframe_no_perm':
  forall m b sz m' bi f0 r s0,
  free m b 0 sz = Some m' ->
  stack m = (Some f0, r) :: s0 ->
  frame_adt_blocks f0 = (b, bi) :: nil ->
  frame_size bi = sz ->
  top_frame_no_perm m'.
Proof.
  intros.
  eapply free_top_tframe_no_perm; eauto.
  rewrite Z.max_r. auto. subst; apply frame_size_pos.
Qed.

(* Properties of [store] *)

Theorem store_get_frame_info:
  forall chunk m1 b o v m2,
  (store chunk m1 b o v = Some m2) ->
  forall b', get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.
Proof.
  intros. erewrite store_stack_unchanged; eauto.
Qed.

Theorem store_is_stack_top:
   forall chunk m1 b o v m2, 
   store chunk m1 b o v = Some m2 ->
   forall b', is_stack_top (stack m2) b' <-> is_stack_top (stack m1) b'.
Proof.
  intros; erewrite store_stack_unchanged; eauto. tauto.
Qed.

(* Properties of [storev] *)

Theorem storev_nextblock :
  forall m chunk addr v m',
  storev chunk m addr v = Some m' ->
  nextblock m' = nextblock m.
Proof.
  intros; destruct addr; simpl in *; try congruence.
  eapply nextblock_store; eauto.
Qed.

Theorem storev_perm_inv:
  forall m chunk addr v m',
  storev chunk m addr v = Some m' ->
  forall b o k p,
  perm m' b o k p ->
  perm m b o k p.
Proof.
  intros; destruct addr; simpl in *; try congruence.
  eapply perm_store_2; eauto.
Qed.

(** Properties of [extends] *)

Theorem extends_extends_compos:
  forall m1 m2 m3,
  extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof.
  intros. inversion H; inversion H0; constructor; intros.
  (* nextblock *)
  congruence.
  (* meminj *)
  replace inject_id with (compose_meminj inject_id inject_id).
  eapply mem_inj_compose; eauto.
  rewrite mext_length_stack0.
  apply compose_frameinj_same.
  apply extensionality; intros. unfold compose_meminj, inject_id. auto.
  (* perm inv *)
  exploit mext_perm_inv1; eauto. intros [A|A]. 
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
  congruence.
Qed.

Lemma is_stack_top_inj:
  forall f g m1 m2 b1 b2 delta,
  mem_inj f g m1 m2 ->
  f b1 = Some (b2, delta) ->
  (exists o k p, perm m1 b1 o k p) ->
  is_stack_top (stack m1) b1 -> is_stack_top (stack m2) b2.
Proof.
  intros. inv H.
  eapply is_stack_top_inj_gen; eauto.
Qed.

Theorem is_stack_top_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (exists (o : Z) (k : perm_kind) (p : permission), perm m1 b o k p) ->
  is_stack_top (stack m1) b ->
  is_stack_top (stack m2) b.
Proof.
  intros.
  inv H.
  eapply is_stack_top_inj; eauto. inv mext_inj0; eauto. reflexivity.
Qed.

Definition mem_unchanged (T: mem -> mem -> Prop) :=
  forall m1 m2, T m1 m2 ->
           nextblock m2 = nextblock m1
           /\ (forall b o k p, perm m2 b o k p <-> perm m1 b o k p)
           /\ (forall P, unchanged_on P m1 m2)
           /\ (forall b o chunk, load chunk m2 b o = load chunk m1 b o).

(** Weak Memory injections *)

Record weak_inject' (f: meminj) (g: frameinj) (m1 m2: mem) : Prop :=
  mk_weak_inject {
    mwi_inj:
      mem_inj f g m1 m2;
    mwi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mwi_no_overlap:
      meminj_no_overlap f m1;
    mwi_representable:
      forall b b' delta,
      f b = Some(b', delta) ->
      delta >= 0
      /\
      forall ofs,
        perm m1 b (Ptrofs.unsigned ofs) Max Nonempty
        \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
        0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mwi_perm_inv:
      forall b1 ofs b2 delta k p,
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
  }.

Definition weak_inject := weak_inject'.

(** Properties of [inject]*)

(** The following lemmas establish the absence of g machine integer overflow
  during address computations. *)

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Theorem inject_delta_pos:
  forall f g m1 m2 b1 b2 delta,
  inject f g m1 m2 ->
  f b1 = Some (b2, delta) ->
  delta >= 0.
Proof.
  intros.
  exploit mi_representable; eauto. intuition.
Qed.

Lemma mem_inj_ext:
  forall j1 j2 g m1 m2,
  mem_inj j1 g m1 m2 ->
  (forall x, j1 x = j2 x) ->
  mem_inj j2 g m1 m2.
Proof.
  intros j1 j2 g m1 m2 INJ EXT.
  inv INJ; constructor; auto; intros; rewrite <- ? EXT in *; eauto.
  eapply memval_inject_ext; eauto.
  eapply stack_inject_ext'; eauto.
Qed.

Theorem inject_ext:
  forall f f' g m1 m2,
  inject f g m1 m2 ->
  (forall b, f b = f' b) ->
  inject f' g m1 m2.
Proof.
  intros.
  inv H; constructor; auto; intros; rewrite <- ? H0 in *; eauto.
  eapply mem_inj_ext; eauto.
  red; intros. eapply mi_no_overlap0; rewrite ? H0; eauto.
Qed.

Lemma weak_valid_pointer_nonempty_perm:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <-> 
  (perm m b ofs Cur Nonempty) \/ (perm m b (ofs-1) Cur Nonempty).
Proof.
  intros. unfold weak_valid_pointer. unfold valid_pointer.
  destruct (perm_dec m b ofs Cur Nonempty); destruct (perm_dec m b (ofs-1) Cur Nonempty); simpl;
  intuition congruence.
Qed.

Lemma weak_valid_pointer_size_bounds : forall f g b1 b2 m1 m2 ofs delta,
  f b1 = Some (b2, delta) ->
  inject f g m1 m2 ->
  weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= delta <= Ptrofs.max_unsigned /\
  0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned.
Proof.
  intros. exploit mi_representable; eauto. intros [A B].
  rewrite weak_valid_pointer_nonempty_perm in H1.
  exploit B; eauto. 
  destruct H1; eauto with mem. intros.
  generalize (Ptrofs.unsigned_range ofs). omega.
Qed.

(*X* SACC:*)
Theorem valid_pointer_inject': 
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. exploit valid_pointer_inject; eauto. intros.
  intros. unfold Ptrofs.add.
  exploit weak_valid_pointer_size_bounds; eauto. 
  erewrite weak_valid_pointer_spec; eauto.
  intros [A B].
  repeat rewrite Ptrofs.unsigned_repr; auto.
Qed.

Theorem weak_valid_pointer_inject': 
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. exploit weak_valid_pointer_inject; eauto.
  intros. unfold Ptrofs.add.
  exploit weak_valid_pointer_size_bounds; eauto. intros [A B].
  repeat rewrite Ptrofs.unsigned_repr; auto.
Qed.

Lemma nth_getN_refl : forall n ofs ofs' mcontents,
        ofs' >= ofs -> ofs' < ofs + Z.of_nat n ->
        nth (nat_of_Z (ofs' - ofs)) (getN n ofs mcontents) Undef = ZMap.get ofs' mcontents.
Proof.
  induction n; intros; simpl in *.
  - omega.
  - rewrite Zpos_P_of_succ_nat in H0.
    assert (ofs' - ofs = 0 \/ ofs' - ofs > 0) by omega.
    destruct H1. 
    + rewrite H1. simpl. assert (ofs' = ofs) by omega. subst ofs. auto.
    + rewrite nat_of_Z_succ; auto.
      replace (ofs' - ofs - 1) with (ofs' - (ofs+1)) by omega.
      apply IHn; omega.
Qed.

Lemma nth_setN_refl : forall lv ofs' ofs mcontents,
  ofs' >= ofs -> ofs' < ofs + Zlength lv ->
  nth (nat_of_Z (ofs' - ofs)) lv Undef = ZMap.get ofs' (setN lv ofs mcontents).
Proof.
  induction lv; simpl in *; intros.
  - rewrite Zlength_correct in H0. simpl in *. omega.
  - rewrite Zlength_correct in H0. simpl in *. 
    rewrite Zpos_P_of_succ_nat in *. 
    assert (ofs' = ofs \/ ofs' > ofs) by omega. destruct H1.
    + subst ofs'. replace (ofs - ofs) with 0 by omega. simpl.
      erewrite setN_outside; eauto. rewrite ZMap.gss. auto. omega.
    + rewrite nat_of_Z_succ; auto.
      replace (ofs' - ofs - 1) with (ofs' - (ofs+1)) by omega.
      apply IHlv. omega. 
      rewrite Zlength_correct. omega.
      omega.
Qed.

Lemma store_right_inj:
  forall f g m1 m2 chunk b ofs v m2',
    mem_inj f g m1 m2 ->
    (forall b' delta ofs',
        f b' = Some(b, delta) ->
        ofs' + delta = ofs ->
        exists vl, loadbytes m1 b' ofs' (size_chunk chunk) = Some vl /\
        list_forall2 (memval_inject f) vl (encode_val chunk v)) ->
    store chunk m2 b ofs v = Some m2' ->
    mem_inj f g m1 m2'.
Proof.
  intros. inv H. constructor.
  - (* perm *)
    eauto with mem.
  - (* access *)
    intros; eapply mi_align0; eauto.
  - (* mem_contents *)
    intros.
    rewrite (store_mem_contents _ _ _ _ _ _ H1).
    rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
    destruct (zlt (ofs0 + delta) ofs).
    rewrite setN_outside. auto. omega.
    destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)).
    rewrite setN_outside. auto. rewrite encode_val_length.
    rewrite <- size_chunk_conv. omega.
    exploit (H0 b1 delta (ofs-delta) H); eauto. omega.
    intros (vl & LBYTES& MVALSINJ). unfold loadbytes in LBYTES.
    destruct (range_perm_dec m1 b1 (ofs - delta) (ofs - delta + size_chunk chunk) Cur Readable); inv LBYTES.
    set (ofs'' := ofs0 + delta - ofs).
    set (l1 := (getN (size_chunk_nat chunk) (ofs - delta) (mem_contents m1) # b1)) in *.
    set (l2 := (encode_val chunk v)) in *.
    assert (memval_inject f (nth (nat_of_Z ofs'') l1 Undef) (nth (nat_of_Z ofs'') l2 Undef)).
    eapply list_forall2_in; eauto. constructor.
    subst ofs''. omega. subst ofs''. 
    rewrite Zlength_correct. 
    subst l1. rewrite getN_length. rewrite <- size_chunk_conv. omega.
    subst ofs'' l1 l2.    
    erewrite <- (nth_getN_refl (size_chunk_nat chunk) (ofs-delta) ofs0).
    replace (ofs0 - (ofs - delta)) with (ofs0 + delta - ofs). 
    erewrite <- nth_setN_refl; try omega. auto. 
    rewrite Zlength_correct. rewrite encode_val_length.
    rewrite <- size_chunk_conv. omega.
    omega. omega. rewrite <- size_chunk_conv. omega.
    auto.
  - rewrite (store_stack_unchanged _ _ _ _ _ _ H1).
    eapply stack_inject_invariant_strong.
    2: eauto. tauto.
Qed.


Theorem store_right_inject:
  forall f g m1 m2 chunk b ofs v m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
   f b' = Some(b, delta) ->
   ofs' + delta = ofs ->
   exists vl, loadbytes m1 b' ofs' (size_chunk chunk) = Some vl /\
              list_forall2 (memval_inject f) vl (encode_val chunk v)) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f g m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply store_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  eauto with mem.
(* perm inv *)
  intros. eauto using perm_store_2.
Qed.

Theorem drop_parallel_inject:
  forall f g m1 m2 b1 b2 delta lo hi p m1',
  inject f g m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ inject f g m1' m2'.
Proof.
  intros. inversion H. 
  exploit drop_mapped_inj; eauto.

  intros (m2' & DPERM & MEMINJ).
  exists m2'. split. auto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. exploit mi_representable; try eassumption.
  intros [A B]; split; eauto. intros ofs0 P. eapply B.
  destruct P; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_drop_4. 
  intuition eauto using perm_drop_4.
  destruct (eq_block b0 b1). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi). 
  rewrite H1 in H2. inv H2.
  assert (perm_order p p0). eapply perm_drop_2; eauto. omega.
  assert (perm m1' b1 ofs k p). eapply perm_drop_1; eauto.
  left. eauto with mem.
  left. eapply perm_drop_3; eauto. right. right. omega.
  left. eapply perm_drop_3; eauto. right. left. omega.
  left. eapply perm_drop_3; eauto. 
Qed.

Lemma drop_right_inj: forall f g m1 m2 b lo hi p m2',
  mem_inj f g m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs' k p',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' k p' ->
    lo <= ofs' + delta < hi -> p' = p) ->
  mem_inj f g m1 m2'.
Proof.
  intros. inv H. constructor.
  (* perm *)
  intros.  
  destruct (eq_block b2 b); auto. subst b2. 
  destruct (zlt (ofs + delta) lo). eapply perm_drop_3; eauto.
  destruct (zle hi (ofs + delta)). eapply perm_drop_3; eauto.
  exploit H1; eauto. omega. intros. subst p0.
  eapply perm_drop_1; eauto. omega.
  eapply perm_drop_3; eauto.
  (* align *)
  eapply mi_align0; eauto.
  (* contents *)
  intros.
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
  apply mi_memval0; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m2 b lo hi Cur Freeable); inv H0; auto.
  (* stack *)
  rewrite (drop_perm_stack_unchanged _ _ _ _ _ _ H0). auto.
Qed.

Theorem drop_right_inject: 
  forall f g m1 m2 b lo hi p m2',
  inject f g m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs' k p',
   f b' = Some(b, delta) ->
   perm m1 b' ofs' k p' ->
   lo <= ofs' + delta < hi -> p' = p) ->
   inject f g m1 m2'.
Proof.
  intros. destruct H. constructor; eauto.
  eapply drop_right_inj; eauto.
  intros. unfold valid_block in *. erewrite nextblock_drop; eauto.
  intros. eapply mi_perm_inv0; eauto using perm_drop_4.
Qed.

Lemma drop_partial_mapped_inj:
  forall f g m1 m2 b1 b2 delta lo1 hi1 lo2 hi2 p m1',
  mem_inj f g m1 m2 ->
  drop_perm m1 b1 lo1 hi1 p = Some m1' ->
  f b1 = Some(b2, delta) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  range_perm m2 b2 (lo2 + delta) (hi2 + delta) Cur Freeable ->
  meminj_no_overlap f m1 ->
  (* no source memory location with non-empty permision 
     injects into the following region in b2 in the target memory: 
     [lo2, lo1)
     and
     [hi1, hi2)
  *)
  (forall b' delta' ofs' k p,
    f b' = Some(b2, delta') ->
    perm m1 b' ofs' k p ->
    ((lo2 + delta <= ofs' + delta' < lo1 + delta )
     \/ (hi1 + delta <= ofs' + delta' < hi2 + delta)) -> False) ->
  exists m2',
      drop_perm m2 b2 (lo2 + delta) (hi2 + delta) p = Some m2'
   /\ mem_inj f g m1' m2'.
Proof.
  intros. 
  assert (exists m2', drop_perm m2 b2 (lo2 + delta) (hi2 + delta) p = Some m2' ) as X.
  apply range_perm_drop_2. apply H4.
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H.
  constructor.
(* perm *)
  intros.
  assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
  destruct (eq_block b1 b0).
  (* b1 = b0 *)
  subst b0. rewrite H1 in H; inv H.
  destruct (zlt (ofs + delta0) (lo1 + delta0)). 
  destruct (zlt (ofs + delta0) (lo2 + delta0)).
  eapply perm_drop_3; eauto.
  exfalso. apply H6 with b1 delta0 ofs k p0; auto.
  eapply perm_drop_4; eauto.
  left. omega.
  destruct (zle (hi1 + delta0) (ofs + delta0)). 
  destruct (zle (hi2 + delta0) (ofs + delta0)).
  eapply perm_drop_3; eauto.
  exfalso. apply H6 with b1 delta0 ofs k p0; auto.
  eapply perm_drop_4; eauto.
  right. omega.
  assert (perm_order p p0).
    eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). omega. eauto.
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. omega.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  destruct (eq_block b3 b2); auto. subst.
  destruct (zlt (ofs + delta0) (lo2 + delta)); auto.
  destruct (zle (hi2 + delta) (ofs + delta0)); auto.
  destruct (zlt (ofs + delta0) (lo1 + delta)).
  exfalso. apply H6 with b0 delta0 ofs k p0; auto. eapply perm_drop_4; eauto. left. omega.
  destruct (zle (hi1 + delta) (ofs + delta0)).
  exfalso. apply H6 with b0 delta0 ofs k p0; auto. eapply perm_drop_4; eauto. right. omega.
  exploit H5; eauto.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable.
  eapply range_perm_drop_1; eauto. omega. auto with mem.
  eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.
  eauto with mem.
  intuition.

(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* memval *)
  intros.
  replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
  replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in DROP; destruct (range_perm_dec m2 b2 (lo2 + delta) (hi2 + delta) Cur Freeable); inv DROP; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b1 lo1 hi1 Cur Freeable); inv H0; auto.
(* stack *)
  rewrite (drop_perm_stack_unchanged _ _ _ _ _ _ H0).
  rewrite (drop_perm_stack_unchanged _ _ _ _ _ _ DROP).
  eapply stack_inject_invariant_strong. 2: eauto.
  intros. eapply perm_drop_4; eauto.
Qed.

Theorem drop_extended_parallel_inject:
  forall f g m1 m2 b1 b2 delta lo1 hi1 lo2 hi2 p m1',
  inject f g m1 m2 ->
  drop_perm m1 b1 lo1 hi1 p = Some m1' ->
  f b1 = Some(b2, delta) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  range_perm m2 b2 (lo2 + delta) (hi2 + delta) Cur Freeable ->
  (* no source memory location with non-empty permision 
     injects into the following region in b2 in the target memory: 
     [lo2, lo1)
     and
     [hi1, hi2)
  *)
  (forall b' delta' ofs' k p,
    f b' = Some(b2, delta') ->
    perm m1 b' ofs' k p ->
    ((lo2 + delta <= ofs' + delta' < lo1 + delta )
     \/ (hi1 + delta <= ofs' + delta' < hi2 + delta)) -> False) ->
  exists m2',
      drop_perm m2 b2 (lo2 + delta) (hi2 + delta) p = Some m2'
   /\ inject f g m1' m2'.
Proof.
  intros. inversion H. 
  exploit drop_partial_mapped_inj; eauto.
  intros (m2' & DPERM & MEMINJ).
  exists m2'. split. auto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. exploit mi_representable; try eassumption.
  intros [A B]; split; eauto. intros ofs0 P. eapply B.
  destruct P; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_drop_4. 
  intuition eauto using perm_drop_4.
  destruct (eq_block b0 b1). subst b0.
  destruct (zle lo1 ofs). destruct (zlt ofs hi1). 
  rewrite H1 in H6. inv H6.
  assert (perm_order p p0). eapply perm_drop_2; eauto. omega.
  assert (perm m1' b1 ofs k p). eapply perm_drop_1; eauto.
  left. eauto with mem.
  left. eapply perm_drop_3; eauto. right. right. omega.
  left. eapply perm_drop_3; eauto. right. left. omega.
  left. eapply perm_drop_3; eauto.
Qed.

Theorem inject_stack_inj_wf:
  forall f g m1 m2,
  inject f g m1 m2 ->
  sum_list g = length (stack m1) /\ length g = length (stack m2).
Proof.
    inversion 1. inv mi_inj0. eauto.
    split.
    eapply stack_inject_length_l; eauto.
    eapply stack_inject_length_r; eauto.
Qed.

Theorem is_stack_top_inject:
  forall f g m1 m2 b1 b2 delta,
  inject f g m1 m2 ->
  f b1 = Some (b2, delta) ->
  (exists (o : Z) (k : perm_kind) (p : permission), perm m1 b1 o k p) ->
  is_stack_top ( (stack m1)) b1 -> is_stack_top ( (stack m2)) b2.
Proof.
  intros.
  eapply is_stack_top_inj; eauto. inv H; eauto.
Qed.

Lemma record_stack_inject_left_zero:
  forall j g m1 s1 s2 f1 f2 l
    (FAP: frame_at_pos s2 0 f2)
    (FI: tframe_inject j m1 f1 f2)
    (SI: stack_inject j m1 g ((None,l) :: s1) s2),
    stack_inject j m1 g (f1 :: s1) s2.
Proof.
  intros j g m1 s1 s2 f1 f2 l FAP FI SI.
  inv SI.
  - simpl in TAKE; repeat destr_in TAKE.
    apply frame_at_pos_last in FAP; subst.
    econstructor. simpl. rewrite Heqo. eauto. all: eauto.
    inv FI0; constructor; auto.
Qed.

Lemma destr_dep_match:
  forall {A B: Type} (a: option A) (x: B)
    (T: forall x (pf: Some x = a), B)
    (MATCH: match a as ano return (ano = a -> option B) with
            | Some m1 => fun Heq: Some m1 = a => Some (T _ Heq)
            | None => fun Heq => None
            end eq_refl = Some x) ,
  forall P: B -> Prop,
    (forall m (pf: Some m = a) x, T m pf = x -> P x) ->
    P x.
Proof.
  intros. destr_in MATCH. subst. inv MATCH. eapply H. eauto.
Qed.

Lemma record_stack_blocks_mem_inj_left_zero:
  forall j g m1 m2 f1 f2 m1',
    mem_inj j g m1 m2 ->
    (* top_is_new m1 -> *)
    record_stack_blocks m1 f1 = Some m1' ->
    frame_at_pos (stack m2) O f2 ->
    tframe_inject j (perm m1) (Some f1,nil) f2 ->
    mem_inj j g m1' m2.
Proof.
  intros j g m1 m2 f1 f2 m1' INJ ADT FAP FI; autospe.
  unfold record_stack_blocks in ADT; repeat destr_in ADT.
  pattern m1'.
  eapply destr_dep_match. apply H0. clear H0. simpl; intros. inv H.
  inversion INJ; subst; constructor; simpl; intros; eauto.
  eapply stack_inject_invariant_strong.
  intros. change (perm m1 b ofs k p) in H0. apply H0.
  unfold prepend_to_current_stage in pf. repeat destr_in pf.
  eapply record_stack_inject_left_zero; eauto.
Qed.

Theorem record_stack_blocks_mem_unchanged:
  forall bfi,
  mem_unchanged (fun m1 m2 => record_stack_blocks m1 bfi = Some m2).
Proof.
  red; intros. unfold record_stack_blocks in H.
  repeat destr_in H.
  pattern m2; eapply destr_dep_match. apply H1. clear H1.
  simpl; intros. subst. simpl.
  repeat split; simpl; auto. xomega.
Qed.

Theorem record_stack_block_inject_left_zero:
  forall m1 m1' m2 j g f1 f2,
  inject j g m1 m2 ->
  frame_at_pos (stack m2) O f2 ->
  tframe_inject j (perm m1) (Some f1,nil) f2 ->
  record_stack_blocks m1 f1 = Some m1' ->
  inject j g m1' m2.
Proof.
  intros.
  inversion H; eauto.
  exploit record_stack_blocks_mem_inj_left_zero; eauto.
  intro MINJ.
  edestruct (record_stack_blocks_mem_unchanged _ _ _ H2) as (NB1 & PERM1 & U1 & C1) ; simpl in *.
  inversion H; econstructor; simpl; intros; eauto.
  + eapply mi_freeblocks0; eauto.
    unfold valid_block in H3; rewrite NB1 in H3; eauto.
  + red; intros.
    rewrite PERM1 in H7, H6.
    eapply mi_no_overlap0; eauto.
  + exploit mi_representable0; eauto.
    intros (A & B); split; auto. intro ofs; rewrite ! PERM1. eauto.
  + rewrite ! PERM1. eapply mi_perm_inv0 in H4; eauto.
Qed.

Ltac unfold_unrecord' H m :=
  unfold unrecord_stack_block in H;
  let A := fresh in
  case_eq (stack m); [
    intro A
  | intros ? ? A
  ]; setoid_rewrite A in H; inv H.
Ltac unfold_unrecord :=
  match goal with
    H: unrecord_stack_block ?m = _ |- _ => unfold_unrecord' H m
  end.

Lemma unrecord_stack_block_mem_unchanged:
  mem_unchanged (fun m1 m2 => unrecord_stack_block m1 = Some m2).
Proof.
  red; intros.
  unfold_unrecord; simpl; repeat split; eauto.
  simpl. xomega.
Qed.

Lemma unrecord_stack_inject_left_zero:
  forall j n g m1 f s1 s2
    (SI: stack_inject j m1 (S n :: g) (f :: s1) s2)
    (LE: (1 <= n)%nat)
(*    (TOPNOPERM: top_tframe_prop (fun tf => forall b, in_frames tf b -> forall o k p, ~ m1 b o k p) (f::s1)) *),
    stack_inject j m1 (n :: g) s1 s2.
Proof.
  intros j n g m1 f s1 s2 SI LE (*TOPNOPERM*).
  inv SI.
  simpl in TAKE; repeat destr_in TAKE.
  destruct n. omega.
  econstructor; eauto. inv FI; auto.
Qed.

Lemma unrecord_stack_block_mem_inj_left_zero:
  forall (m1 m1' m2 : mem) (j : meminj) n g,
    mem_inj j (S n :: g) m1 m2 ->
    unrecord_stack_block m1 = Some m1' ->
(*    top_frame_no_perm m1 -> *)
    (1 <= n)%nat ->
    mem_inj j (n :: g) m1' m2.
Proof.
  intros m1 m1' m2 j n g MI USB LE.
  unfold_unrecord.
  inv MI; constructor; simpl; intros; eauto.
  eapply stack_inject_invariant_strong.
  - intros b ofs k p b' delta JB PERM. change (perm m1 b ofs k p) in PERM. eauto.
  - rewrite H in *. simpl in *.
    eapply unrecord_stack_inject_left_zero; eauto.
Qed.

Theorem unrecord_stack_block_inject_left_zero:
  forall (m1 m1' m2 : mem) (j : meminj) n g,
  inject j (S n :: g) m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  (1 <= n)%nat ->
  inject j (n :: g) m1' m2.
Proof.
  intros m1 m1' m2 j n g INJ USB LE.
  generalize (unrecord_stack_block_mem_unchanged _ _ USB). simpl. intros (NB & PERM & UNCH & LOAD).
  inv INJ; constructor; eauto.
  - eapply unrecord_stack_block_mem_inj_left_zero; eauto. 
  - unfold valid_block; rewrite NB; eauto.
  - red; intros. rewrite PERM in H2, H3. eauto.
  - intros. exploit mi_representable0.  eauto. intros (A & B).
    split; auto. intros ofs. rewrite ! PERM. eauto.
  - intros. rewrite ! PERM; eauto.
Qed.

(** The following property is needed by Unusedglobproof, to prove
    injection between the initial memory states. *)

Theorem self_inject:
  forall f m,
  (forall b, f b = None \/ f b = Some (b, 0)) ->
  (forall b, f b <> None -> valid_block m b) ->
  (forall b,
     f b <> None ->
     forall o b' o' q n,
       loadbytes m b o 1 = Some (Fragment (Vptr b' o') q n :: nil) ->
       f b' <> None) ->
  inject f (flat_frameinj (length (stack m))) m m.
Proof.
  intros.
  assert (F_EQ : forall b b' delta, f b = Some (b', delta) -> b' = b /\ delta = 0).
  {
    intros. 
    destruct H with b; rewrite H2 in H3;
    inversion H3;
    eauto.
  }
  constructor; intros.
  - constructor; intros;
    try (exploit F_EQ; eauto; intros EQ; destruct EQ; try subst).
    + rewrite Z.add_0_r.
      assumption.
    + exists 0. omega.
    + rewrite Z.add_0_r.
      remember (ZMap.get ofs (mem_contents m) # b1) as v.
      destruct v; try constructor.
      destruct v; try constructor.
      assert (LOADBYTES: loadbytes m b1 ofs 1 =
              Some (Fragment (Vptr b i) q n :: nil)).
      { unfold loadbytes.
        destruct (range_perm_dec m b1 ofs (ofs + 1) Cur Readable).
        - simpl. rewrite Heqv. reflexivity.
        - destruct n0.
          red; intros.
          replace ofs0 with ofs by omega.
          assumption.
      }
      apply H1 in LOADBYTES; try congruence.
      destruct (H b); try congruence.
      econstructor; eauto.
      rewrite Ptrofs.add_zero.
      reflexivity.
    + apply stack_inject_flat. auto.
  - destruct (H b). assumption. 
    destruct H2. apply H0.
    congruence.
  - exploit F_EQ; eauto; intros EQ; destruct EQ; subst.
    apply H0; congruence.
  - unfold meminj_no_overlap.
    intros.
    destruct (F_EQ _ _ _ H3), (F_EQ _ _ _ H4); subst.
    left; assumption.
  - destruct (F_EQ _ _ _ H2); subst.
    split. omega.
    intros. rewrite Z.add_0_r. apply Ptrofs.unsigned_range_2.
  - left.
    destruct (F_EQ _ _ _ H2); subst.
    rewrite Z.add_0_r in H3.
    assumption.
Qed.

Theorem frame_inject_flat:
  forall thr f,
  Forall (fun bfi => Plt (fst bfi) thr) (frame_adt_blocks f) ->
  frame_inject (flat_inj thr) f f.
Proof.
  red; intros thr f PLT.
  eapply Forall_impl. 2: eauto. simpl; intros a IN PLTa b2 delta FI.
  unfold flat_inj in FI. destr_in FI. inv FI.
  eexists; split; eauto.
  rewrite <- surjective_pairing. auto.
Qed.

(** ** Properties of [weak_inject]. *)

(*X* SACC:*)
Theorem empty_weak_inject: forall f m, 
  stack m = nil ->
  (forall b b' delta, f b = Some(b', delta) -> delta >= 0) ->
  (forall b b' delta, f b = Some(b', delta) -> valid_block m b') ->
  weak_inject f nil empty m.
Proof.
  intros f m STK DELTA MAPPED. constructor. constructor.
  - (* perm *)
    intros b1 b2 delta ofs k p F PERM.
    exploit perm_empty; eauto. contradiction.
  - (* align *)
    intros b1 b2 delta chunk ofs p F RNGP.
    red in RNGP. specialize (RNGP ofs).
    exploit RNGP. generalize (size_chunk_pos chunk). omega.
    intros. exploit perm_empty; eauto. contradiction.
  - (* memval *)
    intros b1 ofs b2 delta F PERM.
    exploit perm_empty; eauto. contradiction.
  - (* stack inject *)
    simpl. rewrite STK. constructor.
  - (* mapped *)
    auto.
  - (* no overlap *)
    red. intros.
    exploit perm_empty; eauto. 
  - (* representable *)
    intros b b' delta F. split.
    eapply DELTA; eauto.
    intros ofs [PERM | PERM]; exploit perm_empty; eauto; contradiction. 
  - (* inv *)
    intros b1 ofs b2 delta k p F PERM.
    right. unfold not. intros.
    exploit perm_empty; eauto; contradiction. 
Qed.

Theorem weak_inject_to_inject: forall f g m1 m2,
  weak_inject f g m1 m2 -> 
  (forall b p, f b = Some p -> valid_block m1 b) ->
  inject f g m1 m2.
Proof.
  intros f g m1 m2 WINJ VB.
  inv WINJ. constructor; auto.
  intros. destruct (f b) eqn:EQ; auto.
  exploit VB; eauto. congruence.
Qed.

Theorem store_mapped_weak_inject:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  weak_inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ weak_inject f g n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. exploit mwi_representable; try eassumption.
  intros [A B]; split; eauto. intros ofs0 P. eapply B.
  destruct P; eauto with mem.
(* perm inv *)
  intros. exploit mwi_perm_inv0; eauto using perm_store_2. 
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem alloc_left_mapped_weak_inject:
  forall f g m1 m2 lo hi m1' b1 b2 delta,
  f b1 = Some(b2, delta) ->
  weak_inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  weak_inject f g m1' m2.
Proof.
  intros f g m1 m2 lo hi m1' b1 b2 delta BINJ INJ ALLOC VB RNG PERMREPR PERMPRES IOA NOOV.
  inversion INJ.
  - constructor.
    + (* inj *)
      eapply alloc_left_mapped_inj; eauto.
    + (* mappedblocks *)
      intros. destruct (eq_block b b1). congruence. eauto.
    + (* overlap *)
      red. intros b0 b1' delta1 b3 b2' delta2 ofs1 ofs2 DIFF FB1 FB2 PE1 PE2.
      exploit perm_alloc_inv. eauto. eexact PE1. intros P1.
      exploit perm_alloc_inv. eauto. eexact PE2. intros P2.
      destruct (eq_block b0 b1); destruct (eq_block b3 b1).
      congruence.
      subst. rewrite BINJ in FB1.
      inversion FB1; subst.
      destruct (eq_block b1' b2'); auto. subst b2'. right; red; intros.
      eapply NOOV; eauto. omega.
      subst. rewrite BINJ in FB2.
      inversion FB2; subst.
      destruct (eq_block b1' b2'); auto. subst b1'. right; red; intros.
      eapply NOOV; eauto. omega.
      eauto.
    + (* representable *)
      {
        intros b b' delta0 FB.
        destruct (eq_block b b1).
        - subst. rewrite BINJ in FB. injection FB; intros; subst b' delta0.
          split. omega.
          intros.
          destruct H.
          exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
          exploit PERMREPR. apply PERMPRES with (k := Max) (p := Nonempty); eauto.
          generalize (Ptrofs.unsigned_range_2 ofs). omega.
          exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
          exploit PERMREPR. apply PERMPRES with (k := Max) (p := Nonempty); eauto.
          generalize (Ptrofs.unsigned_range_2 ofs). omega.
        - exploit mwi_representable0; try eassumption.
          intros [A B]; split; auto.
          intros; eapply B; eauto.
          destruct H; eauto using perm_alloc_4.
      }
    + (* perm inv *)
      intros b0 ofs b3 delta0 k p FB PERM.
      intros. destruct (eq_block b0 b1). subst.
      rewrite BINJ in FB. inversion FB; clear FB; subst.
      assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by omega.
      destruct EITHER.
      left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
      right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
      exploit mwi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4.
Qed.

Theorem alloc_left_unmapped_weak_inject:
  forall f g m1 m2 lo hi m1' b1,
  f b1 = None ->
  weak_inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  weak_inject f g m1' m2.
Proof.
  intros. inversion H0.
  - constructor.
    + (* inj *)
      eapply alloc_left_unmapped_inj; eauto. 
    + (* mappedblocks *)
      intros. destruct (eq_block b b1). congruence. eauto.
    + (* no overlap *)
      red; intros.
      destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
      eapply mwi_no_overlap0. eexact H2. eauto. eauto.
      exploit perm_alloc_inv. eauto. eexact H5. rewrite dec_eq_false; auto.
      exploit perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
    + (* representable *)
      intros.
      destruct (eq_block b b1). subst. rewrite H in H2. congruence.
      exploit mwi_representable0; try eassumption.
      intros [A B]; split; auto.
      intros; eapply B; eauto.
      destruct H3; eauto using perm_alloc_4.
    + (* perm inv *)
      intros. destruct (eq_block b0 b1). subst. rewrite H in H2. congruence.
      exploit mwi_perm_inv0; eauto. 
      intuition eauto using perm_alloc_1, perm_alloc_4.
Qed.

Theorem drop_parallel_weak_inject:
  forall f g m1 m2 b1 b2 delta lo hi p m1',
  weak_inject f g m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ weak_inject f g m1' m2'.
Proof.
  intros. inversion H. 
  exploit drop_mapped_inj; eauto.
  intros (m2' & DPERM & MEMINJ).
  exists m2'. split. auto. constructor.
(* inj *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. exploit mwi_representable; try eassumption.
  intros [A B]; split; eauto. intros ofs0 P. eapply B.
  destruct P; eauto with mem.
(* perm inv *)
  intros. exploit mwi_perm_inv0; eauto using perm_drop_4. 
  intuition eauto using perm_drop_4.
  destruct (eq_block b0 b1). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi). 
  rewrite H1 in H2. inv H2.
  assert (perm_order p p0). eapply perm_drop_2; eauto. omega.
  assert (perm m1' b1 ofs k p). eapply perm_drop_1; eauto.
  left. eauto with mem.
  left. eapply perm_drop_3; eauto. right. right. omega.
  left. eapply perm_drop_3; eauto. right. left. omega.
  left. eapply perm_drop_3; eauto. 
Qed.

Theorem drop_extended_parallel_weak_inject:
  forall f g m1 m2 b1 b2 delta lo1 hi1 lo2 hi2 p m1',
  weak_inject f g m1 m2 ->
  drop_perm m1 b1 lo1 hi1 p = Some m1' ->
  f b1 = Some(b2, delta) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  range_perm m2 b2 (lo2 + delta) (hi2 + delta) Cur Freeable ->
  (* no source memory location with non-empty permision 
     injects into the following region in b2 in the target memory: 
     [lo2, lo1)
     and
     [hi1, hi2)
  *)
  (forall b' delta' ofs' k p,
    f b' = Some(b2, delta') ->
    perm m1 b' ofs' k p ->
    ((lo2 + delta <= ofs' + delta' < lo1 + delta )
     \/ (hi1 + delta <= ofs' + delta' < hi2 + delta)) -> False) ->
  exists m2',
      drop_perm m2 b2 (lo2 + delta) (hi2 + delta) p = Some m2'
   /\ weak_inject f g m1' m2'.
Proof.
  intros. inversion H. 
  exploit drop_partial_mapped_inj; eauto.
  intros (m2' & DPERM & MEMINJ).
  exists m2'. split. auto. constructor.
(* inj *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. exploit mwi_representable; try eassumption.
  intros [A B]; split; eauto. intros ofs0 P. eapply B.
  destruct P; eauto with mem.
(* perm inv *)
  intros. exploit mwi_perm_inv0; eauto using perm_drop_4. 
  intuition eauto using perm_drop_4.
  destruct (eq_block b0 b1). subst b0.
  destruct (zle lo1 ofs). destruct (zlt ofs hi1). 
  rewrite H1 in H6. inv H6.
  assert (perm_order p p0). eapply perm_drop_2; eauto. omega.
  assert (perm m1' b1 ofs k p). eapply perm_drop_1; eauto.
  left. eauto with mem.
  left. eapply perm_drop_3; eauto. right. right. omega.
  left. eapply perm_drop_3; eauto. right. left. omega.
  left. eapply perm_drop_3; eauto.
Qed.

(** Invariance properties between two memory states *)

(** ** Properties of [unchanged_on] and [strong_unchanged_on] *)

(** The following property is needed by Separation, to prove
minjection. HINT: it can be used only for [strong_unchanged_on], not
for [unchanged_on]. *)

Theorem inject_unchanged_on:
   forall j g m0 m m',
   inject j g m0 m ->
   unchanged_on
     (fun (b : block) (ofs : Z) =>
        exists (b0 : block) (delta : Z),
          j b0 = Some (b, delta) /\
          perm m0 b0 (ofs - delta) Max Nonempty) m m' ->
   stack m' = stack m ->
   inject j g m0 m'.
Proof.
  intros j g m0 m m' INJ.
  set (img := fun b' ofs => exists b delta, j b = Some(b', delta) /\ perm m0 b (ofs - delta) Max Nonempty) in *.
  assert (IMG: forall b1 b2 delta ofs k p,
           j b1 = Some (b2, delta) -> perm m0 b1 ofs k p -> img b2 (ofs + delta)).
  { intros. red. exists b1, delta; split; auto. 
    replace (ofs + delta - delta) with ofs by omega.
    eauto with mem. }
  inversion INJ; constructor.
- destruct mi_inj0. constructor; intros.
+ eapply perm_unchanged_on; eauto.
+ eauto.
+ rewrite (unchanged_on_contents _ _ _ H); eauto.
+ rewrite H0; auto.
- assumption.
- intros. eapply valid_block_unchanged_on; eauto.
- assumption.
- assumption.
- intros. destruct (perm_dec m0 b1 ofs Max Nonempty); auto.
  eapply mi_perm_inv; eauto. 
  eapply perm_unchanged_on_2; eauto.
Qed.

(* Properties of [push_new_stage] *)


Theorem push_new_stage_nextblock: 
  forall m, 
  nextblock (push_new_stage m) = nextblock m.
Proof.
  reflexivity.
Qed.

Theorem push_new_stage_length_stack:
  forall m,
  length (stack (push_new_stage m)) = S (length (stack m)).
Proof.
  reflexivity.
Qed.

Theorem push_new_stage_load: 
  forall chunk m b o,
  load chunk (push_new_stage m) b o = load chunk m b o.
Proof.
  reflexivity.
Qed.

Theorem loadbytes_push:
  forall m b o n,
  loadbytes (push_new_stage m) b o n = loadbytes m b o n.
Proof.
  unfold loadbytes.
  intros.
  repeat destr.
  exfalso; apply n0.
  red; intros.
  eapply r in H. auto.
Qed.

Lemma stack_inject_push_new_stage:
  forall j g P s1 s2,
    stack_inject j P g s1 s2 ->
    stack_inject j P (1%nat :: g) ((None,nil)::s1) ((None,nil)::s2).
Proof.
  intros j g P s1 s2 SI.
  - econstructor. reflexivity. all: eauto. repeat constructor.
    easy.
Qed.

Lemma mem_inj_push_new_stage:
  forall j g m1 m2,
    mem_inj j g m1 m2 ->
    mem_inj j (1%nat :: g) (push_new_stage m1) (push_new_stage m2).
Proof.
  intros j g m1 m2 MI; inv MI; constructor; eauto.
  eapply stack_inject_push_new_stage; eauto.
Qed.

Theorem push_new_stage_inject:
  forall j g m1 m2,
  inject j g m1 m2 ->
  inject j (1%nat :: g) (push_new_stage m1) (push_new_stage m2).
Proof.
  intros j g m1 m2 MI; inv MI; constructor; eauto.
  eapply mem_inj_push_new_stage; eauto.
Qed.

Lemma stack_inject_push_new_stage_left:
  forall j n g P s1 s2,
    stack_inject j P (n::g) s1 s2 ->
    stack_inject j P (S n::g) ((None,nil)::s1) s2.
Proof.
  intros j n g P s1 s2 SI.
  inv SI. simpl in *; repeat destr_in TAKE.
  econstructor; simpl; try reflexivity. rewrite Heqo. eauto. auto.
  constructor; auto. red; easy.
Qed.

Lemma mem_inj_push_new_stage_left:
  forall j n g m1 m2,
    mem_inj j (n :: g) m1 m2 ->
    mem_inj j (S n :: g) (push_new_stage m1) m2.
Proof.
  intros j n g m1 m2 MI; inv MI; constructor; eauto.
  eapply stack_inject_push_new_stage_left; eauto.
Qed.

Theorem inject_push_new_stage_left:
  forall j n g m1 m2,
  inject j (n::g) m1 m2 ->
  inject j (S n :: g) (push_new_stage m1) m2.
Proof.
  intros j n g m1 m2 MI; inv MI; constructor; eauto.
  eapply mem_inj_push_new_stage_left; eauto.
Qed.

Lemma mem_inj_push_new_stage_right:
  forall j n g m1 m2,
    mem_inj j (S n :: g) m1 m2 ->
    top_tframe_tc (stack m1) ->
    (1 <= n)%nat ->
    mem_inj j (1%nat :: n :: g) m1 (push_new_stage m2).
Proof.
  intros j g n m1 m2 MI; inv MI; constructor; eauto.
  simpl.
  eapply stack_inject_push_new_stage_right in mi_stack_blocks0; eauto. omega.
Qed.

Theorem inject_push_new_stage_right:
  forall j n g m1 m2,
  inject j (S n :: g) m1 m2 ->
  top_tframe_tc (stack m1) ->
  (O < n)%nat ->
  inject j (1%nat :: n :: g) m1 (push_new_stage m2).
Proof.
  destruct 1; intros TTNP G1.
  constructor; simpl; intros; eauto.
  eapply mem_inj_push_new_stage_right; eauto.
  red; simpl. eapply mi_mappedblocks0; eauto.
Qed.

Theorem push_new_stage_stack:
  forall m,
  stack (push_new_stage m) = (None, nil) :: stack m.
Proof.
  reflexivity.
Qed.

Theorem push_new_stage_perm:
  forall m b o k p,
  perm (push_new_stage m) b o k p <-> perm m b o k p.
Proof.
  reflexivity.
Qed.

Theorem extends_push:
  forall m1 m2,
  extends m1 m2 ->
  extends (push_new_stage m1) (push_new_stage m2).
Proof.
  intros m1 m2 MI; inv MI; constructor; eauto.
  eapply mem_inj_push_new_stage in mext_inj0; eauto.
  simpl. omega.
Qed.

Theorem push_new_stage_unchanged_on:
  forall P m,
  unchanged_on P m (push_new_stage m).
Proof.
  red; intros. 
  repeat split; simpl; auto. xomega.
Qed.

Theorem push_new_stage_loadv:
  forall chunk m v,
  loadv chunk (push_new_stage m) v = loadv chunk m v.
Proof.
  intros; simpl; auto.
Qed.

Theorem storebytes_push:
  forall m b o bytes m',
  storebytes (push_new_stage m) b o bytes = Some m' ->
  exists m2,
    storebytes m b o bytes = Some m2.
Proof.
  intros.
  eapply range_perm_storebytes.
  eapply storebytes_range_perm in H.
  red; intros; rewrite <- push_new_stage_perm; eapply H; eauto.
Qed.

Theorem push_new_stage_inject_flat:
   forall j m1 m2,
   inject j (flat_frameinj (length (stack m1))) m1 m2 ->
   inject j (flat_frameinj (length (stack (push_new_stage m1))))
            (push_new_stage m1) (push_new_stage m2).
Proof.
  intros j m1 m2 INJ.
  apply push_new_stage_inject in INJ.
  rewrite push_new_stage_length_stack.
  unfold flat_frameinj in *. simpl in *; auto.
Qed.

(* Properties of [tailcall_stage] *)

Theorem tailcall_stage_unchanged_on:
  forall P m1 m2,
  tailcall_stage m1 = Some m2 ->
  unchanged_on P m1 m2.
Proof.
  red. intros P m1 m2 TC.
  unfold tailcall_stage in TC.
  eapply destr_dep_match. apply TC. clear TC; intros; subst. simpl.
  change (perm _) with (perm m1).
  intros; split; simpl. xomega.
  change (perm _) with (perm m1). tauto.
  reflexivity.
Qed.

Lemma constr_match:
  forall {A B: Type} (a: option A)
    x (EQ: a = Some x)
    (T: forall x (pf: Some x = a), option B)
    X
    (EQ: T _ (eq_sym EQ) = Some X),
    (match a as ano return (ano = a -> option B) with
       Some m1 =>
       fun Heq : Some m1 = a => T m1 Heq
     | None => fun _ => None
     end) eq_refl = Some X.
Proof.
  intros. subst. simpl in *.  auto. 
Qed.

Lemma stack_inject_tailcall_stage_gen:
  forall j g (m: perm_type) o1 l1 s1 o2 l2 s2 (m': perm_type),
    (forall b1 b2 delta o k p, j b1 = Some (b2, delta) -> m b1 o k p ->
                          m' b2 (o + delta)%Z k p) ->
    top_tframe_prop (fun tf => forall b, in_frames tf b -> forall o k p, ~ m' b o k p) ((o2, l2)::s2) ->
    stack_inject j m g ((o1,l1)::s1) ((o2, l2)::s2) ->
    stack_inject j m g ((None, opt_cons o1 l1)::s1) ((None, opt_cons o2 l2)::s2).
Proof.
  intros j g m o1 l1 s1 o2 l2 s2 m' PERMINJ NOPERM SI. inv SI.
  simpl in *. repeat destr_in TAKE. 
  econstructor.
  simpl; rewrite Heqo. reflexivity. simpl. reflexivity. auto.
  constructor; auto.
  - red. simpl. congruence.
  - inv FI. eapply Forall_impl. 2: apply H2. simpl; intros.
    clear H1 H2.
    red. intros f0 EQ HPF. 
    exfalso.
    specialize (H0 _ EQ HPF).
    destruct HPF as (b & o & k & p & NONE & IFR & PERM).
    destruct H0 as (f3 & EQQ & FI); inv EQQ.
    destruct (j b) eqn:JB; try congruence. destruct p0.
    eapply PERMINJ in PERM; eauto.
    inv NOPERM.
    eapply H2 in PERM; eauto. red. simpl. simpl in *; subst.
    eapply frame_inject_in_frame; eauto.
Qed.

Lemma stack_inject_tailcall_stage_gen':
  forall j g m m' ,
    (forall (b1 b2 : block) (delta o : Z) (k : perm_kind) (p : permission),
        j b1 = Some (b2, delta) -> perm m b1 o k p ->
        perm m' b2 (o + delta)%Z k p) ->
    top_frame_no_perm m' ->
    forall s1' s2',
      tailcall_stage_stack m = Some s1' ->
      tailcall_stage_stack m' = Some s2' ->
      stack_inject j (perm m) g (stack m) (stack m') ->
      stack_inject j (perm m) g s1' s2'.
Proof.
  intros j g m m' PERMINJ TTP s1' s2' TSS TSS' SI.
  unfold tailcall_stage_stack in *.
  repeat destr_in TSS. repeat destr_in TSS'. simpl in *.
  inv t. inv t0. simpl.
  red in H0, H2.
  eapply stack_inject_tailcall_stage_gen.
  apply PERMINJ.
  rewrite <- surjective_pairing. setoid_rewrite H1. auto.
  rewrite <- H1, <- H in SI.
  rewrite <- ! surjective_pairing. auto.
Qed.

Theorem tailcall_stage_tc:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  top_tframe_tc (stack m2).
Proof.
  unfold tailcall_stage; intros m1 m2 TC.
  pattern m2. eapply destr_dep_match. apply TC. clear TC; intros; subst. simpl.
  unfold tailcall_stage_stack in pf. destr_in pf. inv pf.
  constructor. reflexivity.
Qed.

Theorem tailcall_stage_perm:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  forall b o k p,
  perm m2 b o k p <-> perm m1 b o k p.
Proof.
  unfold tailcall_stage. intros m1 m2 TS.
  pattern m2. eapply destr_dep_match. apply TS. clear TS.
  simpl. intros; subst. tauto.
Qed.

Theorem tailcall_stage_tl_stack:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  tl (stack m2) = tl (stack m1).
Proof.
  unfold tailcall_stage; intros m1 m2 TC.
  pattern m2. eapply destr_dep_match. apply TC. clear TC; intros; subst. simpl.
  unfold tailcall_stage_stack in pf. destr_in pf. inv pf.
  reflexivity.
Qed.

Lemma stack_inject_mem_inj:
  forall j1 g1 m1 m2 g2 m3 m4
    (MINJ: mem_inj j1 g1 m1 m2)
    (SINJ: stack_inject j1 (perm m1) g1 (stack m1) (stack m2) ->
           stack_inject j1 (perm m3) g2 (stack m3) (stack m4))
    (PERMINJ2: forall b o k p, perm m2 b o k p -> perm m4 b o k p)
    (PERMINJ1: forall b o k p, perm m3 b o k p -> perm m1 b o k p)
    (CONTENTS1: mem_contents m1 = mem_contents m3)
    (CONTENTS2: mem_contents m2 = mem_contents m4),
    mem_inj j1 g2 m3 m4.
Proof.
  intros j1 g1 m1 m2 g2 m3 m4 MINJ SINJ PERMINJ2 PERMINJ1 CONTENTS1 CONTENTS2.
  inv MINJ.
  constructor; simpl; intros; eauto.
  - eapply mi_align0; eauto. red; intros; eapply PERMINJ1; eauto.
  - rewrite <- CONTENTS1, <- CONTENTS2. eauto.
Qed.

Theorem tailcall_stage_extends:
  forall m1 m2 m1',
  extends m1 m2 ->
  tailcall_stage m1 = Some m1' ->
  top_frame_no_perm m2 ->
  exists m2', tailcall_stage m2 = Some m2' /\ extends m1' m2'.
Proof.
  intros m1 m2 m1' INJ TC TTP.
  unfold tailcall_stage in TC.
  pattern m1'. eapply destr_dep_match. apply TC. clear TC. intros; subst.
  assert (exists m2', tailcall_stage_stack m2 = Some m2').
  {
    unfold tailcall_stage_stack in *. repeat destr_in pf.
    destr. eauto.
  }
  destruct H as (m2' & TCS).
  unfold tailcall_stage. eexists; split.
  eapply constr_match. eauto.
  Unshelve. all: eauto.
  inv INJ; constructor; simpl; intros; eauto.
  eapply stack_inject_mem_inj; eauto; try tauto.
  simpl. 
  change (perm _) with (perm m1).
  replace (length m) with (length (stack m1)).
  eapply stack_inject_tailcall_stage_gen'; eauto.
  inv mext_inj0. eauto. unfold tailcall_stage_stack in pf. repeat destr_in pf. inv t. simpl. reflexivity.
  unfold tailcall_stage_stack in *. repeat destr_in pf. repeat destr_in TCS. simpl.
  revert mext_length_stack0. inv t. inv t0.
  simpl. auto.
Qed.

Lemma stack_inject_inject:
  forall j1 g1 m1 m2 g2 m3 m4
    (MINJ: inject j1 g1 m1 m2)
    (SINJ: stack_inject j1 (perm m1) g1 (stack m1) (stack m2) ->
           stack_inject j1 (perm m3) g2 (stack m3) (stack m4))
    (PERMINJ2: forall b o k p, perm m2 b o k p <-> perm m4 b o k p)
    (PERMINJ1: forall b o k p, perm m3 b o k p <-> perm m1 b o k p)
    (CONTENTS1: mem_contents m1 = mem_contents m3)
    (CONTENTS2: mem_contents m2 = mem_contents m4)
    (NB1: nextblock m1 = nextblock m3)
    (NB2: nextblock m2 = nextblock m4),
    inject j1 g2 m3 m4.
Proof.
  intros j1 g1 m1 m2 g2 m3 m4 MINJ SINJ PERMINJ2 PERMINJ1 CONTENTS1 CONTENTS2 NB1 NB2.
  inv MINJ.
  constructor; simpl; intros; eauto.
  - eapply stack_inject_mem_inj; eauto. intros; rewrite <- PERMINJ2; eauto.
    intros; rewrite <- PERMINJ1; eauto.
  - eapply mi_freeblocks0; eauto. unfold valid_block; rewrite NB1; eauto.
  - red; rewrite <- NB2. eapply mi_mappedblocks0; eauto.
  - red; intros. eapply mi_no_overlap0; eauto.
    rewrite <- PERMINJ1; eauto.
    rewrite <- PERMINJ1; eauto.
  - edestruct mi_representable0; eauto. split; intros; eauto.
    apply H1. 
    rewrite <- ! PERMINJ1; auto.
  - rewrite ! PERMINJ1. rewrite <- PERMINJ2 in H0; eauto.
Qed.

Theorem tailcall_stage_inject:
  forall j g m1 m2 m1',
  inject j g m1 m2 ->
  tailcall_stage m1 = Some m1' ->
  top_frame_no_perm m2 ->
  exists m2', tailcall_stage m2 = Some m2' /\ inject j g m1' m2'.
Proof.
  intros j g m1 m2 m1' INJ TC TTP.
  unfold tailcall_stage in TC.
  pattern m1'. eapply destr_dep_match. apply TC. clear TC. intros; subst.
  assert (exists m2', tailcall_stage_stack m2 = Some m2').
  {
    unfold tailcall_stage_stack in *. repeat destr_in pf.
    destr. eauto.
  }
  destruct H as (m2' & TCS).
  unfold tailcall_stage. eexists; split.
  eapply constr_match. eauto.
  eapply stack_inject_inject; eauto; try tauto.
  simpl. instantiate (1 := m2').
  change (perm _) with (perm m1). eapply stack_inject_tailcall_stage_gen'; eauto.
  intros; eapply perm_inject; eauto.
  Unshelve. auto.
Qed.

Theorem tailcall_stage_stack_equiv:
  forall m1 m2 m1' m2',
  tailcall_stage m1 = Some m1' ->
  tailcall_stage m2 = Some m2' ->
  stack_equiv (stack m1)  (stack m2) ->
  stack_equiv (stack m1') (stack m2').
Proof.
  unfold tailcall_stage in *. intros.
  pattern m2'; eapply destr_dep_match. apply H0. clear H0. intros; subst.
  pattern m1'; eapply destr_dep_match. apply H. clear H. intros; subst.
  simpl.
  unfold tailcall_stage_stack in *.
  repeat destr_in pf; repeat destr_in pf0.
  revert H1.
  inv t; inv t0. intro A; inv A. simpl. constructor; auto.
  split; simpl; auto.
  destruct LF2.
  red. red in H3. red in H0, H2. repeat destr_in H3. simpl.
  constructor; auto.
Qed.

Theorem tailcall_stage_same_length_pos:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  length (stack m2) = length (stack m1) /\ lt O (length (stack m1)).
Proof.
  unfold tailcall_stage in *. intros.
  pattern m2; eapply destr_dep_match. apply H. clear H. intros; subst.
  simpl.
  unfold tailcall_stage_stack in pf; repeat destr_in pf. simpl. inv t. simpl.
  split; omega.
Qed.

Theorem tailcall_stage_nextblock:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  nextblock m2 = nextblock m1.
Proof.
  unfold tailcall_stage. intros m1 m2 TS.
  pattern m2. eapply destr_dep_match. apply TS. clear TS.
  simpl. intros; subst. tauto.
Qed.

Theorem tailcall_stage_inject_left:
  forall j n g m1 m2 m1',
  inject j (n :: g) m1 m2 ->
  tailcall_stage m1 = Some m1' ->
  inject j (n::g) m1' m2.
Proof.
  intros j n g m1 m2 m1' INJ TC.
  unfold tailcall_stage in TC.
  pattern m1'. eapply destr_dep_match. apply TC. clear TC. intros; subst.
  eapply stack_inject_inject; eauto; try tauto.
  simpl.
  change (perm _) with (perm m1).
  unfold tailcall_stage_stack in pf. repeat destr_in pf. inv t. simpl. intro SI.
  inv SI. simpl in *. repeat destr_in TAKE.
  econstructor; simpl. rewrite Heqo. eauto. all: eauto.
  constructor. red; easy. inv FI; auto.
Qed.

Theorem tailcall_stage_right_extends:
  forall m1 m2,
  extends m1 m2 ->
  top_frame_no_perm m1 ->
  top_frame_no_perm m2 ->
  exists m2', tailcall_stage m2 = Some m2' /\ extends m1 m2'.
Proof.
  intros m1 m2 EXT TFNP1 TFNP2.
  assert (exists s2, tailcall_stage_stack m2 = Some s2).
  {
    unfold tailcall_stage_stack. destr. eauto.
  }
  destruct H.
  unfold tailcall_stage.
  intros.
  eexists; split.
  eapply constr_match. eauto.
  Unshelve. 3: eauto.
  inv EXT; constructor; simpl; intros; eauto.
  inv mext_inj0; constructor; eauto.
  simpl.
  unfold tailcall_stage_stack in H. repeat destr_in H.
  simpl.
  revert mi_stack_blocks0. inv TFNP1. inv TFNP2. simpl.
  intro SI. inv SI.
  simpl in *. inv TAKE.
  econstructor; simpl; eauto.
  constructor. red. intros f1 EQ (b & o & k & p & NONE & IFR & PERM).
  eapply H0 in PERM; eauto. easy. eapply in_frame_in_frames; eauto.
  constructor.
  unfold tailcall_stage_stack in H. repeat destr_in H.
  simpl. inv t. simpl. rewrite <- H in mext_length_stack0. simpl in *; auto.
Qed.

Theorem tailcall_stage_stack_eq:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  exists f r,
  stack m1 = f :: r /\ stack m2 = (None, opt_cons (fst f) (snd f))::r.
Proof.
  unfold tailcall_stage in *. intros.
  pattern m2; eapply destr_dep_match. apply H. clear H. intros; subst.
  simpl. unfold tailcall_stage_stack in pf; repeat destr_in pf. 
  inv t. simpl. eauto.
Qed.

Theorem stack_inject_tailcall_stage:
  forall j g m f1 l1 s1 f2 l2 s2,
  stack_inject j m (1%nat::g) ((Some f1,l1)::s1) ((Some f2, l2)::s2) ->
  stack_inject j m (1%nat::g) ((None, f1::l1)::s1) ((None, f2::l2)::s2).
Proof.
  intros j g m f1 l1 s1 f2 l2 s2 SI. inv SI; econstructor.
  reflexivity. reflexivity. simpl in *; auto.
  constructor; auto.
  simpl in *. inv TAKE.
  red. simpl. congruence.
Qed.

Theorem tailcall_stage_inject_flat:
  forall j m1 m2 m1',
  inject j (flat_frameinj (length (stack m1))) m1 m2 ->
  tailcall_stage m1 = Some m1' ->
  top_frame_no_perm m2 ->
  exists m2',
    tailcall_stage m2 = Some m2' /\ inject j (flat_frameinj (length (stack m1'))) m1' m2'.
  Proof.
    intros j m1 m2 m1' INJ TS TOPNOPERM.
    destruct (tailcall_stage_same_length_pos _ _ TS) as (LENEQ & LENPOS).
    rewrite LENEQ.
    destruct (length (stack m1)); simpl in *. omega.
    rewrite frameinj_push_flat in *.
    eapply tailcall_stage_inject; eauto.
Qed.
(* Properties of [record_stack_block] *)

Theorem record_stack_blocks_original_stack:
  forall m1 f1 m2,
    record_stack_blocks m1 f1 = Some m2 ->
    exists f r,
      stack m1 = (None,f)::r.
Proof.
  unfold record_stack_blocks.
  intros m f m' RSB. repeat destr_in RSB.
  pattern m'. eapply destr_dep_match. apply H0. clear H0.
  intros; subst.
  unfold prepend_to_current_stage in pf. repeat destr_in pf.
  eauto.
Qed.

Theorem record_stack_blocks_stack:
  forall m f m' of1 s1,
    record_stack_blocks m f = Some m' ->
    stack m = of1::s1 ->
    stack m' = (Some f, snd of1)::s1.
Proof.
  unfold record_stack_blocks.
  intros m f m' of1 s1 RSB SEQ. repeat destr_in RSB.
  pattern m'. eapply destr_dep_match. apply H0. clear H0.
  intros; subst. simpl.
  unfold prepend_to_current_stage in pf. rewrite SEQ in pf. repeat destr_in pf; reflexivity.
Qed.


Theorem record_stack_blocks_stack_eq:
  forall m1 f m2,
  record_stack_blocks m1 f = Some m2 ->
  exists tf r,
    stack m1 = (None,tf)::r /\ stack m2 = (Some f,tf)::r.
Proof.
  intros.
  edestruct record_stack_blocks_original_stack as (ff & r & eq); eauto. rewrite eq.
  eapply record_stack_blocks_stack in eq; eauto.
Qed.

Theorem record_stack_blocks_length_stack:
  forall m1 f m2,
  record_stack_blocks m1 f = Some m2 ->
  length (stack m2) = length (stack m1).
Proof.
  intros.
  edestruct record_stack_blocks_original_stack as (ff & r & eq); eauto. rewrite eq.
  eapply record_stack_blocks_stack in eq; eauto. rewrite eq. reflexivity.
Qed.

Lemma record_stack_inject_left:
  forall j g m1 s1 s2
    (SI : stack_inject j m1 g s1 s2)
    f1 f2
    (FAP: frame_at_pos s2 O f2)
    (FI : tframe_inject j m1 (Some f1,nil) f2)
    s1' 
    (PREP: prepend_to_current_stage f1 s1 = Some s1'),
    stack_inject j m1 g s1' s2.
Proof.
  intros j g m1 s1 s2 SI f1 f2 FAP FI s1' PREP.
  unfold prepend_to_current_stage in PREP. destr_in PREP. inv PREP.
  inv SI. simpl in *. repeat destr_in TAKE.
  specialize (FI _ (eq_refl)).
  apply frame_at_pos_last in FAP. subst.
  repeat destr_in H0.
  econstructor. simpl. rewrite Heqo. eauto. simpl. eauto. eauto.
  inv FI0; constructor; auto.
  intros ff EQ. inv EQ.
  auto.
Qed.

Lemma record_stack_blocks_mem_inj_left:
    forall j g m1 m2 f1 f2 m1',
      mem_inj j g m1 m2 ->
      record_stack_blocks m1 f1 = Some m1' ->
      frame_at_pos (stack m2) O f2 ->
      tframe_inject j (perm m1) (Some f1,nil) f2 ->
      mem_inj j g m1' m2.
Proof.
  intros j g m1 m2 f1 f2 m1' INJ ADT FAP FI.
  unfold record_stack_blocks in ADT.
  repeat destr_in ADT.
  pattern m1'. eapply destr_dep_match. apply H0. clear H0. intros; subst.
  inversion INJ; subst; constructor; simpl; intros; eauto.
  eapply stack_inject_invariant_strong.
  intros. change (perm m1 b ofs k p) in H0. apply H0.
  eapply record_stack_inject_left; eauto.
Qed.

Theorem record_stack_blocks_inject_left:
  forall m1 m1' m2 j g f1 f2,
  inject j g m1 m2 ->
  frame_at_pos (stack m2) 0 f2 ->
  tframe_inject j (perm m1) (Some f1, nil) f2 ->
  record_stack_blocks m1 f1 = Some m1' ->
  inject j g m1' m2.
Proof.
  intros m1 m1' m2 j g f1 f2 INJ FAP FI RSB.
  inversion INJ; eauto.
  exploit record_stack_blocks_mem_inj_left; eauto.
  intro MINJ.
  edestruct (record_stack_blocks_mem_unchanged _ _ _ RSB) as (NB1 & PERM1 & U1 & C1) ; simpl in *.
  inversion INJ; econstructor; simpl; intros; eauto.
  + eapply mi_freeblocks0; eauto.
    unfold valid_block in H; rewrite NB1 in H; eauto.
  + red; intros.
    rewrite PERM1 in H3, H2.
    eapply mi_no_overlap0; eauto.
  + exploit mi_representable0; eauto.
    intros (A & B); split; auto. intro ofs; rewrite ! PERM1. eauto.
  + rewrite ! PERM1. eapply mi_perm_inv0 in H0; eauto.
Qed.

Lemma record_stack_inject:
  forall j g m1 s1 s2
    (SI : stack_inject j g m1 s1 s2)
    f1 f2
    (FI : frame_inject j f1 f2)
    (INF : forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame f1 b1 <-> in_frame f2 b2)
    (EQsz : frame_adt_size f1 = frame_adt_size f2)
    s1' s2'
    (PREP1: prepend_to_current_stage f1 s1 = Some s1')
    (PREP2: prepend_to_current_stage f2 s2 = Some s2'),
    stack_inject j
                 g
                 m1
                 s1' s2'.
Proof.
  intros j g m1 s1 s2 SI f1 f2 FI INF EQsz s1' s2' PREP1 PREP2.
  unfold prepend_to_current_stage in PREP1, PREP2; repeat destr_in PREP1; repeat destr_in PREP2.
  inv SI.
  simpl in TAKE. repeat destr_in TAKE.
  econstructor. simpl. rewrite Heqo. eauto. reflexivity. simpl. simpl in *. auto.
  inv FI0; constructor; auto.
  - intros ff EQ. simpl in EQ. inv EQ.
    intro; exists f2; split; eauto.
  - eapply Forall_impl. 2: apply H2. simpl.
    intros a INA TFI ff INAFF HPF. simpl.
    destruct (TFI _ INAFF) as (ff2 & INt0 & FI2); eauto. simpl in INt0. congruence.
Qed.

Lemma record_stack_blocks_mem_inj:
    forall j g m1 m2 f1 f2 m1',
      mem_inj j g m1 m2 ->
      record_stack_blocks m1 f1 = Some m1' ->
      frame_inject j f1 f2 ->
      valid_frame f2 m2 ->
      (forall b, in_stack (stack m2) b -> ~ in_frame f2 b) ->
      frame_agree_perms (perm m2) f2 ->
      top_tframe_tc (stack m2) ->
      (forall b1 b2 delta, j b1 = Some (b2, delta) -> in_frame f1 b1 <-> in_frame f2 b2) ->
      frame_adt_size f1 = frame_adt_size f2 ->
      (size_stack (tl (stack m2)) <= size_stack (tl (stack m1)))%Z ->
      exists m2',
        record_stack_blocks m2 f2 = Some m2'
        /\ mem_inj j g m1' m2'.
Proof.
  intros j g m1 m2 f1 f2 m1' INJ ADT FI VB NIN2 BNDS2 TTNP INF EQsz SZ; autospe.
  unfold record_stack_blocks in ADT.
  repeat destr_in ADT.
  pattern m1'.
  eapply destr_dep_match. apply H0. clear H0. simpl; intros. subst.
  unfold record_stack_blocks.
  repeat destr.
  inv TTNP.
  eexists; split.
  eapply constr_match. eauto.
  - inversion INJ; subst; constructor; simpl; intros; eauto.
    + eapply mi_perm0; eauto.
    + eapply stack_inject_invariant_strong.
      intros. change (perm m1 b ofs k p) in H2. apply H2.
      eapply record_stack_inject. all:eauto.
      unfold prepend_to_current_stage. rewrite <- H.
      instantiate (1 := (Some f2, snd tf)::r).
      repeat destr. inv H0.
  - exfalso; apply n;  auto. apply frame_agree_perms_rew; eauto.
  - exfalso. rewrite <- EQsz in g0. omega.
  - exfalso; apply n;  auto.
    rewrite Forall_forall. intros.
    intro INS; apply NIN2 in INS.
    destruct x.
    apply INS. eapply in_frame_blocks_in_frame; eauto.
    Unshelve. rewrite <- H. simpl. destruct tf; simpl in *; subst. reflexivity.
Qed.


Theorem record_stack_blocks_inject_parallel:
  forall m1 m1' m2 j g fi1 fi2,
  inject j g m1 m2 ->
  frame_inject j fi1 fi2 ->
  (forall b : block, in_stack (stack m2) b -> ~ in_frame fi2 b) ->
  (valid_frame fi2 m2) ->
  frame_agree_perms (perm m2) fi2 ->
  (forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame fi1 b1 <-> in_frame fi2 b2) ->
  frame_adt_size fi1 = frame_adt_size fi2 ->
  record_stack_blocks m1 fi1 = Some m1' ->
  top_tframe_tc (stack m2) ->
  size_stack (tl (stack m2)) <= size_stack (tl (stack m1)) ->
  exists m2',
    record_stack_blocks m2 fi2 = Some m2' /\
    inject j g m1' m2'.
Proof.
  intros m1 m1' m2 j g fi1 fi2 INJ FI NOIN VF BOUNDS EQING EQsz RSB TTNP SZ.
  exploit record_stack_blocks_mem_inj.
  inversion INJ; eauto.
  all: eauto.
  intros (m2' & ADT & INJ').
  eexists; split; eauto.
  edestruct (record_stack_blocks_mem_unchanged _ _ _ RSB) as (NB1 & PERM1 & U1 & C1) ;
    edestruct (record_stack_blocks_mem_unchanged _ _ _ ADT) as (NB & PERM & U & C); simpl in *.
  inversion INJ; econstructor; simpl; intros; eauto.
  + eapply mi_freeblocks0; eauto.
    unfold valid_block in H; rewrite NB1 in H; eauto.
  + unfold valid_block; rewrite NB; eauto.
    eapply mi_mappedblocks0; eauto.
  + red; intros.
    rewrite PERM1 in H3, H2.
    eapply mi_no_overlap0; eauto.
  + exploit mi_representable0; eauto.
    intros (A & B); split; auto. intro ofs; rewrite ! PERM1. eauto.
  + rewrite ! PERM1. rewrite PERM in H0. eapply mi_perm_inv0 in H0; eauto.
Qed.

Lemma record_stack_blocks_valid:
  forall m1 fi m2,
    record_stack_blocks m1 fi = Some m2 ->
    valid_frame fi m1.
Proof.
  unfold record_stack_blocks; intros m1 fi m2 RSB; repeat destr_in RSB.
Qed.

Theorem record_stack_blocks_extends:
  forall m1 m2 m1' fi,
  extends m1 m2 ->
  record_stack_blocks m1 fi = Some m1' ->
  (forall b, in_frame fi b -> ~ in_stack ( (stack m2)) b ) ->
  frame_agree_perms (perm m2) fi ->
  top_tframe_tc (stack m2) ->
  size_stack (tl (stack m2)) <= size_stack (tl (stack m1)) ->
  exists m2',
    record_stack_blocks m2 fi = Some m2' /\
    extends m1' m2'.
Proof.
  intros m1 m2 fi m1' EXT ADT NIN BNDS TTNP SZ; autospe.
  inversion EXT.
  exploit record_stack_blocks_mem_inj; eauto.
  - eapply frame_inject_id.
  - red. red. rewrite <- mext_next0.
    eapply record_stack_blocks_valid; eauto.
  - intros b INS INF. eapply NIN; eauto.
  - inversion 1. subst. tauto.
  - intros (m2' & ADT' & INJ). 
    edestruct (record_stack_blocks_stack_eq _ _ _ ADT) as (f1 & r & EQ1 & EQ2).
    edestruct (record_stack_blocks_stack_eq _ _ _ ADT') as (f2 & r2 & EQ3 & EQ4). 
    eexists; split; eauto.
    edestruct (record_stack_blocks_mem_unchanged _ _ _ ADT) as (NB1 & PERM1 & _) ;
    edestruct (record_stack_blocks_mem_unchanged _ _ _ ADT') as (NB & PERM & _); simpl in *.
    constructor; simpl; intros; eauto.
    congruence.
    revert INJ.
    rewrite EQ1, EQ2. simpl.  auto.
    rewrite ! PERM1, PERM in *. eauto.
    revert mext_length_stack0.
    rewrite EQ1, EQ2, EQ3, EQ4; simpl. intros; omega.
Qed.

Lemma inject_frame_flat a thr:
  frame_inject (flat_inj thr) a a.
Proof.
  destruct a; try (econstructor; inversion 1; tauto).
  apply Forall_forall. unfold flat_inj; intros. destr_in H0. 
  simpl in *. inv H0. destruct x. simpl in *. eauto.
Qed.

Lemma record_stack_blocks_sep:
  forall m1 fi m2 ,
    record_stack_blocks m1 fi = Some m2 ->
    forall b : block, in_stack (stack m1) b -> ~ in_frame fi b.
Proof.
  unfold record_stack_blocks.
  intros m f m' RSB. repeat destr_in RSB.
  intros b INS INF.
  clear H0. rewrite Forall_forall in f0.
  edestruct in_frame_info; eauto.
  apply f0 in H. simpl in H. eauto.
Qed.

Lemma record_stack_blocks_bounds:
  forall m1 fi m2,
    record_stack_blocks m1 fi = Some m2 ->
    frame_agree_perms (perm m1) fi.
Proof.
  unfold record_stack_blocks; intros m1 fi m2 RSB; repeat destr_in RSB.
  apply frame_agree_perms_rew; eauto.
Qed.

Lemma record_stack_blocks_top_noperm:
  forall m1 f m1',
    record_stack_blocks m1 f = Some m1' ->
    top_tframe_tc (stack m1).
Proof.
  unfold record_stack_blocks. intros m1 f m1' RSB; repeat destr_in RSB.
  pattern m1'. eapply destr_dep_match. apply H0. clear H0. intros; subst.
  unfold prepend_to_current_stage in pf. repeat destr_in pf.
  constructor. reflexivity.
Qed.

Theorem record_stack_blocks_inject_neutral:
  forall thr m fi m',
  inject_neutral thr m ->
  record_stack_blocks m fi = Some m' ->
  Forall (fun b => Plt b thr) (map fst (frame_adt_blocks fi)) ->
  inject_neutral thr m'.
Proof.
  unfold inject_neutral; intros.
  exploit record_stack_blocks_mem_inj.
  - eauto.
  - eauto.
  - apply inject_frame_flat.
  - eapply record_stack_blocks_valid; eauto. 
  - eapply record_stack_blocks_sep; eauto.
  - generalize (record_stack_blocks_bounds _ _ _ H0). auto.
  - eapply record_stack_blocks_top_noperm; eauto.
  - unfold flat_inj. intros. destr_in H2.
  - auto.
  - destruct (record_stack_blocks_original_stack _ _ _ H0) as ( f & r & EQ ).
    rewrite EQ. reflexivity.
  - intros (m2' & RSB & MI).
    assert (m' = m2') by congruence. subst.
    destruct (record_stack_blocks_stack_eq _ _ _ H0) as ( f & r & EQ1 & EQ2 ).
    revert MI. rewrite EQ1, EQ2. simpl. auto.
Qed.

Theorem record_stack_block_inject_flat:
 forall m1 m1' m2 j  f1 f2,
 inject j (flat_frameinj (length (stack m1))) m1 m2 ->
 frame_inject j f1 f2 ->
 (forall b, in_stack (stack m2) b -> ~ in_frame f2 b) ->
 valid_frame f2 m2 ->
 frame_agree_perms (perm m2) f2 ->
 (forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame f1 b1 <-> in_frame f2 b2) ->
 frame_adt_size f1 = frame_adt_size f2 ->
 record_stack_blocks m1 f1 = Some m1' ->
 top_tframe_tc (stack m2) ->
 size_stack (tl (stack m2)) <= size_stack (tl (stack m1)) ->
 exists m2',
   record_stack_blocks m2 f2 = Some m2' /\
   inject j (flat_frameinj (length (stack m1'))) m1' m2'.
Proof.
 intros m1 m1' m2 j f1 f2 INJ FI NOIN VF BOUNDS EQINF EQsz RSB TTNB SZ.
 edestruct record_stack_blocks_stack_eq as (ff1 & r1 & EQ1 & EQ2); eauto.  
 destruct (record_stack_blocks_inject_parallel _ m1' _ _ _ _ _ INJ FI NOIN VF)
   as (m2' & RSB' & INJ'); eauto.
 eexists; split; eauto.
 revert INJ'.
 rewrite EQ1, EQ2. auto.
Qed.

Theorem record_stack_blocks_top_tframe_no_perm:
  forall m1 f m2,
  record_stack_blocks m1 f = Some m2 ->
  top_tframe_tc (stack m1).
Proof.
  unfold record_stack_blocks. intros m1 f m1' RSB; repeat destr_in RSB.
  pattern m1'. eapply destr_dep_match. apply H0. clear H0. intros; subst.
  unfold prepend_to_current_stage in pf. repeat destr_in pf.
  constructor. reflexivity.
Qed.

Theorem record_stack_block_unchanged_on:
  forall m bfi m' (P: block -> Z -> Prop),
  record_stack_blocks m bfi = Some m' ->
  unchanged_on P m m'.
Proof.
  intros; eapply record_stack_blocks_mem_unchanged; eauto.
Qed.

Theorem record_stack_block_perm:
  forall m bfi m',
  record_stack_blocks m bfi = Some m' ->
  forall b' o k p,
    perm m' b' o k p ->
    perm m b' o k p.
Proof.
  intros. eapply record_stack_blocks_mem_unchanged in H; eauto.
  apply H; eauto.
Qed.

Theorem record_stack_block_perm': 
  forall m m' bofi,
  record_stack_blocks m bofi = Some m' ->
  forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
  perm m b' o k p -> perm m' b' o k p.
Proof.
  intros. eapply record_stack_blocks_mem_unchanged in H; eauto.
  apply H; eauto.
Qed.

Theorem record_stack_block_valid:
  forall m bf m',
  record_stack_blocks m bf = Some m' ->
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; intros.
  eapply record_stack_blocks_mem_unchanged in H; eauto.
  destruct H. rewrite H. auto.
Qed.

Theorem record_stack_block_nextblock:
  forall m bf m',
  record_stack_blocks m bf = Some m' ->
  nextblock m' = nextblock m.
Proof.
  intros.
  eapply record_stack_blocks_mem_unchanged in H; eauto.
  intuition.
Qed.

Theorem record_stack_block_is_stack_top:
  forall m b fi m',
  record_stack_blocks m fi = Some m' ->
  in_frame fi b ->
  is_stack_top (stack m') b.
Proof.
  unfold is_stack_top, get_stack_top_blocks.
  intros.
  edestruct (record_stack_blocks_original_stack _ _ _ H) as (f & r & EQ).
  erewrite record_stack_blocks_stack; eauto.
  unfold get_frames_blocks. simpl. auto.
Qed.


Theorem record_push_inject:
  forall j n g m1 m2 fi1 fi2 m1',
  inject j (n :: g) m1 m2 ->
  frame_inject j fi1 fi2 ->
  (forall b, 
    in_stack (stack m2) b -> 
    in_frame fi2 b -> 
    False) ->
  valid_frame fi2 m2 ->
  frame_agree_perms (perm m2) fi2 ->
  (forall b1 b2 delta, 
    j b1 = Some (b2, delta) -> 
    in_frame fi1 b1 <-> in_frame fi2 b2) ->
  frame_adt_size fi1 = frame_adt_size fi2 ->
  record_stack_blocks m1 fi1 = Some m1' ->
  top_tframe_tc (stack m2) ->
  size_stack (tl (stack m2)) <= size_stack (tl (stack m1)) ->
  exists m2', 
       record_stack_blocks m2 fi2 = Some m2'
    /\ inject j (n::g) m1' m2'.
Proof.
  intros.
  eapply record_stack_blocks_inject_parallel; eauto.
Qed.

Theorem record_push_inject_flat:
  forall j m1 m2 fi1 fi2 m1', 
  inject j (flat_frameinj (length (stack m1))) m1 m2 ->
  frame_inject j fi1 fi2 ->
  (forall b, 
    in_stack (stack m2) b -> 
    in_frame fi2 b -> 
    False) ->
  valid_frame fi2 m2 ->
  frame_agree_perms (perm m2) fi2 ->
  (forall b1 b2 delta, 
    j b1 = Some (b2, delta) -> 
    in_frame fi1 b1 <-> in_frame fi2 b2) ->
  (frame_adt_size fi1 = frame_adt_size fi2) ->
  record_stack_blocks m1 fi1 = Some m1' ->
  top_tframe_tc (stack m2) ->
  size_stack (tl (stack m2)) <= size_stack (tl (stack m1)) ->
  exists m2', 
       record_stack_blocks m2 fi2 = Some m2' 
    /\ inject j (flat_frameinj (length (stack m1'))) m1' m2'.
Proof.
  intros j m1 m2 fi1 fi2 m1' MINJ FI NINSTACK VALID FAP2 INF SZ RSB TTNP SZ0.
  destruct (record_stack_blocks_original_stack _ _ _ RSB) as (f & r & EQ).
  rewrite (record_stack_blocks_length_stack _ _ _ RSB).
  rewrite EQ in MINJ |- *.
  eapply record_push_inject; eauto.
Qed.

Theorem record_stack_blocks_inject_parallel_flat:
   forall m1 m1' m2 j fi1 fi2,
   inject j (flat_frameinj (length (stack m1))) m1 m2 ->
   frame_inject j fi1 fi2 ->
   (forall b : block, in_stack (stack m2) b -> ~ in_frame fi2 b) ->
   (valid_frame fi2 m2) ->
   frame_agree_perms (perm m2) fi2 ->
   (forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame fi1 b1 <-> in_frame fi2 b2) ->
   frame_adt_size fi1 = frame_adt_size fi2 ->
   record_stack_blocks m1 fi1 = Some m1' ->
   top_tframe_tc (stack m2) ->
   size_stack (tl (stack m2)) <= size_stack (tl (stack m1)) ->
   exists m2',
     record_stack_blocks m2 fi2 = Some m2' /\
     inject j (flat_frameinj (length (stack m1'))) m1' m2'.
Proof.
  intros.
  edestruct record_stack_blocks_inject_parallel as (m2' & RSB & INJ'); eauto.
  eexists; split; eauto.
  erewrite record_stack_blocks_length_stack; eauto.
Qed.

Theorem record_push_inject_alloc: 
  forall m01 m02 m1 m2 j0 j g fsz b1 b2 sz m1',
  inject j0 g m01 m02 ->
  alloc m01 0 fsz = (m1, b1) ->
  alloc m02 0 fsz = (m2, b2) ->
  inject j g m1 m2 ->
  (forall b : block, b <> b1 -> j b = j0 b) ->
  j b1 = Some (b2, 0) ->
  record_stack_blocks m1 (make_singleton_frame_adt b1 fsz sz) = Some m1' ->
  top_tframe_tc (stack m02) ->
  size_stack (tl (stack m02)) <= size_stack (tl (stack m01)) ->
  exists m2' : mem,
    record_stack_blocks m2 (make_singleton_frame_adt b2 fsz sz) = Some m2' /\
    inject j g m1' m2'.
Proof.
  intros m01 m02 m1 m2 j0 j g fsz b1 b2 sz m1' MINJ0 ALLOC1 ALLOC2 MINJ OLD NEW RSB TTT SZ.
  eapply record_stack_blocks_inject_parallel. eauto. 7: eauto. all: eauto.
  - red; simpl. constructor; auto.
    simpl. rewrite NEW. inversion 1; subst. eauto.
  - unfold in_frame; simpl.
    erewrite alloc_stack_unchanged by eauto.
    intros b H. eapply in_stack_valid in H. red in H.
    intros [A|[]]; subst.
    eapply fresh_block_alloc; eauto.
  - red; unfold in_frame; simpl. intros b [[]|[]].
    eapply valid_new_block; eauto.
  - simpl.
    intros ? ? ? ? ? [A|[]]. inv A.
    intro P; eapply perm_alloc_inv in P; eauto. destr_in P.
    simpl. rewrite Z.max_r; omega.
  - unfold in_frame; simpl.
    intros b0 b3 delta JB.
    split; intros [A|[]]; inv A; left. congruence.
    destruct (peq b1 b0); auto.
    rewrite OLD in JB by auto.
    eapply valid_block_inject_2 in JB; eauto.
    eapply fresh_block_alloc in JB. easy. eauto.
  - erewrite alloc_stack_unchanged by eauto. auto.
  - erewrite (alloc_stack_unchanged _ _ _ _ _ ALLOC1), (alloc_stack_unchanged _ _ _ _ _ ALLOC2); auto.
Qed.

Theorem record_push_inject_flat_alloc:
  forall m01 m02 m1 m2 j0 j fsz b1 b2 sz m1',
  inject j0 (flat_frameinj (length (stack m01))) m01 m02 ->
  alloc m01 0 fsz = (m1, b1) ->
  alloc m02 0 fsz = (m2, b2) ->
  inject j (flat_frameinj (length (stack m01))) m1 m2 ->
  (forall b : block, b <> b1 -> j b = j0 b) ->
  j b1 = Some (b2, 0) ->
  record_stack_blocks m1 (make_singleton_frame_adt b1 fsz sz) = Some m1' -> 
  top_tframe_tc (stack m02) ->
  size_stack (tl (stack m02)) <= size_stack (tl (stack m01)) ->
  exists m2' : mem,
    record_stack_blocks m2 (make_singleton_frame_adt b2 fsz sz) = Some m2' /\
    inject j (flat_frameinj (length (stack m1'))) m1' m2'.
Proof.
  intros m01 m02 m1 m2 j0 j fsz b1 b2 sz m1' MINJ0 ALLOC1 ALLOC2 MINJ OLD NEW RSB TTT SZ.
  eapply record_push_inject_alloc. 7: eauto. 2: eauto. all: eauto.
  erewrite record_stack_blocks_length_stack, alloc_stack_unchanged; eauto.
  erewrite record_stack_blocks_length_stack, alloc_stack_unchanged; eauto.
Qed.

Theorem record_push_extends_flat_alloc: 
  forall m01 m02 m1 m2 fsz b sz m1',
  alloc m01 0 fsz = (m1, b) ->
  alloc m02 0 fsz = (m2, b) ->
  extends m1 m2 ->
  record_stack_blocks m1 (make_singleton_frame_adt b fsz sz) = Some m1' ->
  top_tframe_tc (stack m02) ->
  size_stack (tl (stack m02)) <= size_stack (tl (stack m01)) ->
  exists m2' : mem,
    record_stack_blocks m2 (make_singleton_frame_adt b fsz sz) = Some m2' /\
    extends m1' m2'.
Proof. 
  intros m01 m02 m1 m2 fsz b sz m1' ALLOC1 ALLOC2 MINJ RSB TTT SZ.
  eapply record_stack_blocks_extends; eauto.
  + unfold in_frame. simpl. intros ? [?|[]]; subst.
    intro IFF.
    erewrite alloc_stack_unchanged in IFF; eauto.
    eapply in_stack_valid in IFF. eapply fresh_block_alloc in ALLOC2. congruence.
  + intros bb fi o k0 p [AA|[]] P; inv AA. simpl.
    eapply perm_alloc_inv in P; eauto. destr_in P. rewrite Z.max_r; omega.
  + erewrite alloc_stack_unchanged; eauto.
  + erewrite (alloc_stack_unchanged _ _ _ _ _ ALLOC1), (alloc_stack_unchanged _ _ _ _ _ ALLOC2); auto.
Qed.

(* Properties of [unrecord_stack_block] *)

Lemma unrecord_stack_block_mem_inj_parallel:
  forall (m1 m1' m2 : mem) (j : meminj) g
    (MINJ:  mem_inj j (1%nat :: g) m1 m2)
    (USB: unrecord_stack_block m1 = Some m1'),
  exists m2',
    unrecord_stack_block m2 = Some m2' /\
    mem_inj j g m1' m2'.
Proof.
  intros.
  unfold_unrecord.
  inversion MINJ. rewrite H in mi_stack_blocks0.
  inversion mi_stack_blocks0. subst.
  unfold unrecord_stack_block.
  setoid_rewrite <- H4. eexists; split; eauto.
  constructor; simpl; intros; eauto.
  {
    change (perm m1 b1 ofs k p) in H1.
    change (perm m2 b2 (ofs + delta) k p). eauto.
  }
  eapply stack_inject_invariant_strong.
  - intros b ofs k p b' delta JB PERM. change (perm m1 b ofs k p) in PERM. eauto.
  - rewrite H, <- H4 in *. simpl.
    eapply stack_inject_unrecord_parallel; eauto. 
    rewrite H4; eapply stack_inv_norepet, mem_stack_inv.
Qed.


Theorem unrecord_stack_block_inject_parallel:
  forall (m1 m1' m2 : mem) (j : meminj) g,
  inject j (1%nat :: g) m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  exists m2', unrecord_stack_block m2 = Some m2' /\ inject j g m1' m2'.
Proof.
  intros m1 m1' m2 j g INJ USB.
  generalize (unrecord_stack_block_mem_unchanged _ _ USB). simpl. intros (NB & PERM & UNCH & LOAD).
  edestruct unrecord_stack_block_mem_inj_parallel as (m2' & USB' & MINJ); eauto. inv INJ; eauto.
  generalize (unrecord_stack_block_mem_unchanged _ _ USB'). simpl. intros (NB' & PERM' & UNCH' & LOAD').
  exists m2'; split; eauto.
  inv INJ; constructor; eauto.
  - unfold valid_block; rewrite NB; eauto.
  - unfold valid_block; rewrite NB'; eauto.
  - red; intros. rewrite PERM in H2, H3. eauto.
  - intros. exploit mi_representable0.  eauto. intros (A & B).
    split; auto. intros ofs. rewrite ! PERM. eauto.
  - intros. rewrite PERM' in H0. rewrite ! PERM; eauto.
Qed.

Lemma stack_inject_unrecord_left:
  forall j n g m1 s1 s2
    (SI: stack_inject j m1 (S n :: g)  s1 s2)
    (LE: (1 <= n)%nat)
    (TOPNOPERM: top_tframe_prop (fun tf => forall b, in_frames tf b -> forall o k p, ~ m1 b o k p) s1)
    f l
    (STK1 : s1 = f :: l),
    stack_inject j m1 (n :: g) l s2.
Proof.
  intros. subst.
  inv SI. simpl in TAKE. repeat destr_in TAKE.
  destruct n. omega. econstructor; eauto. inv FI; auto.
Qed.

Lemma unrecord_stack_block_mem_inj_left:
  forall (m1 m1' m2 : mem) (j : meminj) n g,
    mem_inj j (S n :: g) m1 m2 ->
    unrecord_stack_block m1 = Some m1' ->
    (1 <= n)%nat ->
    top_frame_no_perm m1 ->
    mem_inj j (n :: g) m1' m2.
Proof.
  intros m1 m1' m2 j n g MI USB LE TOPNOPERM.
  unfold_unrecord.
  inv MI; constructor; simpl; intros; eauto.
  eapply stack_inject_unrecord_left.
  eapply stack_inject_invariant_strong.
  intros b ofs k p b' delta JB PERM. change (perm m1 b ofs k p) in PERM. eauto.
  eauto. intuition. eauto. rewrite H. simpl. eauto.
Qed.

Theorem unrecord_stack_block_inject_left:
  forall (m1 m1' m2 : mem) (j : meminj) n g,
  inject j (S n :: g) m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  (1 <= n)%nat ->
  top_frame_no_perm m1 ->
  inject j (n :: g) m1' m2.
Proof.
  intros m1 m1' m2 j n g INJ USB LE NOPERM.
  generalize (unrecord_stack_block_mem_unchanged _ _ USB). simpl. intros (NB & PERM & UNCH & LOAD).
  inv INJ; constructor; eauto.
  - eapply unrecord_stack_block_mem_inj_left; eauto. 
  - unfold valid_block; rewrite NB; eauto.
  - red; intros. rewrite PERM in H2, H3. eauto.
  - intros. exploit mi_representable0.  eauto. intros (A & B).
    split; auto. intros ofs. rewrite ! PERM. eauto.
  - intros. rewrite ! PERM; eauto.
Qed.

Theorem unrecord_stack_eq:
  forall m m',
  unrecord_stack_block m = Some m' ->
  exists b, stack m = b :: stack m'.
Proof.
  intros. unfold_unrecord. simpl. rewrite H0. eauto.
Qed.

Theorem unrecord_stack_block_extends:
  forall m1 m2 m1',
  extends m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  exists m2',
  unrecord_stack_block m2 = Some m2' /\
  extends m1' m2'.
Proof.
  intros.
  edestruct unrecord_stack_eq as (b & EQ). eauto.
  inversion H. rewrite EQ in mext_inj0.
  exploit unrecord_stack_block_mem_inj_parallel. apply mext_inj0. eauto. 
  intros (m2' & A & B).
  eexists; split; eauto.
  exploit unrecord_stack_block_mem_unchanged. apply H0.
  intros (Eqnb1 & Perm1 & UNCH1 & LOAD1).
  exploit unrecord_stack_block_mem_unchanged. apply A.
  intros (Eqnb2 & Perm2 & UNCH2 & LOAD2).
  simpl in *.
  constructor; auto. congruence.
  intros b0 ofs k p.
  rewrite ! Perm1. rewrite Perm2; auto.
  destruct (unrecord_stack_eq _ _ H0). rewrite H1 in mext_length_stack0.
  destruct (unrecord_stack_eq _ _ A). rewrite H2 in mext_length_stack0.
  simpl in mext_length_stack0; congruence.  
Qed.

Theorem unrecord_stack_block_succeeds:
  forall m b r,
  stack m = b :: r ->
  exists m', unrecord_stack_block m = Some m' /\ stack m' = r.
Proof.
  unfold unrecord_stack_block.
  intros.
  setoid_rewrite H. eexists; split; eauto. simpl. rewrite H; reflexivity.
Qed.

Theorem unrecord_stack_block_inject_neutral:
  forall thr m m',
  inject_neutral thr m ->
  unrecord_stack_block m = Some m' ->
  inject_neutral thr m'.
Proof.
  intros.
  destruct (unrecord_stack_eq _ _ H0). red in H.
  exploit unrecord_stack_block_mem_inj_parallel. rewrite H1 in H; simpl in H; eauto. eauto.
  intros (m2' & RSB & MI). rewrite H0 in RSB; inv RSB.
  eauto.
Qed.

Theorem unrecord_stack_block_inject_parallel_flat:
  forall (m1 m1' m2 : mem) (j : meminj),
  inject j (flat_frameinj (length (stack m1))) m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  exists m2',
    unrecord_stack_block m2 = Some m2' /\
    inject j (flat_frameinj (length (stack m1'))) m1' m2'.
Proof.
  intros m1 m1' m2 j INJ USB.
  edestruct unrecord_stack_eq as (b & EQ). eauto. rewrite EQ in INJ. simpl in INJ.
  destruct (unrecord_stack_block_inject_parallel _ _ _ _ _ INJ USB)
    as (m2' & USB' & INJ').
  rewrite USB'. eexists; split;  eauto.
Qed.

Theorem unrecord_stack_block_unchanged_on:
  forall m m' P,
  unrecord_stack_block m = Some m' ->
  unchanged_on P m m'.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition.
Qed.

Theorem unrecord_stack_block_perm:
  forall m m',
  unrecord_stack_block m = Some m' ->
  forall b' o k p,
  perm m' b' o k p ->
  perm m b' o k p.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition. apply H; auto.
Qed.

Theorem unrecord_stack_block_perm': 
  forall m m' : mem,
  unrecord_stack_block m = Some m' ->
  forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
  perm m b' o k p -> perm m' b' o k p.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition. apply H; auto.
Qed.

Theorem unrecord_stack_block_nextblock:
  forall m m',
  unrecord_stack_block m = Some m' ->
  nextblock m' = nextblock m.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition.
Qed.

Theorem unrecord_stack_block_get_frame_info:
  forall m m' b,
  unrecord_stack_block m = Some m' ->
  ~ is_stack_top (stack m) b ->
  get_frame_info (stack m') b = get_frame_info (stack m) b.
Proof.
  unfold is_stack_top, get_stack_top_blocks, get_frame_info. intros.
  exploit unrecord_stack_eq. eauto. intros (b0 & EQ).
  rewrite EQ in *. simpl.
  destr.
Qed.

(* Interaction of [unrecord_stack] with [push_new_stage] *)

Theorem unrecord_push:
  forall m, unrecord_stack_block (push_new_stage m) = Some m.
Proof.
  unfold unrecord_stack_block, push_new_stage. simpl. intros.
  f_equal. destruct m. simpl. apply mkmem_ext; auto.
Qed.

Theorem push_storebytes_unrecord:
  forall m b o bytes m1 m2,
  storebytes m b o bytes = Some m1 ->
  storebytes (push_new_stage m) b o bytes = Some m2 ->
  unrecord_stack_block m2 = Some m1.
Proof.
  unfold storebytes, unrecord_stack_block. simpl; intros.
  repeat destr_in H0. simpl in *.
  repeat destr_in H. f_equal.
  apply mkmem_ext; auto.
Qed.

Theorem push_store_unrecord:
  forall m b o chunk v m1 m2,
  store chunk m b o v = Some m1 ->
  store chunk (push_new_stage m) b o v = Some m2 ->
  unrecord_stack_block m2 = Some m1.
Proof.
  unfold store, unrecord_stack_block. simpl; intros.
  destr_in H0. destr_in H.
  repeat destr_in Heqo1. repeat destr_in Heqo0. inv H; inv H0. simpl in *. f_equal.
  apply mkmem_ext; auto.
Qed.

(* Interaction of [tailcall_stage] and [push_new_stage] *)

Lemma stack_inject_new_stage_left_tailcall_right:
  forall j n g m t1 s1 t2 s2,
    (forall a l,
        take (n) (t1::s1) = Some l ->
        In a l ->
        tframe_inject j m a t2 -> forall b, in_frames a b ->
                                                   forall o k p , ~ m b o k p) ->
    stack_inject j m (n::g) (t1::s1) (t2::s2) ->
    stack_inject j m (S n :: g) ((None,nil)::t1::s1) ((None,opt_cons (fst t2) (snd t2))::s2).
Proof.
  intros j n g m t1 s1 t2 s2 NOPERM SI. inv SI; simpl in *. repeat destr_in TAKE.
  econstructor; simpl. rewrite Heqo. eauto. eauto. eauto.
  constructor. red; simpl; congruence.
  eapply Forall_impl. 2: apply FI.
  simpl; intros. red; simpl.
  intros f0 EQ (b & o & k & p & NONE & IFR & PERM).
  eapply NOPERM in PERM; eauto. easy.
  red. rewrite EQ. auto.
Qed.

Theorem inject_new_stage_left_tailcall_right:
  forall j n g m1 m2,
  inject j (n :: g) m1 m2 ->
  (forall l, 
    take ( n) (stack m1) = Some l ->
    Forall (fun tf => forall b, in_frames tf b -> forall o k p, ~ perm m1 b o k p) l) ->
  top_frame_no_perm m2 ->
  exists m2',
    tailcall_stage m2 = Some m2' /\
    inject j (S n :: g) (push_new_stage m1) m2'.
Proof.
  intros j n g m1 m2 INJ NP1 TTP.
  assert (exists m2', tailcall_stage_stack m2 = Some m2').
  {
    unfold tailcall_stage_stack.  destr; eauto.
  }
  destruct H as (m2' & TCS).
  unfold tailcall_stage. eexists; split.
  eapply constr_match. eauto.
  Unshelve. all: eauto.
  eapply stack_inject_inject; eauto; try tauto.
  simpl.
  change (perm (push_new_stage m1)) with (perm m1).
  inv TTP. intro SI. remember SI as SI'. clear HeqSI'. inv SI. 
  simpl in *. repeat destr_in TAKE. simpl in *.
  unfold tailcall_stage_stack in TCS; repeat destr_in TCS.
  eapply stack_inject_new_stage_left_tailcall_right; simpl; eauto.
  - rewrite <- H. simpl.
    rewrite Heqo.
    intros a l0 EQ IN TFI b INFR o k p P. inv EQ.
    specialize (NP1 _ eq_refl).
    rewrite Forall_forall in NP1; eapply NP1; eauto.
  - rewrite <- H. simpl. assumption.
Qed.

Theorem inject_tailcall_left_new_stage_right:
  forall (j : meminj) (n : nat) (g : list nat) (m1 m2 m1' : mem),
  inject j (S n :: g) m1 m2 ->
  lt O n ->
  tailcall_stage m1 = Some m1' ->
  inject j (1%nat:: n :: g) m1' (push_new_stage m2).
Proof.
  intros j n g m1 m2 m1' INJ LT TC.
  unfold tailcall_stage in TC.
  pattern m1'. eapply destr_dep_match. apply TC. clear TC. intros; subst.
  eapply stack_inject_inject; eauto; try tauto.
  simpl.
  change (perm _) with (perm m1).
  unfold tailcall_stage_stack in pf. repeat destr_in pf. inv t. simpl. intro SI.
  - inv SI. simpl in *. repeat destr_in TAKE.
    econstructor; simpl; eauto.
    destruct n. omega. econstructor; eauto.
    + inv FI. auto.
    + inv FI.
      constructor; auto.
      red; simpl. easy.
Qed.

(* properties of [record_init_sp] *)

Theorem record_init_sp_stack:
  forall m1 m2,
  record_init_sp m1 = Some m2 ->
  stack m2 = (Some (make_singleton_frame_adt (nextblock (push_new_stage m1)) 0 0),nil)::stack m1.
Proof.
  unfold record_init_sp. intros m1 m2 RIS; destr_in RIS.
  destruct (record_stack_blocks_stack_eq _ _ _ RIS) as (tf & r & EQ1 & EQ2).
  rewrite EQ2. 
  erewrite (alloc_stack_unchanged _ _ _ _ _ Heqp) in EQ1.
  rewrite push_new_stage_stack in EQ1. inv EQ1.
  exploit alloc_result; eauto. intros; subst. reflexivity.
Qed.

Theorem record_init_sp_nextblock:
  forall m1 m2,
    record_init_sp m1 = Some m2 ->
    Ple (nextblock m1) (nextblock m2).
Proof.
    intros m1 m2 RIS.
    unfold record_init_sp in RIS. destr_in RIS.
    erewrite (record_stack_block_nextblock _ _ _ RIS).
    erewrite (nextblock_alloc _ _ _ _ _ Heqp).
    rewrite push_new_stage_nextblock. xomega.
  Qed.

Theorem record_init_sp_nextblock_eq:
  forall m1 m2,
  record_init_sp m1 = Some m2 ->
  (nextblock m2) = Pos.succ (nextblock m1).
Proof.
  intros m1 m2 RIS.
  unfold record_init_sp in RIS. destr_in RIS.
  erewrite (record_stack_block_nextblock _ _ _ RIS).
  erewrite (nextblock_alloc _ _ _ _ _ Heqp).
  rewrite push_new_stage_nextblock. reflexivity.
Qed.

Theorem record_init_sp_perm:
  forall m1 m2,
  record_init_sp m1 = Some m2 ->
  forall b o k p,
  perm m2 b o k p <-> perm m1 b o k p.
Proof.
  unfold record_init_sp. intros m1 m2 RIS; destr_in RIS.
  intros.
  split; intro P.
- eapply push_new_stage_perm.
  eapply record_stack_block_perm in P. 2: eauto.
  eapply perm_alloc_inv in P; eauto.
  destr_in P. omega.
- eapply record_stack_block_perm'. eauto.
  eapply perm_alloc_1. eauto.
  eapply push_new_stage_perm. auto.
Qed.

Theorem record_init_sp_inject:
  forall j g m1 m1' m2,
    inject j g m1 m1' ->
    size_stack (stack m1') <= size_stack (stack m1) ->
    record_init_sp m1 = Some m2 ->
    exists m2', record_init_sp m1' = Some m2' 
              /\ inject (fun b => if peq b (nextblock (push_new_stage m1))
                                  then Some (nextblock (push_new_stage m1'), 0)
                                  else j b) (1%nat::g) m2 m2'.
Proof.
    intros j g m1 m1' m2 INJ SZ RIS.
    unfold record_init_sp in *; destr_in RIS.
    exploit Mem.push_new_stage_inject. apply INJ. intro INJ0.
    edestruct Mem.alloc_parallel_inject as (f' & m2' & b2 & ALLOC & INJ1 & INCR & JNEW & JOLD).
    apply INJ0. eauto. reflexivity. reflexivity.
    rewrite ALLOC.
    edestruct record_push_inject_alloc as (m2'' & RSB & INJ'). 7: apply RIS.
    2: apply Heqp. 2: apply ALLOC. all: eauto.
    rewrite push_new_stage_stack. constructor; reflexivity.

    eexists; split. eauto.
    eapply inject_ext. eauto.
    intros. erewrite <- ! alloc_result by eauto.
    destr. eauto.
Qed.


Theorem record_init_sp_flat_inject: 
  forall (m1 m1' m2 : mem),
    inject (flat_inj (nextblock m1)) (flat_frameinj (length (stack m1))) m1 m1' ->
    size_stack (stack m1') <= size_stack (stack m1) ->
    record_init_sp m1 = Some m2 ->
    nextblock m1 = nextblock m1' ->
    exists m2' : mem,
      record_init_sp m1' = Some m2' /\
      inject
        (flat_inj (nextblock m2))
        (flat_frameinj (length (stack m2))) m2 m2'.
Proof.
  intros m1 m1' m2 INJ SZ RIS EQNB.
  edestruct record_init_sp_inject as (m2' & RIS' & INJ'); eauto.
  eexists; split; eauto.
  unfold record_init_sp in RIS; destr_in RIS.
  erewrite (record_stack_block_nextblock _ _ _ RIS).
  erewrite (nextblock_alloc _ _ _ _ _ Heqp).
  rewrite push_new_stage_nextblock.
  destruct (record_stack_blocks_stack_eq _ _ _ RIS) as (tf & r & EQ1 & EQ2).
  rewrite EQ2. 
  erewrite (alloc_stack_unchanged _ _ _ _ _ Heqp) in EQ1.
  rewrite push_new_stage_stack in EQ1. inv EQ1.
  simpl. rewrite frameinj_push_flat.
  eapply inject_ext; eauto.
  simpl; intros. unfold flat_inj.
  repeat (destr; subst); xomega.
Qed.


(* Perm equivalences *)

Theorem store_perm:
  forall chunk m b' o' v m',
  store chunk m b' o' v = Some m' ->
  forall b o k p,
  perm m' b o k p <-> perm m b o k p.
Proof.
  split; intros.
  eapply perm_store_2; eauto.
  eapply perm_store_1; eauto.
Qed.

Theorem storev_perm:
  forall chunk m addr v m',
  storev chunk m addr v = Some m' ->
  forall b o k p,
  perm m' b o k p <-> perm m b o k p.
Proof.
  intros. destruct addr; simpl in *; try congruence.
  eapply store_perm; eauto.
Qed.

Theorem free_perm:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  forall b' o k p,
  perm m' b' o k p <-> if peq b b' && zle lo o && zlt o hi then False else perm m b' o k p.
Proof.
  intros.
  destr.
  - rewrite ! andb_true_iff in Heqb0. intuition.
    destruct zlt; simpl in *; try congruence.
    destruct zle; simpl in *; try congruence.
    destruct peq; simpl in *; try congruence.
    subst.
    eapply perm_free_2; eauto.
  - rewrite ! andb_false_iff in Heqb0.
    split; intros.
    + eapply perm_free_3; eauto.
    + eapply perm_free_1; eauto.
      destruct Heqb0. destruct H1. destruct peq; simpl in *; try congruence. auto.
      destruct zle; simpl in *; try congruence. right. left. omega.
      destruct zlt; simpl in *; try congruence. right. right. omega.
Qed.

Theorem alloc_perm:
  forall m lo hi m' b,
  alloc m lo hi = (m',b) ->
  forall b' o k p,
  perm m' b' o k p <-> if peq b b' then lo <= o < hi else perm m b' o k p.
Proof.
  split; intros.
  eapply perm_alloc_inv in H0; eauto. destr_in H0; subst; destr.
  destr_in H0. subst.
  eapply perm_implies. eapply perm_alloc_2; eauto. constructor.
  eapply perm_alloc_1; eauto.
Qed.

Theorem record_perm:
  forall m fi m',
  record_stack_blocks m fi = Some m' ->
  forall b o k p,
  perm m' b o k p <-> perm m b o k p.
Proof.
  split; intros.
  eapply record_stack_block_perm; eauto.
  eapply record_stack_block_perm'; eauto.
Qed.


Theorem unrecord_perm:
  forall m m',
  unrecord_stack_block m = Some m' ->
  forall b o k p,
  perm m' b o k p <-> perm m b o k p.
Proof.
  split; intros.
  eapply unrecord_stack_block_perm; eauto.
  eapply unrecord_stack_block_perm'; eauto.
Qed.

Theorem drop_perm_perm:
  forall m b lo hi p m',
  drop_perm m b lo hi p = Some m' ->
  forall b' o k p',
  perm m' b' o k p' <-> (perm m b' o k p' /\( b = b' -> lo <= o < hi -> perm_order p p')).
Proof.
  intros.
  split.
  intros PERM.
  split.
  eapply perm_drop_4; eauto. intros; subst.
  eapply perm_drop_2; eauto.
  intros (A & B).
  destruct (peq b b').
  2: eapply perm_drop_3; eauto.
  subst.
  trim B; auto.
  destruct (zle lo o).
  destruct (zlt o hi). trim B. omega.
  eapply perm_implies.
  eapply perm_drop_1; eauto. auto.
  eapply perm_drop_3; eauto. right; right. omega.
  eapply perm_drop_3; eauto. right; left. omega.
Qed.

End Mem.

Notation mem := Mem.mem.

Global Opaque Mem.alloc Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Hint Resolve
  Mem.valid_not_valid_diff
  Mem.perm_implies
  Mem.perm_cur
  Mem.perm_max
  Mem.perm_valid_block
  Mem.range_perm_implies
  Mem.range_perm_cur
  Mem.range_perm_max
  Mem.valid_access_implies
  Mem.valid_access_valid_block
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.loadbytes_range_perm
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.nextblock_store
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.storebytes_range_perm
  Mem.perm_storebytes_1
  Mem.perm_storebytes_2
  Mem.storebytes_valid_access_1
  Mem.storebytes_valid_access_2
  Mem.nextblock_storebytes
  Mem.storebytes_valid_block_1
  Mem.storebytes_valid_block_2
  Mem.nextblock_alloc
  Mem.alloc_result
  Mem.valid_block_alloc
  Mem.fresh_block_alloc
  Mem.valid_new_block
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_4
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.nextblock_free
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
  Mem.unchanged_on_refl
 : mem.


