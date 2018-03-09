(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.
Require Import MemPerm.
Require Import StackADT.


Definition store_spec_of_ofs_spec b (l: list (memory_chunk * ptrofs * val)) : list (memory_chunk * val * val) :=
  (map (fun cov => let '(ch, o, v) := cov in (ch, Vptr b o, v)) l).

Module Mem.

Definition locset := block -> Z -> Prop.

Close Scope nat_scope.

Class MemoryModelOps
      (** The abstract type of memory states. *)
 (mem: Type)

: Type
 :=
{

(** * Operations on memory states *)

(** [empty] is the initial memory state. *)
  empty: mem;

(** [alloc m lo hi] allocates a fresh block of size [hi - lo] bytes.
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
 alloc: forall (m: mem) (lo hi: Z), mem * block;

(** [free m b lo hi] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b].  Returns the updated memory
  state, or [None] if the freed addresses are not writable. *)
 free: forall (m: mem) (b: block) (lo hi: Z), option mem;

(** [load chunk m b ofs] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the value read, or [None] if the accessed addresses
  are not readable. *)
 load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z), option val;

(** [store chunk m b ofs v] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable. *)
 store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val), option mem;

(** [loadbytes m b ofs n] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable. *)
 loadbytes: forall (m: mem) (b: block) (ofs n: Z), option (list memval);

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)
 storebytes: forall (m: mem) (b: block) (ofs: Z) (bytes: list memval), option mem;

(** [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

 drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission), option mem;

(** * Permissions, block validity, access validity, and bounds *)

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

 nextblock: mem -> block;

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
 perm: forall (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission), Prop;

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
 range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p;

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

 valid_pointer: forall (m: mem) (b: block) (ofs: Z), bool;

(** * Relating two memory states. *)

(** ** Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by relaxing the permissions of [m1] (for instance, allocating larger
  blocks) and replacing some of the [Vundef] values stored in [m1] by
  more defined values stored in [m2] at the same addresses. *)

 extends: forall {injperm: InjectPerm}, mem -> mem -> Prop;

(** The [magree] predicate is a variant of [extends] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [lessdef] relation.
  Needed by Deadcodeproof. *)

 magree: forall {injperm: InjectPerm} (m1 m2: mem) (P: locset), Prop;

(** ** Memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].

A memory injection [f] defines a relation [Val.inject] between values
that is the identity for integer and float values, and relocates pointer
values as prescribed by [f].  (See module [Values].)

Likewise, a memory injection [f] defines a relation between memory states
that we now axiomatize. *)

 inject: forall {injperm: InjectPerm}, meminj -> frameinj -> mem -> mem -> Prop;

(** Memory states that inject into themselves. *)

 inject_neutral: forall {injperm: InjectPerm} (thr: block) (m: mem), Prop;

(** ** Invariance properties between two memory states *)

 unchanged_on: forall (P: block -> Z -> Prop) (m_before m_after: mem), Prop
 ;

 (** Necessary to distinguish from [unchanged_on], used as
 postconditions to external function calls, whereas
 [strong_unchanged_on] will be used for ordinary memory operations. *)

 strong_unchanged_on: forall (P: block -> Z -> Prop) (m_before m_after: mem), Prop
 ;

 (* Stack ADT and methods *)
 stack_adt: mem -> stack_adt;
 (* Pushes a new stage on the stack, with no frames in it. *)
 push_new_stage: mem -> mem;
 record_stack_blocks: mem -> frame_adt -> option mem;
 (* record_stack_blocks_tailcall: mem -> frame_adt -> mem -> Prop; *)
 (* push_frame: mem -> frame_info -> list (memory_chunk * ptrofs * val) -> option (mem*block); *)
 (* record_stack_blocks_none: forall (m: mem) (bl : list (block * frame_info)) (sz: Z), *)
 (*                           Forall *)
 (*                             (fun b : block * frame_info => *)
 (*                                forall (o : Z) (k : perm_kind) (p : permission), perm m (fst b) o k p -> 0 <= o < frame_size (snd b)) bl ->  *)
 (*                           option mem; *)
 unrecord_stack_block: mem -> option mem;
 frame_inject f := StackADT.frame_inject f;
 stack_limit: Z;
}.


Section WITHMEMORYMODELOPS.
Context `{memory_model_ops: MemoryModelOps}.
Context {injperm: InjectPerm}.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end.

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => None
  end.

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).


Definition valid_frame f m :=
  forall b, in_frame f b -> valid_block m b.

(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs)
  /\ (perm_order p Writable -> stack_access ( (stack_adt m)) b ofs (ofs + size_chunk chunk)).

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

(** Integrity of pointer values. *)

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Definition abstract_unchanged (T: mem -> mem -> Prop) :=
  forall m1 m2, T m1 m2 -> stack_adt m2 = stack_adt m1.

Definition mem_unchanged (T: mem -> mem -> Prop) :=
  forall m1 m2, T m1 m2 ->
           nextblock m2 = nextblock m1
           /\ (forall b o k p, perm m2 b o k p <-> perm m1 b o k p)
           /\ (forall P, strong_unchanged_on P m1 m2)
           /\ (forall b o chunk, load chunk m2 b o = load chunk m1 b o).

Definition wf_tframe_strong (m: perm_type) (j: meminj) (f: tframe_adt) : Prop :=
  forall b,
    j b <> None ->
    in_frames f b ->
    forall o k p, ~ m b o k p.

Inductive top_tframe_prop (P: tframe_adt -> Prop) : StackADT.stack_adt -> Prop :=
| top_tframe_prop_intro tf r:
    P tf ->
    top_tframe_prop P (tf::r).

Definition top_tframe_no_perm (m: perm_type) (s: StackADT.stack_adt) : Prop :=
  top_tframe_prop (wf_tframe_strong m inject_id) s.

End WITHMEMORYMODELOPS.

Class MemoryModel mem `{memory_model_ops: MemoryModelOps mem} 
  : Prop :=
{

 valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b';

(** Logical implications between permissions *)

 perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2;

(** The current permission is always less than or equal to the maximal permission. *)

 perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p;
 perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p;
 perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p;

(** Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
 perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b;

 range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2;

 range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p;

 range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p;

 valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2;

 valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b;

 valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p;

 valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty;
 valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty;

 weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true;
 valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true;

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

 nextblock_empty: nextblock empty = 1%positive;
 perm_empty: forall b ofs k p, ~perm empty b ofs k p;
 valid_access_empty:
  forall chunk b ofs p, ~valid_access empty chunk b ofs p;

(** ** Properties of [load]. *)

(** A load succeeds if and only if the access is valid for reading *)
 valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v;
 load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable;

(** The value returned by [load] belongs to the type of the memory quantity
  accessed: [Vundef], [Vint] or [Vptr] for an integer quantity,
  [Vundef] or [Vfloat] for a float quantity. *)
 load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk);

(** For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
 load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end;

 load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs);

 load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs);

 loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv  Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2);

(** ** Properties of [loadbytes]. *)

(** [loadbytes] succeeds if and only if we have read permissions on the accessed
    memory area. *)

 range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes;
 loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable;

(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
 loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes);

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
 load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes;

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
 loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n;

 loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil;

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
 loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2);
 loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2;

(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [store] succeeds if and only if the corresponding access
  is valid for writing. *)

 nextblock_store:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  nextblock m2 = nextblock m1;
 store_valid_block_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b';
 store_valid_block_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b';

 perm_store_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p;
 perm_store_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p;

 valid_access_store':
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  exists m2: mem, store chunk m1 b ofs v = Some m2;
 store_valid_access_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p;
 store_valid_access_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p;
 store_valid_access_3:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  valid_access m1 chunk b ofs Writable;

(** Load-store properties. *)

 load_store_similar:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v';
 load_store_similar_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v);

 load_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  load chunk m2 b ofs = Some (Val.load_result chunk v);

 load_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs';

 load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef;
 load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef;
 load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs');

(** Load-store properties for [loadbytes]. *)

 loadbytes_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v);
 loadbytes_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' n,
  b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n;

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

 store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v;
 store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v;
 store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n);
 store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n);
 store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n);
 store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n);
 storev_int64_split:
  forall m a v m',
  storev Mint64 m a v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m';

(** ** Properties of [storebytes]. *)

(** [storebytes] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [storebytes] succeeds if and only if we have write permissions
  on the addressed memory area. *)

 range_perm_storebytes' :
  forall m1 b ofs bytes,
    range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
    stack_access ( (stack_adt m1)) b ofs (ofs + Z_of_nat (length bytes)) ->
  exists m2 : mem, storebytes m1 b ofs bytes = Some m2;
 storebytes_range_perm:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
                       range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable;
 storebytes_stack_access:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
     stack_access ( (stack_adt m1)) b ofs (ofs + Z_of_nat (length bytes)) ;
 perm_storebytes_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p;
 perm_storebytes_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p;
 storebytes_valid_access_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p;
 storebytes_valid_access_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p;
 nextblock_storebytes:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  nextblock m2 = nextblock m1;
 storebytes_valid_block_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b';
 storebytes_valid_block_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b';

(** Connections between [store] and [storebytes]. *)

 storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2;

 store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2;

(** Load-store properties. *)

 loadbytes_storebytes_same:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  loadbytes m2 b ofs (Z_of_nat (length bytes)) = Some bytes;
 loadbytes_storebytes_disjoint:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z_of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len;
 loadbytes_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len;
 load_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs';

(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

 storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2;
 storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2;

(** ** Properties of [alloc]. *)

(** The identifier of the freshly allocated block is the next block
  of the initial memory state. *)

 alloc_result:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  b = nextblock m1;

(** Effect of [alloc] on block validity. *)

 nextblock_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  nextblock m2 = Psucc (nextblock m1);

 valid_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m1 b' -> valid_block m2 b';
 fresh_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  ~(valid_block m1 b);
 valid_new_block:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  valid_block m2 b;
 valid_block_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b';

(** Effect of [alloc] on permissions. *)

 perm_alloc_1:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p;
 perm_alloc_2:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable;
 perm_alloc_3:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi;
 perm_alloc_4:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p;
 perm_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p;

(** Effect of [alloc] on access validity. *)

 valid_access_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p;
 valid_access_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable;
 valid_access_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p;

(** Load-alloc properties. *)

 load_alloc_unchanged:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs;
 load_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v;
 load_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef;
 load_alloc_same':
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef;
 loadbytes_alloc_unchanged:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n;
 loadbytes_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef;

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] current permission. *)

 range_perm_free' :
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  exists m2: mem, free m1 b lo hi = Some m2;
 free_range_perm:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
                    range_perm m1 bf lo hi Cur Freeable;

(** Block validity is preserved by [free]. *)

 nextblock_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  nextblock m2 = nextblock m1;
 valid_block_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m1 b -> valid_block m2 b;
 valid_block_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m2 b -> valid_block m1 b;

(** Effect of [free] on permissions. *)

 perm_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p;
 perm_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p;
 perm_free_3:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p;

(** Effect of [free] on access validity. *)

 valid_access_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p;
 valid_access_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p);
 valid_access_free_inv_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p;
 valid_access_free_inv_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs;

(** Load-free properties *)

 load_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs;
 loadbytes_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes;

(** ** Properties of [drop_perm]. *)

 nextblock_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  nextblock m' = nextblock m;
 drop_perm_valid_block_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m b' -> valid_block m' b';
 drop_perm_valid_block_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m' b' -> valid_block m b';

 range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  range_perm m b lo hi Cur Freeable;
 range_perm_drop_2' :
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> exists m', drop_perm m b lo hi p = Some m';

 perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p;
 perm_drop_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p';
 perm_drop_3:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p';
 perm_drop_4:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p';

 loadbytes_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs n,
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n;
 load_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs;


(** ** Properties of [extends]. *)

 extends_refl {injperm: InjectPerm}:
  forall m, extends m m;

 load_extends {injperm: InjectPerm}:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2;

 loadv_extends {injperm: InjectPerm}:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2;

 loadbytes_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2;

 store_within_extends {injperm: InjectPerm}:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2';

 store_outside_extends {injperm: InjectPerm}:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2';

 storev_extends {injperm: InjectPerm}:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2';

 storebytes_within_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2';

 storebytes_outside_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z_of_nat (length bytes2) -> False) ->
  extends m1 m2';

 alloc_extends {injperm: InjectPerm}:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2';

 free_left_extends {injperm: InjectPerm}:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2;

 free_right_extends {injperm: InjectPerm}:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2';

 free_parallel_extends {injperm: InjectPerm}:
  forall m1 m2 b lo hi m1',
    extends m1 m2 ->
    inject_perm_condition Freeable ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2';

 valid_block_extends {injperm: InjectPerm}:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b);
 perm_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> inject_perm_condition p -> perm m2 b ofs k p;
 valid_access_extends {injperm: InjectPerm}:
  forall m1 m2 chunk b ofs p,
    extends m1 m2 -> valid_access m1 chunk b ofs p -> inject_perm_condition p ->
    valid_access m2 chunk b ofs p;
 valid_pointer_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true;
 weak_valid_pointer_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true;

  
(** ** Properties of [magree]. *)
 ma_perm {injperm: InjectPerm}:
   forall m1 m2 (P: locset),
     magree m1 m2 P ->
     forall b ofs k p,
       perm m1 b ofs k p ->
       inject_perm_condition p ->
       perm m2 b ofs k p;

 magree_monotone {injperm: InjectPerm}:
  forall m1 m2 (P Q: locset),
  magree m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree m1 m2 Q;

 mextends_agree {injperm: InjectPerm}:
  forall m1 m2 P, extends m1 m2 -> magree m1 m2 P;

 magree_extends {injperm: InjectPerm}:
  forall m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree m1 m2 P -> extends m1 m2;

 magree_loadbytes {injperm: InjectPerm}:
  forall m1 m2 P b ofs n bytes,
  magree m1 m2 P ->
  loadbytes m1 b ofs n = Some bytes ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  exists bytes', loadbytes m2 b ofs n = Some bytes' /\ list_forall2 memval_lessdef bytes bytes';

 magree_load {injperm: InjectPerm}:
  forall m1 m2 P chunk b ofs v,
  magree m1 m2 P ->
  load chunk m1 b ofs = Some v ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  exists v', load chunk m2 b ofs = Some v' /\ Val.lessdef v v';

 magree_storebytes_parallel {injperm: InjectPerm}:
  forall m1 m2 (P Q: locset) b ofs bytes1 m1' bytes2,
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + Z_of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2', storebytes m2 b ofs bytes2 = Some m2' /\ magree m1' m2' Q;

 magree_storebytes_left {injperm: InjectPerm}:
  forall m1 m2 P b ofs bytes1 m1',
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes1) -> ~(P b i)) ->
  magree m1' m2 P;

 magree_store_left {injperm: InjectPerm}:
  forall m1 m2 P chunk b ofs v1 m1',
  magree m1 m2 P ->
  store chunk m1 b ofs v1 = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b i)) ->
  magree m1' m2 P;

 magree_free {injperm: InjectPerm}:
  forall m1 m2 (P Q: locset) b lo hi m1',
    magree m1 m2 P ->
    inject_perm_condition Freeable ->
    free m1 b lo hi = Some m1' ->
    (forall b' i, Q b' i ->
             b' <> b \/ ~(lo <= i < hi) ->
             P b' i) ->
    exists m2', free m2 b lo hi = Some m2' /\ magree m1' m2' Q;

 magree_valid_access {injperm: InjectPerm}:
  forall m1 m2 (P: locset) chunk b ofs p,
  magree m1 m2 P ->
  valid_access m1 chunk b ofs p ->
  inject_perm_condition p ->
  valid_access m2 chunk b ofs p;

(** ** Properties of [inject]. *)
 mi_no_overlap {injperm: InjectPerm}:
   forall f g m1 m2,
   inject f g m1 m2 ->
   meminj_no_overlap f m1;

 mi_delta_pos {injperm: InjectPerm}:
   forall f g m1 m2 b1 b2 delta,
     inject f g m1 m2 ->
     f b1 = Some (b2, delta) ->
     delta >= 0;

 valid_block_inject_1 {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m1 b1;

 valid_block_inject_2 {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m2 b2;

 perm_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  perm m1 b1 ofs k p ->
  inject_perm_condition p ->
  perm m2 b2 (ofs + delta) k p;

 range_perm_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  inject_perm_condition p ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p;

 valid_access_inject {injperm: InjectPerm}:
  forall f g m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  inject_perm_condition p ->
  valid_access m2 chunk b2 (ofs + delta) p;

 valid_pointer_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true;

 weak_valid_pointer_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true;

 address_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 ofs1 b2 delta p,
  inject f g m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta;

 (** The following is needed by Separation, to prove storev_parallel_rule *)
 address_inject' {injperm: InjectPerm}:
  forall f g m1 m2 chunk b1 ofs1 b2 delta,
  inject f g m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta;

 valid_pointer_inject_no_overflow {injperm: InjectPerm}:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned;

 weak_valid_pointer_inject_no_overflow {injperm: InjectPerm}:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned;

 valid_pointer_inject_val {injperm: InjectPerm}:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true;

 weak_valid_pointer_inject_val {injperm: InjectPerm}:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true;

 inject_no_overlap {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f g m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2;

 different_pointers_inject {injperm: InjectPerm}:
  forall f g m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f g m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2));

 disjoint_or_equal_inject {injperm: InjectPerm}:
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
             \/ ofs2 + delta2 + sz <= ofs1 + delta1;

 aligned_area_inject {injperm: InjectPerm}:
  forall f g m m' b ofs al sz b' delta,
  inject f g m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta);

 load_inject {injperm: InjectPerm}:
  forall f g m1 m2 chunk b1 ofs b2 delta v1,
  inject f g m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2;

 loadv_inject {injperm: InjectPerm}:
  forall f g m1 m2 chunk a1 a2 v1,
  inject f g m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2;

 loadbytes_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 ofs len b2 delta bytes1,
  inject f g m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2;

 store_mapped_inject {injperm: InjectPerm}:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f g n1 n2;

 store_unmapped_inject {injperm: InjectPerm}:
  forall f g chunk m1 b1 ofs v1 n1 m2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2;

 store_outside_inject {injperm: InjectPerm}:
  forall f g m1 m2 chunk b ofs v m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f g m1 m2';

 storev_mapped_inject {injperm: InjectPerm}:
  forall f g chunk m1 a1 v1 n1 m2 a2 v2,
  inject f g m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f g n1 n2;

 storebytes_mapped_inject {injperm: InjectPerm}:
  forall f g m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f g n1 n2;

 storebytes_unmapped_inject {injperm: InjectPerm}:
  forall f g m1 b1 ofs bytes1 n1 m2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2;

 storebytes_outside_inject {injperm: InjectPerm}:
  forall f g m1 m2 b ofs bytes2 m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f g m1 m2';

 storebytes_empty_inject {injperm: InjectPerm}:
  forall f g m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f g m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f g m1' m2';

 alloc_right_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo hi b2 m2',
  inject f g m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f g m1 m2';

 alloc_left_unmapped_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo hi m1' b1,
  inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' g m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b);

 alloc_left_mapped_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo hi m1' b1 b2 delta,
  inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> inject_perm_condition p -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  (forall (fi : frame_info),
      in_stack' (stack_adt m2) (b2,fi) ->
      forall (o : Z) (k : perm_kind) (pp : permission), perm m1' b1 o k pp -> inject_perm_condition pp -> frame_public fi (o + delta)) ->
  exists f',
     inject f' g m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b);

 alloc_parallel_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f g m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' g m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b);

 free_inject {injperm: InjectPerm}:
  forall f g m1 l m1' m2 b lo hi m2',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f g m1' m2';

 free_left_inject {injperm: InjectPerm}:
  forall f g m1 m2 b lo hi m1',
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f g m1' m2;
 free_list_left_inject {injperm: InjectPerm}:
  forall f g m2 l m1 m1',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f g m1' m2;

 free_right_inject {injperm: InjectPerm}:
  forall f g m1 m2 b lo hi m2',
  inject f g m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2';

 free_parallel_inject {injperm: InjectPerm}:
  forall f g m1 m2 b lo hi m1' b' delta,
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  inject_perm_condition Freeable ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f g m1' m2';

 drop_outside_inject {injperm: InjectPerm}:
  forall f g m1 m2 b lo hi p m2',
    inject f g m1 m2 ->
    drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2';

(** The following property is needed by ValueDomain, to prove mmatch_inj. *)

 self_inject f m {injperm: InjectPerm}:
  (forall b, f b = None \/ f b = Some (b, 0)) ->
  (forall b, f b <> None -> valid_block m b) ->
  (forall b,
     f b <> None ->
     forall o b' o' q n,
       loadbytes m b o 1 = Some (Fragment (Vptr b' o') q n :: nil) ->
       f b' <> None) ->
  inject f (flat_frameinj (length (stack_adt m))) m m;

 inject_stack_adt {injperm: InjectPerm}:
   forall f g m1 m2,
     inject f g m1 m2 ->
     stack_inject f g (perm m1) ( (stack_adt m1)) ( (stack_adt m2));

 extends_stack_adt {injperm: InjectPerm}:
   forall m1 m2,
     extends m1 m2 ->
     stack_inject inject_id (flat_frameinj (length (stack_adt m1))) (perm m1) (stack_adt m1) (stack_adt m2);

(* Needed by Stackingproof, with Linear2 to Mach,
   to compose extends (in Linear2) and inject. *)
 extends_inject_compose {injperm: InjectPerm}:
   forall f g m1 m2 m3,
     extends m1 m2 -> inject f g m2 m3 -> inject f g m1 m3;

 (* Needed by EraseArgs. *)
 extends_extends_compose {injperm: InjectPerm}:
   forall m1 m2 m3,
     extends m1 m2 -> extends m2 m3 -> extends m1 m3;


(** ** Properties of [inject_neutral] *)

 neutral_inject {injperm: InjectPerm}:
  forall m, inject_neutral (nextblock m) m ->
  inject (flat_inj (nextblock m)) (flat_frameinj (length (stack_adt m))) m m;

 empty_inject_neutral {injperm: InjectPerm}:
  forall thr, inject_neutral thr empty;

 empty_stack_adt {injperm: InjectPerm}:
   stack_adt empty = nil;

 alloc_inject_neutral {injperm: InjectPerm}:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m';

 store_inject_neutral {injperm: InjectPerm}:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m';

 drop_inject_neutral {injperm: InjectPerm}:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m';
drop_perm_stack_adt {injperm: InjectPerm}:
  forall m1 b lo hi p m1',
    drop_perm m1 b lo hi p = Some m1' ->
    stack_adt m1' = stack_adt m1;

(** ** Properties of [unchanged_on] and [strong_unchanged_on] *)

 strong_unchanged_on_weak P m1 m2:
  strong_unchanged_on P m1 m2 ->
  unchanged_on P m1 m2;
 unchanged_on_nextblock P m1 m2:
  unchanged_on P m1 m2 ->
  Ple (nextblock m1) (nextblock m2);
 strong_unchanged_on_refl:
  forall P m, strong_unchanged_on P m m;
 unchanged_on_trans:
  forall P m1 m2 m3, unchanged_on P m1 m2 -> unchanged_on P m2 m3 -> unchanged_on P m1 m3;
 strong_unchanged_on_trans:
  forall P m1 m2 m3, strong_unchanged_on P m1 m2 -> strong_unchanged_on P m2 m3 -> strong_unchanged_on P m1 m3;
 perm_unchanged_on:
  forall P m m' b ofs k p,
  unchanged_on P m m' -> P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p;
 perm_unchanged_on_2:
  forall P m m' b ofs k p,
  unchanged_on P m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p;
 loadbytes_unchanged_on_1:
  forall P m m' b ofs n,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n;
 loadbytes_unchanged_on:
   forall P m m' b ofs n bytes,
     unchanged_on P m m' ->
     (forall i, ofs <= i < ofs + n -> P b i) ->
     loadbytes m b ofs n = Some bytes ->
     loadbytes m' b ofs n = Some bytes;
 load_unchanged_on_1:
  forall P m m' chunk b ofs,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs;
 load_unchanged_on:
   forall P m m' chunk b ofs v,
     unchanged_on P m m' ->
     (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
     load chunk m b ofs = Some v ->
     load chunk m' b ofs = Some v;
 store_strong_unchanged_on:
  forall P chunk m b ofs v m',
    store chunk m b ofs v = Some m' ->
    (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
    strong_unchanged_on P m m';
 storebytes_strong_unchanged_on:
  forall P m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  strong_unchanged_on P m m';
 alloc_strong_unchanged_on:
   forall P m lo hi m' b,
     alloc m lo hi = (m', b) ->
     strong_unchanged_on P m m';
 free_strong_unchanged_on:
  forall P m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  strong_unchanged_on P m m';
 drop_perm_strong_unchanged_on:
   forall P m b lo hi p m',
     drop_perm m b lo hi p = Some m' ->
     (forall i, lo <= i < hi -> ~ P b i) ->
     strong_unchanged_on P m m';
 unchanged_on_implies:
   forall (P Q: block -> Z -> Prop) m m',
     unchanged_on P m m' ->
     (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
     unchanged_on Q m m'
 ;
 strong_unchanged_on_implies:
   forall (P Q: block -> Z -> Prop) m m',
     strong_unchanged_on P m m' ->
     (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
     strong_unchanged_on Q m m'
 ;

(** The following property is needed by Separation, to prove
minjection. HINT: it can be used only for [strong_unchanged_on], not
for [unchanged_on]. *)

 inject_strong_unchanged_on j g m0 m m'  {injperm: InjectPerm}:
   inject j g m0 m ->
   strong_unchanged_on
     (fun (b : block) (ofs : Z) =>
        exists (b0 : block) (delta : Z),
          j b0 = Some (b, delta) /\
          perm m0 b0 (ofs - delta) Max Nonempty) m m' ->
   stack_adt m' = stack_adt m ->
   inject j g m0 m';

 (* Original operations don't modify the abstract part. *)
 store_no_abstract:
   forall chunk b o v, abstract_unchanged (fun m1 m2 => store chunk m1 b o v = Some m2);

 storebytes_no_abstract:
   forall b o bytes, abstract_unchanged (fun m1 m2 => storebytes m1 b o bytes = Some m2);

 alloc_no_abstract:
   forall lo hi b, abstract_unchanged (fun m1 m2 => alloc m1 lo hi = (m2, b));

 free_no_abstract:
   forall lo hi b, abstract_unchanged (fun m1 m2 => free m1 b lo hi = Some m2);

 freelist_no_abstract:
   forall bl, abstract_unchanged (fun m1 m2 => free_list m1 bl = Some m2);

 drop_perm_no_abstract:
   forall b lo hi p, abstract_unchanged (fun m1 m2 => drop_perm m1 b lo hi p = Some m2);

 (* Properties of record_stack_block *)

 record_stack_blocks_inject_left {injperm: InjectPerm}:
   forall m1 m1' m2 j g f1 f2
     (INJ: inject j g m1 m2)
     (FAP2: frame_at_pos (stack_adt m2) 0 f2)
     (FI: tframe_inject j (f1::nil) f2)
     (RSB: record_stack_blocks (push_new_stage m1) f1 = Some m1'),
     inject j (fun n : nat => if Nat.eq_dec n 0 then Some O else g (Init.Nat.pred n)) m1' m2;

 record_stack_blocks_inject_left' {injperm: InjectPerm}:
   forall m1 m1' m2 j g f1 f2
     (INJ: inject j g m1 m2)
     (FAP2: frame_at_pos (stack_adt m2) 0 f2)
     (G0: g O = Some O)
     (FI: tframe_inject j (f1::nil) f2)
     (RSB: record_stack_blocks m1 f1 = Some m1'),
     inject j g m1' m2;


 record_stack_blocks_inject_parallel {injperm: InjectPerm}:
   forall m1 m1' m2 j g fi1 fi2,
     inject j g m1 m2 ->
     frame_inject j fi1 fi2 ->
     (forall b : block, in_stack (stack_adt m2) b -> ~ in_frame fi2 b) ->
     (valid_frame fi2 m2) ->
     (forall b fi, In (b,fi) (frame_adt_blocks fi2) ->
              forall o k p, perm m2 b o k p -> 0 <= o < frame_size fi) ->
     (forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame fi1 b1 <-> in_frame fi2 b2) ->
     frame_adt_size fi1 = frame_adt_size fi2 ->
     record_stack_blocks m1 fi1 = Some m1' ->
     top_tframe_no_perm (perm m2) (stack_adt m2) ->
     g O = Some O ->
     exists m2',
       record_stack_blocks m2 fi2 = Some m2' /\
       inject j g m1' m2';

 record_stack_blocks_extends {injperm: InjectPerm}:
    forall m1 m2 m1' fi,
      extends m1 m2 ->
      record_stack_blocks m1 fi = Some m1' ->
      (forall b, in_frame fi b -> ~ in_stack ( (stack_adt m2)) b ) ->
      frame_agree_perms (perm m2) fi ->
      top_tframe_no_perm (perm m2) (stack_adt m2) ->
      exists m2',
        record_stack_blocks m2 fi = Some m2' /\
        extends m1' m2';

 record_stack_blocks_mem_unchanged:
   forall bfi,
     mem_unchanged (fun m1 m2 => record_stack_blocks m1 bfi = Some m2);

 record_stack_blocks_stack_adt:
   forall m fi m' f s,
     record_stack_blocks m fi = Some m' ->
     stack_adt m = f::s ->
     stack_adt m' = (fi :: f) :: s;

 record_stack_blocks_inject_neutral {injperm: InjectPerm}:
   forall thr m fi m',
     inject_neutral thr m ->
     record_stack_blocks m fi = Some m' ->
     Forall (fun b => Plt b thr) (map fst (frame_adt_blocks fi)) ->
     inject_neutral thr m';

 (* Properties of unrecord_stack_block *)

 unrecord_stack_block_inject_parallel {injperm: InjectPerm}:
   forall (m1 m1' m2 : mem) (j : meminj) g,
     inject j g m1 m2 ->
     unrecord_stack_block m1 = Some m1' ->
     (forall i j, g i = Some j -> (O < i) -> (O < j))%nat ->
     g O = Some O ->
     size_stack (tl (stack_adt m2)) <= size_stack (tl (stack_adt m1)) ->
     exists m2',
       unrecord_stack_block m2 = Some m2' /\ inject j (fun n => option_map pred (g (S n))) m1' m2';

 unrecord_stack_block_inject_left {injperm: InjectPerm}:
   forall (m1 m1' m2 : mem) (j : meminj) g,
     inject j g m1 m2 ->
     unrecord_stack_block m1 = Some m1' ->
     g 1%nat = Some O \/ g O = None->
     (forall b, is_stack_top (stack_adt m1) b -> forall o k p, ~ perm m1 b o k p) ->
     size_stack (stack_adt m2) <= size_stack (stack_adt m1') ->
     inject j (fun n => g (S n)) m1' m2;

 unrecord_stack_block_extends {injperm: InjectPerm}:
   forall m1 m2 m1',
     extends m1 m2 ->
     unrecord_stack_block m1 = Some m1' ->
     size_stack (tl (stack_adt m2)) <= size_stack (tl (stack_adt m1)) ->
     exists m2',
       unrecord_stack_block m2 = Some m2' /\
       extends m1' m2';

 unrecord_stack_block_mem_unchanged:
   mem_unchanged (fun m1 m2 => unrecord_stack_block m1 = Some m2);

 unrecord_stack_adt:
   forall m m',
     unrecord_stack_block m = Some m' ->
     exists b,
       stack_adt m = b :: stack_adt m';

 unrecord_stack_block_succeeds:
   forall m b r,
     stack_adt m = b :: r ->
     exists m',
       unrecord_stack_block m = Some m'
       /\ stack_adt m' = r;

 unrecord_stack_block_inject_neutral {injperm: InjectPerm}:
   forall thr m m',
     inject_neutral thr m ->
     unrecord_stack_block m = Some m' ->
     inject_neutral thr m';


 (* Other properties *)

 public_stack_access_extends {injperm: InjectPerm}:
   forall m1 m2 b lo hi p,
     extends m1 m2 ->
     range_perm m1 b lo hi Cur p ->
     inject_perm_condition p ->
     public_stack_access ( (stack_adt m1)) b lo hi ->
     public_stack_access ( (stack_adt m2)) b lo hi;

 public_stack_access_inject {injperm: InjectPerm}:
   forall f g m1 m2 b b' delta lo hi p,
     f b = Some (b', delta) ->
     inject f g m1 m2 ->
     range_perm m1 b lo hi Cur p ->
     inject_perm_condition p ->
     public_stack_access ( (stack_adt m1)) b lo hi ->
     public_stack_access ( (stack_adt m2)) b' (lo + delta) (hi + delta);

 public_stack_access_magree {injperm: InjectPerm}: forall P (m1 m2 : mem) (b : block) (lo hi : Z) p,
     magree m1 m2 P ->
     range_perm m1 b lo hi Cur p ->
     inject_perm_condition p ->
     public_stack_access ( (stack_adt m1)) b lo hi ->
     public_stack_access ( (stack_adt m2)) b lo hi;


 (* not_in_frames_extends {injperm: InjectPerm}: *)
 (*   forall m1 m2 b, *)
 (*     extends m1 m2 -> *)
 (*     ~ in_frames ( (stack_adt m1)) b -> *)
 (*     ~ in_frames ( (stack_adt m2)) b; *)


 (* not_in_frames_inject {injperm: InjectPerm}: *)
 (*   forall f g m1 m2 b b' delta, *)
 (*     f b = Some (b', delta) -> *)
 (*     inject f g m1 m2 -> *)
 (*     ~ in_frames ( (stack_adt m1)) b -> *)
 (*     ~ in_frames ( (stack_adt m2)) b'; *)

 in_frames_valid:
   forall m b,
     in_stack ( (stack_adt m)) b -> valid_block m b;

 is_stack_top_extends {injperm: InjectPerm}:
   forall m1 m2 b
     (MINJ: extends m1 m2)
     (PERM: exists (o : Z) (k : perm_kind) (p : permission),
         perm m1 b o k p /\ inject_perm_condition p)
     (IST: is_stack_top ( (stack_adt m1)) b),
     is_stack_top ( (stack_adt m2)) b ;

 is_stack_top_inject {injperm: InjectPerm}:
   forall f g m1 m2 b1 b2 delta
     (MINJ: inject f g m1 m2)
     (FB: f b1 = Some (b2, delta))
     (PERM: exists (o : Z) (k : perm_kind) (p : permission),
         perm m1 b1 o k p /\ inject_perm_condition p)
     (IST: is_stack_top ( (stack_adt m1)) b1),
     is_stack_top ( (stack_adt m2)) b2 ;

 stack_limit_range:
   0 <= stack_limit <= Ptrofs.max_unsigned;
 stack_limit_aligned:
   (8 | stack_limit);
 size_stack_below:
   forall m, size_stack (stack_adt m) < stack_limit;

 
 record_stack_block_inject_left_zero {injperm: InjectPerm}:
    forall m1 m1' m2 j g f1 f2
      (INJ: inject j g m1 m2)
      (FAP2: frame_at_pos (stack_adt m2) O f2)
      (FI: tframe_inject j (f1::nil) f2)
      (SZ2: Forall (fun f => Forall (fun f =>0 = frame_adt_size f) f)%Z (stack_adt m2)) 
      (RSB: record_stack_blocks (push_new_stage m1) f1 = Some m1'),
      inject j (fun n : nat => if Nat.eq_dec n O then Some O else g (pred n)) m1' m2;

 unrecord_stack_block_inject_left_zero {injperm: InjectPerm}:
    forall (m1 m1' m2 : mem) (j : meminj) g,
      inject j g m1 m2 ->
      unrecord_stack_block m1 = Some m1' ->
      (forall i j, g i = Some j -> j = O) ->
      (forall b, is_stack_top (stack_adt m1) b -> forall o k p, ~ perm m1 b o k p) ->
      g 1%nat = Some O ->
      size_stack (stack_adt m2) <= size_stack (stack_adt m1') ->
      inject j (fun n => g (S n)) m1' m2;


 mem_inject_ext {injperm: InjectPerm}:
   forall j g1 g2 m1 m2,
     inject j g1 m1 m2 ->
     (forall x, g1 x = g2 x) ->
     inject j g2 m1 m2;

 record_stack_blocks_intro:
    forall m1 f,
      valid_frame f m1 ->
      Forall (fun b => ~ in_stack (stack_adt m1) b) (map fst (frame_adt_blocks f)) ->
      Forall
        (fun bfi : block * frame_info =>
           forall (o : Z) (k : perm_kind) (p : permission),
             perm m1 (fst bfi) o k p -> (0 <= o < frame_size (snd bfi))%Z) 
        (frame_adt_blocks f) ->
      (size_stack (stack_adt m1) + align (frame_adt_size f) 8 < stack_limit)%Z ->
      top_tframe_no_perm (perm m1) (stack_adt m1) ->
      exists m2,
        record_stack_blocks m1 f = Some m2;

 extends_same_length_stack:
   forall {injperm: InjectPerm} m1 m2,
     extends m1 m2 ->
     length (stack_adt m2) = length (stack_adt m1);

 stack_norepet:
   forall m, nodup (stack_adt m);

 inject_ext {injperm: InjectPerm}:
    forall j1 j2 g m1 m2,
      inject j1 g m1 m2 ->
      (forall x, j1 x = j2 x) ->
      inject j2 g m1 m2;
unrecord_stack_block_inject_right {injperm: InjectPerm}:
    forall j g m1 m2 m2'
      (MI: inject j g m1 m2)
      (TOPNOPERM: forall b, is_stack_top (stack_adt m1) b -> ~ exists o k p, perm m1 b o k p)
      (NO0: forall i j, g i = Some j -> (O < i -> O < j)%nat)
      (Ginit: (g O = Some O)%nat)
      (USB: unrecord_stack_block m2 = Some m2'),
      inject j (fun n => if Nat.eq_dec n O then None else option_map pred (g n)) m1 m2';

stack_inject_unrecord_parallel_frameinj_flat {injperm: InjectPerm}:
  forall j m1 m2
    (MI: inject j (flat_frameinj (length (stack_adt m2))) m1 m2)
    (LEN: length (stack_adt m1) = length (stack_adt m2))
    (* fr2 l2 *)
    (* (STK2 : stack_adt m2 = fr2 :: l2) *)
    (* fr1 l1 *)
    (* (STK1 : stack_adt m1 = fr1 :: l1) *)
    m1'
    (USB: unrecord_stack_block m1 = Some m1')
    (SZ: size_stack (tl (stack_adt m2)) <= size_stack (tl (stack_adt m1))),
  exists m2',
    unrecord_stack_block m2 = Some m2' /\ 
    inject j (flat_frameinj (pred (length (stack_adt m2)))) m1' m2';

record_stack_block_inject_flat {injperm: InjectPerm}:
   forall m1 m1' m2 j  f1 f2
     (INJ: inject j (flat_frameinj (length (stack_adt m1))) m1 m2)
     (FI: frame_inject j f1 f2)
     (NOIN: forall b, in_stack (stack_adt m2) b -> ~ in_frame f2 b)
     (VF: valid_frame f2 m2)
     (BOUNDS: forall b fi,
         In (b,fi) (frame_adt_blocks f2) ->
         forall (o : Z) (k : perm_kind) (p : permission), perm m2 b o k p -> (0 <= o < frame_size fi)%Z)
     (EQINF: forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame f1 b1 <-> in_frame f2 b2)
     (EQsz: frame_adt_size f1 = frame_adt_size f2)
     (RSB: record_stack_blocks m1 f1 = Some m1')
     (TNF: top_tframe_no_perm (perm m2) (stack_adt m2)),
     exists m2',
       record_stack_blocks m2 f2 = Some m2' /\
       inject j (flat_frameinj (length (stack_adt m1'))) m1' m2' /\
       (length (stack_adt m1) = length (stack_adt m2) ->
        length (stack_adt m1') = length (stack_adt m2'));

unrecord_stack_block_inject_parallel_flat {injperm: InjectPerm}:
  forall (m1 m1' m2 : mem) (j : meminj),
    inject j (flat_frameinj (length (stack_adt m1))) m1 m2 ->
    unrecord_stack_block m1 = Some m1' ->
    size_stack (tl (stack_adt m2)) <= size_stack (tl (stack_adt m1)) ->
    exists m2',
      unrecord_stack_block m2 = Some m2' /\
      inject j (flat_frameinj (length (stack_adt m1'))) m1' m2' /\
      (length (stack_adt m1) = length (stack_adt m2) ->
       length (stack_adt m1') = length (stack_adt m2'));

(* mem_inject_tailcall_inlined {injperm: InjectPerm}: *)
(*     forall F g m m'0 stk szstk *)
(*       (INJ: inject F g m m'0) *)
(*       m' (FREE: free m stk 0 szstk = Some m')  *)
(*       (* m'' (USB: unrecord_stack_block m' = Some m'' ) *) *)
(*       m'1 stk0 szstk0 (ALLOC: alloc m' 0 szstk0 = (m'1, stk0)) *)
(*       stkreq m''0 (RSB: record_stack_blocks m'1 (make_singleton_frame_adt stk0 szstk0 stkreq) = Some m''0) *)
(*       sp' delta (Fstk: F stk = Some (sp', delta)) *)
(*       delta0 *)
(*       (LE: (delta <= delta0)%Z) *)
(*       (PERMinjstk0: forall o, (0 <= o < szstk0)%Z -> perm m'0 sp' (o + delta0) Cur Freeable) *)
(*       (DIV: inj_offset_aligned delta0 szstk0) *)
(*       (G0 : g O = Some O) *)
(*       vf1 f1 s1 *)
(*       (STKeq: stack_adt m = f1::s1) *)
(*       (FrameSTK: nth_error f1 O = Some vf1) *)
(*       (STACKTOP: get_frame_blocks vf1 = stk::nil) *)
(*       (PERMstk: forall o k p, perm m stk o k p -> (0 <= o < szstk)%Z) *)
(*       sz1 sz2 *)
(*       (STACKTOP':  exists r rt, stack_adt m'0 = (make_singleton_frame_adt sp' sz1 sz2 :: rt) :: r) *)
(*       (RNG: forall o : Z, (0 <= o < szstk0)%Z -> (0 <= o + delta0 < sz1)%Z) *)
(*       (JBstack: forall b, in_stack (stack_adt m) b -> exists b' delta, F b = Some (b', delta)) *)
(*       (* (SIZE: (sz2 <= stkreq)%Z) *) *)
(*       (PERMsp': forall b d o p, *)
(*           F b = Some (sp', d) -> b <> stk -> *)
(*           perm m b o Max p -> *)
(*           (o + d < delta)%Z) *)
(*       (REPR: (0 <= Z.max szstk0 0 + delta0 <= Ptrofs.max_unsigned)%Z) *)
(*     , *)
(*       let F' := fun b => if peq b stk0 then Some (sp', delta0) else F b in *)
(*       inject F' g m''0 m'0; *)


record_stack_blocks_tailcall_original_stack:
  forall m1 f1 m2,
    record_stack_blocks m1 f1 = Some m2 ->
    exists f r,
      stack_adt m1 = f::r;

push_new_stage_nextblock: forall m, nextblock (push_new_stage m) = nextblock m;
 push_new_stage_load: forall chunk m b o, load chunk (push_new_stage m) b o = load chunk m b o;

 push_new_stage_inject  {injperm: InjectPerm}:
   forall j g m1 m2,
        inject j g m1 m2 ->
        inject j (fun n => if Nat.eq_dec n O then Some O else option_map S (g (pred n)))
               (push_new_stage m1) (push_new_stage m2);

 inject_push_new_stage_left {injperm: InjectPerm}:
   forall j g m1 m2,
     inject j g m1 m2 ->
     stack_adt m2 <> nil ->
     inject j (upstar g) (push_new_stage m1) m2;


 push_new_stage_length_stack:
      forall m,
        length (stack_adt (push_new_stage m)) = S (length (stack_adt m));
 push_new_stage_stack:
      forall m,
        stack_adt (push_new_stage m) = nil :: stack_adt m;


 inject_stack_size {injperm: InjectPerm}:
      forall j g m1 m2,
        inject j g m1 m2 ->
        size_stack (stack_adt m2) <= size_stack (stack_adt m1);

    

 push_new_stage_perm:
      forall m b o k p,
        perm (push_new_stage m) b o k p <-> perm m b o k p;

wf_stack_mem:
  forall j m,
    wf_stack (Mem.perm m) j (Mem.stack_adt m);

 agree_perms_mem:
  forall m,
    stack_agree_perms (Mem.perm m) (Mem.stack_adt m);

 record_stack_blocks_top_tframe_no_perm:
   forall m1 f m2,
     Mem.record_stack_blocks m1 f = Some m2 ->
     Mem.top_tframe_no_perm (Mem.perm m1) (Mem.stack_adt m1);


}.

Section WITHMEMORYMODEL.

Context `{memory_model_prf: MemoryModel}.

Lemma stack_top_valid:
  forall m b, is_stack_top (stack_adt m) b -> valid_block m b.
Proof.
  intros. rewrite is_stack_top_stack_blocks in H.
  decompose [ex and] H.
  eapply in_frames_valid. rewrite H2, in_stack_cons; auto.
Qed.

Lemma get_frame_info_valid:
  forall m b f, get_frame_info (stack_adt m) b = Some f -> valid_block m b.
Proof.
  intros. eapply in_frames_valid. eapply get_frame_info_in_stack; eauto.
Qed.

Lemma invalid_block_stack_access:
  forall m b lo hi,
    ~ valid_block m b ->
    stack_access (stack_adt m) b lo hi.
Proof.
  right.
  red.
  rewrite not_in_stack_get_assoc. auto.
  intro IN; apply in_frames_valid in IN; congruence.
Qed.

Lemma store_get_frame_info:
  forall chunk m1 b o v m2 (STORE: store chunk m1 b o v = Some m2),
  forall b', get_frame_info (stack_adt m2) b' = get_frame_info (stack_adt m1) b'.
Proof.
  intros. 
  erewrite store_no_abstract; eauto.
Qed.

Lemma store_stack_blocks:
  forall m1 sp chunk o v m2,
    store chunk m1 sp o v = Some m2 ->
    stack_adt m2 = stack_adt m1.
Proof.
  intros. 
  eapply store_no_abstract; eauto.
Qed.

Lemma store_is_stack_top:
   forall chunk m1 b o v m2 (STORE: store chunk m1 b o v = Some m2),
   forall b', is_stack_top (stack_adt m2) b' <-> is_stack_top (stack_adt m1) b'.
Proof.
  intros; erewrite store_no_abstract; eauto. tauto.
Qed.

Lemma storebytes_get_frame_info:
   forall m1 b o v m2 (STOREBYTES: storebytes m1 b o v = Some m2),
   forall b', get_frame_info (stack_adt m2) b' = get_frame_info (stack_adt m1) b'.
Proof.
  intros; erewrite storebytes_no_abstract; eauto.
Qed.

Lemma storebytes_is_stack_top:
  forall m1 b o v m2 (STOREBYTES: storebytes m1 b o v = Some m2),
  forall b', is_stack_top (stack_adt m2) b' <-> is_stack_top (stack_adt m1) b'.
Proof.
  intros; erewrite storebytes_no_abstract; eauto. tauto.
Qed.

Lemma alloc_get_frame_info:
  forall m1 lo hi m2 b (ALLOC: alloc m1 lo hi = (m2, b)),
  forall b', get_frame_info (stack_adt m2) b' = get_frame_info (stack_adt m1) b'.
Proof.
  intros; erewrite alloc_no_abstract; eauto.
Qed.

Lemma alloc_is_stack_top:
  forall m1 lo hi m2 b (ALLOC: alloc m1 lo hi = (m2, b)),
  forall b', is_stack_top (stack_adt m2) b' <-> is_stack_top (stack_adt m1) b'.
Proof.
  intros; erewrite alloc_no_abstract; eauto. tauto.
Qed.

Lemma alloc_get_frame_info_fresh:
  forall m1 lo hi m2 b (ALLOC: alloc m1 lo hi = (m2, b)),
    get_frame_info (stack_adt m2) b = None.
Proof.
  intros; eapply not_in_stack_get_assoc; auto.
  rewrite alloc_no_abstract; eauto.
  intro IN; apply in_frames_valid in IN.
  eapply fresh_block_alloc in IN; eauto.
Qed.

Lemma alloc_stack_blocks:
  forall m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) ->
    stack_adt m2 = stack_adt m1.
Proof. intros; eapply alloc_no_abstract; eauto. Qed.

Lemma free_stack_blocks:
  forall m1 b lo hi m2,
    free m1 b lo hi = Some m2 ->
    stack_adt m2 = stack_adt m1.
Proof. intros; eapply free_no_abstract; eauto. Qed.

Lemma free_get_frame_info:
  forall m1 b lo hi m2 b',
    free m1 b lo hi = Some m2 ->
    get_frame_info (stack_adt m2) b' = get_frame_info (stack_adt m1) b'.
Proof.
  intros; erewrite free_no_abstract; eauto.
Qed.

Lemma storebytes_stack_blocks:
  forall m1 b o bytes m2,
    storebytes m1 b o bytes = Some m2 ->
    stack_adt m2 = stack_adt m1.
Proof.
  intros; eapply storebytes_no_abstract; eauto.
Qed.

Lemma free_list_stack_blocks:
  forall m bl m',
    free_list m bl = Some m' ->
    stack_adt m' = stack_adt m.
Proof.
  intros; eapply freelist_no_abstract; eauto.
Qed.

Lemma record_stack_block_unchanged_on:
  forall m bfi m' (P: block -> Z -> Prop),
    record_stack_blocks m bfi = Some m' ->
    strong_unchanged_on P m m'.
Proof.
  intros; eapply record_stack_blocks_mem_unchanged; eauto.
Qed.

Lemma record_stack_block_perm:
  forall m bfi m',
    record_stack_blocks m bfi = Some m' ->
    forall b' o k p,
      perm m' b' o k p ->
      perm m b' o k p.
Proof.
  intros. eapply record_stack_blocks_mem_unchanged in H; eauto.
  apply H; eauto.
Qed.

Lemma record_stack_block_perm'
  : forall m m' bofi,
    record_stack_blocks m bofi = Some m' ->
    forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
      perm m b' o k p -> perm m' b' o k p.
Proof.
  intros. eapply record_stack_blocks_mem_unchanged in H; eauto.
  apply H; eauto.
Qed.

Lemma record_stack_block_valid:
  forall m bf m',
    record_stack_blocks m bf = Some m' ->
    forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; intros.
  eapply record_stack_blocks_mem_unchanged in H; eauto.
  destruct H. rewrite H. auto.
Qed.

Lemma record_stack_block_nextblock:
  forall m bf m',
    record_stack_blocks m bf = Some m' ->
    nextblock m' = nextblock m.
Proof.
  intros.
  eapply record_stack_blocks_mem_unchanged in H; eauto.
  intuition.
Qed.

Lemma record_stack_block_is_stack_top:
  forall m b fi m',
    record_stack_blocks m fi = Some m' ->
    in_frame fi b ->
    is_stack_top (stack_adt m') b.
Proof.
  unfold is_stack_top, get_stack_top_blocks.
  intros.
  edestruct (record_stack_blocks_tailcall_original_stack _ _ _ H) as (f & r & EQ).
  erewrite record_stack_blocks_stack_adt; eauto.
  unfold get_frames_blocks. simpl.
  rewrite in_app; left. auto.
Qed.

Lemma unrecord_stack_block_unchanged_on:
  forall m m' P,
    unrecord_stack_block m = Some m' ->
    strong_unchanged_on P m m'.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition.
Qed.

Lemma unrecord_stack_block_perm:
   forall m m',
     unrecord_stack_block m = Some m' ->
     forall b' o k p,
       perm m' b' o k p ->
       perm m b' o k p.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition. apply H; auto.
Qed.

Lemma unrecord_stack_block_perm'
     : forall m m' : mem,
       unrecord_stack_block m = Some m' ->
       forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
       perm m b' o k p -> perm m' b' o k p.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition. apply H; auto.
Qed.

Lemma unrecord_stack_block_nextblock:
  forall m m',
    unrecord_stack_block m = Some m' ->
    nextblock m' = nextblock m.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition.
Qed.

Lemma unrecord_stack_block_get_frame_info:
   forall m m' b,
     unrecord_stack_block m = Some m' ->
     ~ is_stack_top (stack_adt m) b ->
     get_frame_info (stack_adt m') b = get_frame_info (stack_adt m) b.
Proof.
  unfold is_stack_top, get_stack_top_blocks, get_frame_info. intros.
  exploit unrecord_stack_adt. eauto. intros (b0 & EQ).
  rewrite EQ in *. simpl.
  destr.
Qed.

Lemma valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros m1 chunk b ofs v H.
  destruct (store _ _ _ _ _) eqn:STORE; eauto.
  exfalso.
  eapply @valid_access_store' with (v := v) in H; eauto.
  destruct H.
  congruence.
Defined.

Lemma range_perm_storebytes:
  forall m1 b ofs bytes,
    range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
    stack_access (stack_adt m1) b ofs (ofs + Z_of_nat (length bytes)) ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Proof.
  intros m1 b ofs bytes H NPSA.
  destruct (storebytes _ _ _ _) eqn:STOREBYTES; eauto.
  exfalso.
  apply range_perm_storebytes' in H.
  destruct H.
  congruence.
  apply NPSA.
Defined.

Lemma range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros m1 b lo hi H.
  destruct (free _ _ _ _) eqn:FREE; eauto.
  exfalso.
  apply range_perm_free' in H.
  destruct H.
  congruence.
Defined.

Lemma range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> { m' | drop_perm m b lo hi p = Some m' }.
Proof.
  intros m b lo hi p H.
  destruct (drop_perm _ _ _ _ _) eqn:DROP; eauto.
  exfalso.
  eapply @range_perm_drop_2' with (p := p) in H; eauto.
  destruct H.
  congruence.
Defined.

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
  split. eapply perm_free_3; eauto.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

Lemma unchanged_on_refl:
  forall P m, unchanged_on P m m.
Proof.
  intros. apply strong_unchanged_on_weak. apply strong_unchanged_on_refl.
Qed.

Lemma store_unchanged_on:
  forall P chunk m b ofs v m',
    store chunk m b ofs v = Some m' ->
    (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
    unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply store_strong_unchanged_on; eauto.
Qed.

Lemma storebytes_unchanged_on:
  forall P m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply storebytes_strong_unchanged_on; eauto.
Qed.

Lemma alloc_unchanged_on:
   forall P m lo hi m' b,
     alloc m lo hi = (m', b) ->
     unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply alloc_strong_unchanged_on; eauto.
Qed.

Lemma free_unchanged_on:
  forall P m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply free_strong_unchanged_on; eauto.
Qed.

Lemma drop_perm_unchanged_on:
   forall P m b lo hi p m',
     drop_perm m b lo hi p = Some m' ->
     (forall i, lo <= i < hi -> ~ P b i) ->
     unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply drop_perm_strong_unchanged_on; eauto.
Qed.

Lemma perm_free m b lo hi m':
  free m b lo hi = Some m' ->
  forall b' o' k p,
    perm m' b' o' k p <->
    ((~ (b' = b /\ lo <= o' < hi)) /\ perm m b' o' k p).
Proof.
  intros H b' o' k p.
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

Lemma store_stack_access:
  forall chunk m b o v m1 ,
    store chunk m b o v = Some m1 ->
    forall b' lo hi,
      stack_access (stack_adt m1) b' lo hi <-> stack_access (stack_adt m) b' lo hi.
Proof.
  intros; erewrite store_no_abstract; eauto. tauto.
Qed.


Context {injperm: InjectPerm}.

Lemma frameinj_order_strict_0:
  forall g j m1 m2,
    inject j g m1 m2 ->
    frameinj_order_strict g ->
    g O = Some O ->
    forall i j0 : nat, g i = Some j0 -> (0 < i)%nat -> (0 < j0)%nat.
Proof.
  intros. eapply inject_stack_adt in H.
  eapply H0; eauto.
Qed.

Lemma frameinj_order_strict_pop:
  forall g j m1 m2,
    inject j g m1 m2 ->
    g O = Some O ->
    frameinj_order_strict g ->
    frameinj_order_strict (fun n : nat => option_map Init.Nat.pred (g (Datatypes.S n))).
Proof.
  red; intros g j m1 m2 INJ GO. intros.
  unfold option_map in H1, H2.
  destr_in H1; destr_in H2. inv H1; inv H2.
  exploit H. 2: exact Heqo. 2: exact Heqo0. omega. intros.
  exploit stack_inject_pack. apply inject_stack_adt. eauto. apply Heqo.
  exploit stack_inject_pack. apply inject_stack_adt. eauto. apply Heqo0.
  eapply frameinj_order_strict_0 in Heqo; eauto. omega. omega.
Qed.

Lemma unrecord_stack_block_inject_parallel_strict:
   forall (m1 m1' m2 : mem) (j : meminj) g,
     inject j g m1 m2 ->
     frameinj_order_strict g ->
     unrecord_stack_block m1 = Some m1' ->
     g O = Some O ->
     size_stack (tl (stack_adt m2)) <= size_stack (tl (stack_adt m1)) ->
     exists m2',
       unrecord_stack_block m2 = Some m2'
       /\ inject j (fun n => option_map pred (g (S n))) m1' m2'
       /\ frameinj_order_strict (fun n => option_map pred (g (S n))).
Proof.
  intros.
  generalize (frameinj_order_strict_0 _ _ _ _ H H0 H2). intros.
  generalize (frameinj_order_strict_pop _ _ _ _ H H2 H0). intros.
  exploit unrecord_stack_block_inject_parallel; eauto.
  intros (m2' & USB & INJ); eauto.
Qed.

Lemma storev_nextblock :
  forall m chunk addr v m',
    storev chunk m addr v = Some m' ->
    nextblock m' = nextblock m.
Proof.
  intros; destruct addr; simpl in *; try congruence.
  eapply nextblock_store; eauto.
Qed.

Lemma storev_stack_adt :
  forall m chunk addr v m',
    storev chunk m addr v = Some m' ->
    stack_adt m' = stack_adt m.
Proof.
  intros; destruct addr; simpl in *; try congruence.
  eapply store_stack_blocks; eauto.
Qed.

Lemma storev_perm_inv:
  forall m chunk addr v m',
    storev chunk m addr v = Some m' ->
    forall b o k p,
      perm m' b o k p ->
      perm m b o k p.
Proof.
  intros; destruct addr; simpl in *; try congruence.
  eapply perm_store_2; eauto.
Qed.

(* Lemma frameinj_surjective_free_list_unrecord: *)
(*   forall g j m P tm tm' tm'' l, *)
(*     free_list tm l = Some tm' -> *)
(*     unrecord_stack_block tm' = Some tm'' -> *)
(*     stack_inject j g P (stack_adt m) (stack_adt tm) -> *)
(*     frameinj_surjective g (length (stack_adt tm)) -> *)
(*     frameinj_surjective (fun n : nat => option_map Init.Nat.pred (g (Datatypes.S n))) *)
(*                         (length (stack_adt tm'')). *)
(* Proof. *)
(*   intros g j m P tm tm' tm'' l FL USB SI SURJ. *)
(*   intros. erewrite <- free_list_stack_blocks in SURJ by eauto. *)
(*   edestruct unrecord_stack_adt as (x & EQ). eauto. rewrite EQ in SURJ. *)
(*   red; intros. *)
(*   destruct (SURJ (S j0)) as (? & G). *)
(*   simpl; omega. *)
(*   destruct (Nat.eq_dec x0 O). subst. *)
(*   { *)
(*     erewrite stack_inject_g0_0 in G. inv G. eauto. eapply stack_inject_range in G; eauto. tauto. *)
(*     eapply stack_inject_range in G; eauto. omega. *)
(*   } *)
(*   exists (pred x0). *)
(*   replace (S (pred x0)) with x0 by omega. rewrite G. simpl. auto. *)
(* Qed. *)


(* Lemma frameinj_surjective_free_unrecord: *)
(*   forall g j m P tm tm' tm'' b lo hi, *)
(*     free tm b lo hi = Some tm' -> *)
(*     unrecord_stack_block tm' = Some tm'' -> *)
(*     stack_inject j g P (stack_adt m) (stack_adt tm) -> *)
(*     frameinj_surjective g (length (stack_adt tm)) -> *)
(*     frameinj_surjective (fun n : nat => option_map Init.Nat.pred (g (Datatypes.S n))) *)
(*                         (length (stack_adt tm'')). *)
(* Proof. *)
(*   intros g j m P tm tm' tm'' b lo hi FL USB SI SURJ. *)
(*   intros. erewrite <- free_stack_blocks in SURJ by eauto. *)
(*   edestruct unrecord_stack_adt as (x & EQ). eauto. rewrite EQ in SURJ. *)
(*   red; intros. *)
(*   destruct (SURJ (S j0)) as (? & G). *)
(*   simpl; omega. *)
(*   destruct (Nat.eq_dec x0 O). subst. *)
(*   { *)
(*     erewrite stack_inject_g0_0 in G. inv G. eauto. eapply stack_inject_range in G; eauto. tauto. *)
(*     eapply stack_inject_range in G; eauto. omega. *)
(*   } *)
(*   exists (pred x0). *)
(*   replace (S (pred x0)) with x0 by omega. rewrite G. simpl. auto.   *)
(* Qed. *)


Lemma frame_inject_flat:
  forall thr f,
    Forall (fun bfi => Plt (fst bfi) thr) (frame_adt_blocks f) ->
    frame_inject (flat_inj thr) f f.
Proof.
  red; intros thr f PLT.
  eapply Forall_impl. 2: eauto. simpl; intros a IN PLTa b2 delta FI.
  unfold flat_inj in FI. destr_in FI. inv FI.
  erewrite in_lnr_get_assoc.
  instantiate (1 := snd a). eexists; split; eauto.
  destruct f; auto.
  rewrite <- surjective_pairing. auto.
Qed.


Lemma noperm_top:
  forall m,
    match Mem.stack_adt m with
      (f::_)::_ => forall b, in_frame f b -> forall o k p, ~ Mem.perm m b o k p
    | _ => False
    end ->
    Mem.top_tframe_no_perm (Mem.perm m) (Mem.stack_adt m).
Proof.
  intros.
  repeat destr_in H.
  constructor.
  red; intros.
  rewrite in_frames_cons in H1. destruct H1; eauto.
  generalize (wf_stack_mem inject_id m); rewrite Heqs. inversion 1. subst.
  eapply H5. congruence. simpl; assumption.
Qed.

Lemma record_push_inject:
  forall j g m1 m2 (MINJ: Mem.inject j g m1 m2)
    fi1 fi2 (FI: Mem.frame_inject j fi1 fi2)
    (NINSTACK: forall b, in_stack (Mem.stack_adt m2) b -> in_frame fi2 b -> False)
    (VALID: Mem.valid_frame fi2 m2)
    (FAP2: frame_agree_perms (Mem.perm m2) fi2)
    (INF: forall b1 b2 delta, j b1 = Some (b2, delta) -> in_frame fi1 b1 <-> in_frame fi2 b2)
    (SZ: frame_adt_size fi1 = frame_adt_size fi2)
    (tc: bool)
    m1'
    (RSB: Mem.record_stack_blocks (if tc then m1 else Mem.push_new_stage m1) fi1 = Some m1')
    (TTNP: tc = true -> Mem.top_tframe_no_perm (Mem.perm m2) (Mem.stack_adt m2))
    newframeinj
    (NFI: forall b, newframeinj b = (if tc then g else up g) b)
    (NFI0: newframeinj O = Some O),
  exists m2', Mem.record_stack_blocks (if tc then m2 else Mem.push_new_stage m2) fi2 = Some m2' /\ Mem.inject j newframeinj m1' m2'.
Proof.
  intros.
  destruct tc.
  - subst.
    eapply Mem.record_stack_blocks_inject_parallel.
    eapply Mem.mem_inject_ext. eauto. eauto. all: eauto.
  - eapply Mem.record_stack_blocks_inject_parallel.
    eapply Mem.mem_inject_ext. 
    apply Mem.push_new_stage_inject. eauto. all: eauto.
    + rewrite Mem.push_new_stage_stack. setoid_rewrite in_stack_cons. intros b [[]|INS]. eauto.
    + red; red; intros; rewrite Mem.push_new_stage_nextblock; eauto. apply VALID; auto.
    + setoid_rewrite Mem.push_new_stage_perm. eauto.
    + rewrite Mem.push_new_stage_stack. constructor. red. easy.
Qed.

Lemma record_stack_blocks_length_stack:
  forall m1 f m2,
    Mem.record_stack_blocks m1 f = Some m2 ->
    length (Mem.stack_adt m2) = length (Mem.stack_adt m1).
Proof.
  intros.
  edestruct Mem.record_stack_blocks_tailcall_original_stack as (ff & r & eq); eauto. rewrite eq.
  eapply Mem.record_stack_blocks_stack_adt in eq; eauto. rewrite eq. reflexivity.
Qed.

Lemma record_stack_blocks_stack_eq:
  forall m1 f m2,
    Mem.record_stack_blocks m1 f = Some m2 ->
    exists tf r,
      Mem.stack_adt m1 = tf::r /\ Mem.stack_adt m2 = (f::tf)::r.
Proof.
  intros.
  edestruct Mem.record_stack_blocks_tailcall_original_stack as (ff & r & eq); eauto. rewrite eq.
  eapply Mem.record_stack_blocks_stack_adt in eq; eauto.
Qed.

Lemma record_push_inject_flat:
  forall j m1 m2 (MINJ: Mem.inject j (flat_frameinj (length (Mem.stack_adt m1))) m1 m2)
    fi1 fi2 (FI: Mem.frame_inject j fi1 fi2)
    (NINSTACK: forall b, in_stack (Mem.stack_adt m2) b -> in_frame fi2 b -> False)
    (VALID: Mem.valid_frame fi2 m2)
    (FAP2: frame_agree_perms (Mem.perm m2) fi2)
    (INF: forall b1 b2 delta, j b1 = Some (b2, delta) -> in_frame fi1 b1 <-> in_frame fi2 b2)
    (SZ: frame_adt_size fi1 = frame_adt_size fi2)
    (tc: bool)
    m1'
    (RSB: Mem.record_stack_blocks (if tc then m1 else Mem.push_new_stage m1) fi1 = Some m1')
    (TTNP: tc = true -> Mem.top_tframe_no_perm (Mem.perm m2) (Mem.stack_adt m2)),
  exists m2', Mem.record_stack_blocks (if tc then m2 else Mem.push_new_stage m2) fi2 = Some m2' /\
         Mem.inject j (flat_frameinj (length (Mem.stack_adt m1'))) m1' m2'.
Proof.
  intros.
  eapply record_push_inject; eauto.
  - intros.
    rewrite (record_stack_blocks_length_stack _ _ _ RSB).
    destr.
    rewrite <- up_flatinj.
    rewrite Mem.push_new_stage_stack. reflexivity.
  - rewrite (record_stack_blocks_length_stack _ _ _ RSB).
    destr.
    apply record_stack_blocks_top_tframe_no_perm in RSB. inv RSB. reflexivity.
    rewrite Mem.push_new_stage_stack; reflexivity.
Qed.


End WITHMEMORYMODEL.

End Mem.
