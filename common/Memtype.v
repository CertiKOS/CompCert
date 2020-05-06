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

Module Type MEM.

(*X* The abstract type of memory states. *)
Parameter mem: Type.

(** * Operations on memory states *)

(*X* [empty] is the initial memory state. *)
Parameter empty: mem.

(*X* [alloc m lo hi] allocates a fresh block of size [hi - lo] bytes.
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
Parameter alloc: forall (m: mem) (lo hi: Z), mem * block.

(*X* [free m b lo hi] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b].  Returns the updated memory
  state, or [None] if the freed addresses are not writable. *)
Parameter free: forall (m: mem) (b: block) (lo hi: Z), option mem.

(*X* [load chunk m b ofs] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the value read, or [None] if the accessed addresses
  are not readable. *)
Parameter load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z), option val.

(*X* [store chunk m b ofs v] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable. *)
Parameter store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val), option mem.

(*X* [loadv] and [storev] are variants of [load] and [store] where
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

(*X* [loadbytes m b ofs n] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable. *)
Parameter loadbytes: forall (m: mem) (b: block) (ofs n: Z), option (list memval).

(*X* [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)
Parameter storebytes: forall (m: mem) (b: block) (ofs: Z) (bytes: list memval), option mem.

(*X* [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(*X* [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Parameter drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission), option mem.

(** * Permissions, block validity, access validity, and bounds *)

(*X* The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

Parameter nextblock: mem -> block.

(*X*)

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

(*X*)

Axiom valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.

(*X* [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
Parameter perm: forall (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission), Prop.

(*X* Logical implications between permissions *)

Axiom perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.

(*X* The current permission is always less than or equal to the maximal permission. *)

Axiom perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Axiom perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Axiom perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.

(*X* Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
Axiom perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.

(*X* [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

(*X*)
Axiom range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.

(*X* An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs).

(*X*)
Axiom valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.

(*X*)
Axiom valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.

(*X*)
Axiom valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p.

(*X* [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

Parameter valid_pointer: forall (m: mem) (b: block) (ofs: Z), bool.

(*X*)

Axiom valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.

(*X*)

Axiom valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.

(*X* C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

(*X*)
Axiom weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.

(*X*)
Axiom valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.

(** * Properties of the memory operations *)

(*X* ** Properties of the initial memory state. *)

Axiom nextblock_empty: nextblock empty = 1%positive.
Axiom perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Axiom valid_access_empty:
  forall chunk b ofs p, ~valid_access empty chunk b ofs p.

(** ** Properties of [load]. *)

(*X* A load succeeds if and only if the access is valid for reading *)
Axiom valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Axiom load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.

(*X* The value returned by [load] belongs to the type of the memory quantity
  accessed: [Vundef], [Vint] or [Vptr] for an integer quantity,
  [Vundef] or [Vfloat] for a float quantity. *)
Axiom load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).

(*X* For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
Axiom load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.

(*X*)
Axiom load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).

(*X*)
Axiom load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).


(** ** Properties of [loadbytes]. *)

(*X* [loadbytes] succeeds if and only if we have read permissions on the accessed
    memory area. *)

Axiom range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes.
(*X*)
Axiom loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.

(*X* If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
Axiom loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes).

(*X* Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
Axiom load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.

(*X* [loadbytes] returns a list of length [n] (the number of bytes read). *)
Axiom loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n.

(*X*)
Axiom loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil.

(*X* Composing or decomposing [loadbytes] operations at adjacent addresses. *)
Axiom loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
(*X*)
Axiom loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.

(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [store] succeeds if and only if the corresponding access
  is valid for writing. *)
(*X*)
Axiom nextblock_store:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  nextblock m2 = nextblock m1.
(*X*)
Axiom store_valid_block_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
(*X*)
Axiom store_valid_block_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b'.

(*X*)
Axiom perm_store_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
(*X*)
Axiom perm_store_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.

(*X*)
Axiom valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
(*X*)
Axiom store_valid_access_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
(*X*)
Axiom store_valid_access_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
(*X*)
Axiom store_valid_access_3:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  valid_access m1 chunk b ofs Writable.

(** Load-store properties. *)

(*X*)
Axiom load_store_similar:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.

(*X*)
Axiom load_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  load chunk m2 b ofs = Some (Val.load_result chunk v).

(*X*)
Axiom load_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.

(*X* Integrity of pointer values. *)

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

(*X*)
Axiom load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
(*X*)
Axiom load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef.
(*X*)
Axiom load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').

(*X* Load-store properties for [loadbytes]. *)

Axiom loadbytes_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
(*X*)
Axiom loadbytes_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' n,
  b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

(*X*)
Axiom store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
(*X*)
Axiom store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
(*X*)
Axiom store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
(*X*)
Axiom store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
(*X*)
Axiom store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
(*X*)
Axiom store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).

(** ** Properties of [storebytes]. *)

(** [storebytes] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [storebytes] succeeds if and only if we have write permissions
  on the addressed memory area. *)

(*X*)
Axiom range_perm_storebytes:
  forall m1 b ofs bytes,
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
  exists m2, storebytes m1 b ofs bytes = Some m2.
(*X*)
Axiom storebytes_range_perm:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable.
(*X*)
Axiom perm_storebytes_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
(*X*)
Axiom perm_storebytes_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
(*X*)
Axiom storebytes_valid_access_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
(*X*)
Axiom storebytes_valid_access_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
(*X*)
Axiom nextblock_storebytes:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  nextblock m2 = nextblock m1.
(*X*)
Axiom storebytes_valid_block_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
(*X*)
Axiom storebytes_valid_block_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b'.

(** Connections between [store] and [storebytes]. *)

(*X*)
Axiom storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2.

(*X*)
Axiom store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2.

(** Load-store properties. *)

(*X*)
Axiom loadbytes_storebytes_same:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  loadbytes m2 b ofs (Z_of_nat (length bytes)) = Some bytes.
(*X*)
Axiom loadbytes_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
(*X*)
Axiom load_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs'.


(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

(*X*)
Axiom storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
(*X*)
Axiom storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2.

(** ** Properties of [alloc]. *)

(*X* The identifier of the freshly allocated block is the next block
  of the initial memory state. *)

Axiom alloc_result:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  b = nextblock m1.

(** Effect of [alloc] on block validity. *)

(*X*)
Axiom nextblock_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  nextblock m2 = Psucc (nextblock m1).

(*X*)
Axiom valid_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
(*X*)
Axiom fresh_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  ~(valid_block m1 b).
(*X*)
Axiom valid_new_block:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  valid_block m2 b.
(*X*)
Axiom valid_block_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.

(** Effect of [alloc] on permissions. *)

(*X*)
Axiom perm_alloc_1:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
(*X*)
Axiom perm_alloc_2:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
(*X*)
Axiom perm_alloc_3:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
(*X*)
Axiom perm_alloc_4:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
(*X*)
Axiom perm_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.

(** Effect of [alloc] on access validity. *)

(*X*)
Axiom valid_access_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
(*X*)
Axiom valid_access_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
(*X*)
Axiom valid_access_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.

(** Load-alloc properties. *)

(*X*)
Axiom load_alloc_unchanged:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
(*X*)
Axiom load_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
(*X*)
Axiom load_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
(*X*)
Axiom load_alloc_same':
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] current permission. *)

(*X*)
Axiom range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
(*X*)
Axiom free_range_perm:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  range_perm m1 bf lo hi Cur Freeable.

(** Block validity is preserved by [free]. *)

(*X*)
Axiom nextblock_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  nextblock m2 = nextblock m1.
(*X*)
Axiom valid_block_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m1 b -> valid_block m2 b.
(*X*)
Axiom valid_block_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m2 b -> valid_block m1 b.

(** Effect of [free] on permissions. *)

(*X*)
Axiom perm_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
(*X*)
Axiom perm_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
(*X*)
Axiom perm_free_3:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.

(** Effect of [free] on access validity. *)

(*X*)
Axiom valid_access_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
(*X*)
Axiom valid_access_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
(*X*)
Axiom valid_access_free_inv_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
(*X*)
Axiom valid_access_free_inv_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.

(** Load-free properties *)

(*X*)
Axiom load_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.

(** ** Properties of [drop_perm]. *)

(*X*)
Axiom nextblock_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  nextblock m' = nextblock m.
(*X*)
Axiom drop_perm_valid_block_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m b' -> valid_block m' b'.
(*X*)
Axiom drop_perm_valid_block_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m' b' -> valid_block m b'.

(*X*)
Axiom range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  range_perm m b lo hi Cur Freeable.
(*X*)
Axiom range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> 
  exists m', drop_perm m b lo hi p = Some m'.

(*X*)
Axiom perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
(*X*)
Axiom perm_drop_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
(*X*)
Axiom perm_drop_3:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
(*X*)
Axiom perm_drop_4:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.

(*X*)
Axiom load_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.

(** * Relating two memory states. *)

(** ** Memory extensions *)

(*X*  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by relaxing the permissions of [m1] (for instance, allocating larger
  blocks) and replacing some of the [Vundef] values stored in [m1] by
  more defined values stored in [m2] at the same addresses. *)

Parameter extends: mem -> mem -> Prop.

(*X*)
Axiom extends_refl:
  forall m, extends m m.

(*X*)
Axiom load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.

(*X*)
Axiom loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.

(*X*)
Axiom loadbytes_extends:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.

(*X*)
Axiom store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.

(*X*)
Axiom store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.

(*X*)
Axiom storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.

(*X*)
Axiom storebytes_within_extends:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2'.

(*X*)
Axiom storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z_of_nat (length bytes2) -> False) ->
  extends m1 m2'.

(*X*)
Axiom alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.

(*X*)
Axiom free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.

(*X*)
Axiom free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.

(*X*)
Axiom free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.

(*X*)
Axiom valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
(*X*)
Axiom perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p.
(*X*)
Axiom valid_access_extends:
  forall m1 m2 chunk b ofs p,
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.
(*X*)
Axiom valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
(*X*)
Axiom weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.

(** * Memory injections *)

(* A memory injection [f] is a function from addresses to either [None]
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

(*X* SACC: *)
Parameter inject: meminj -> frameinj -> mem -> mem -> Prop.

(*X*)
Axiom valid_block_inject_1:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m1 b1.

(*X*)
Axiom valid_block_inject_2:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m2 b2.

(*X*)
Axiom perm_inject:
  forall f g m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.

(*X*)
Axiom valid_access_inject:
  forall f g m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.

(*X*)
Axiom valid_pointer_inject:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.

(*X*)
Axiom weak_valid_pointer_inject:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.

(*X*)
Axiom address_inject:
  forall f g m1 m2 b1 ofs1 b2 delta p,
  inject f g m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.

(*X*)
Axiom valid_pointer_inject_no_overflow:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

(*X*)
Axiom weak_valid_pointer_inject_no_overflow:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

(*X*)
Axiom valid_pointer_inject_val:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.

(*X*)
Axiom weak_valid_pointer_inject_val:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.

(*X*)
Axiom inject_no_overlap:
  forall f g m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f g m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

(*X*)
Axiom different_pointers_inject:
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

(*X*)
Axiom load_inject:
  forall f g m1 m2 chunk b1 ofs b2 delta v1,
  inject f g m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.

(*X*)
Axiom loadv_inject:
  forall f g m1 m2 chunk a1 a2 v1,
  inject f g m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2.

(*X*)
Axiom loadbytes_inject:
  forall f g m1 m2 b1 ofs len b2 delta bytes1,
  inject f g m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.

(*X*)
Axiom store_mapped_inject:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f g n1 n2.

(*X*)
Axiom store_unmapped_inject:
  forall f g chunk m1 b1 ofs v1 n1 m2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2.

(*X*)
Axiom store_outside_inject:
  forall f g m1 m2 chunk b ofs v m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f g m1 m2'.

(*X*)
Axiom storev_mapped_inject:
  forall f g chunk m1 a1 v1 n1 m2 a2 v2,
  inject f g m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f g n1 n2.

(*X*)
Axiom storebytes_mapped_inject:
  forall f g m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f g n1 n2.

(*X*)
Axiom storebytes_unmapped_inject:
  forall f g m1 b1 ofs bytes1 n1 m2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2.

(*X*)
Axiom storebytes_outside_inject:
  forall f g m1 m2 b ofs bytes2 m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f g m1 m2'.

(*X*)
Axiom  storebytes_empty_inject:
  forall f g m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f g m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f g m1' m2'.

(*X*)
Axiom alloc_right_inject:
  forall f g m1 m2 lo hi b2 m2',
  inject f g m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f g m1 m2'.

(*X*)
Axiom alloc_left_unmapped_inject:
  forall f g m1 m2 lo hi m1' b1,
  inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' g m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).

(*X*)
Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

(*X*)
Axiom alloc_left_mapped_inject:
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

(*X*)
Axiom alloc_parallel_inject:
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

(*X*)
Axiom free_inject:
  forall f g m1 l m1' m2 b lo hi m2',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f g m1' m2'.

(*X*)
Axiom free_parallel_inject:
  forall f g m1 m2 b lo hi m1' b' delta,
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f g m1' m2'.

(*X*)
Axiom drop_outside_inject:
  forall f g m1 m2 b lo hi p m2',
  inject f g m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2'.

(*X* Memory states that inject into themselves. *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

(*X*)

Parameter inject_neutral: forall (thr: block) (m: mem), Prop.

(** ** Properties of [inject_neutral] *)

(*X*)
Axiom empty_inject_neutral:
  forall thr, inject_neutral thr empty.

(*X*)
Axiom alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m'.

(*X*)
Axiom store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m'.

(*X*)
Axiom drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.

(************************************************************)
(************************************************************)
(***** Stack-Aware CompCert Addendum to the Memory Spec *****)
(************************************************************)
(************************************************************)

(** Maximum unaligned stack size *)
Parameter stack_limit': Z.

(* Aligned stack_limit *)
Parameter stack_limit: Z.
Global Opaque stack_limit.

(* Alignement properties of stack_limit *)
Axiom stack_limit_range: 
  0 < stack_limit <= Ptrofs.max_unsigned.
Axiom stack_limit_range': 
  stack_limit + align (size_chunk Mptr) 8 <= Ptrofs.max_unsigned.
Axiom stack_limit_aligned: 
  (8 | stack_limit).

(** Stack ADT and methods *)
Parameter stack: mem -> StackADT.stack.

(** Pushes a new stage on the stack, with no frames in it. *)
Parameter push_new_stage: mem -> mem.

(** Marks the current active frame in the top stage as tailcalled. *)
Parameter tailcall_stage: mem -> option mem.

(** Records a [frame_adt] on the current top stage. *)
Parameter record_stack_blocks: mem -> frame_adt -> option mem.

(** Pops the topmost stage of the stack, if any. *)
Parameter unrecord_stack_block: mem -> option mem.

Parameter record_init_sp : mem -> option mem.

Parameter loadbytesv : memory_chunk -> mem -> val -> option val.

(** Basic Stack Properties*)

Definition top_frame_no_perm m :=
  top_tframe_prop
    (fun tf : tframe_adt =>
     forall b : block,
     in_frames tf b -> forall (o : Z) (k : perm_kind) (p : permission), ~ perm m b o k p)
    (stack m).

Axiom empty_stack:
  stack empty = nil.

Axiom size_stack_below:
  forall m, size_stack (stack m) < stack_limit.

Axiom stack_norepet:
  forall m, nodup (stack m).

Axiom get_frame_info_valid:
  forall m b f, get_frame_info (stack m) b = Some f -> valid_block m b.

Axiom stack_top_valid:
  forall m b, is_stack_top (stack m) b -> valid_block m b.

Axiom in_stack_valid:
  forall m b,
  in_stack ( (stack m)) b -> valid_block m b.

Axiom wf_stack_mem:
  forall m,
  wf_stack (perm m) (stack m).

Axiom stack_perm:
  forall m,
  stack_agree_perms (perm m) (stack m).

(* properties of [record_init_sp] *)

Axiom record_init_sp_stack:
  forall m1 m2,
  record_init_sp m1 = Some m2 ->
  stack m2 = (Some (make_singleton_frame_adt (nextblock (push_new_stage m1)) 0 0),nil)::stack m1.

Axiom record_init_sp_nextblock_eq:
  forall m1 m2,
  record_init_sp m1 = Some m2 ->
      (nextblock m2) = Pos.succ (nextblock m1).

Axiom record_init_sp_perm:
  forall m1 m2,
  record_init_sp m1 = Some m2 ->
  forall b o k p,
  perm m2 b o k p <-> perm m1 b o k p.

(* [range_perm] Properties *)

(*X* SACC *)
Axiom range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p.

(*X* SACC *)
Axiom range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p.

(* Properties of [loadv] *)

Axiom loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv  Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).

(* Properties of [storebytes] *)

Axiom storebytes_get_frame_info:
   forall m1 b o v m2, 
   storebytes m1 b o v = Some m2 ->
   forall b', get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.

Axiom storebytes_is_stack_top:
  forall m1 b o v m2 (STOREBYTES: storebytes m1 b o v = Some m2),
  forall b', is_stack_top (stack m2) b' <-> is_stack_top (stack m1) b'.

(* Properties of [alloc] *)

Axiom alloc_get_frame_info:
  forall m1 lo hi m2 b, 
  alloc m1 lo hi = (m2, b) ->
  forall b', get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.

Axiom alloc_is_stack_top:
  forall m1 lo hi m2 b,
  alloc m1 lo hi = (m2, b) ->
  forall b', is_stack_top (stack m2) b' <-> is_stack_top (stack m1) b'.

Axiom alloc_get_frame_info_fresh:
  forall m1 lo hi m2 b, 
  alloc m1 lo hi = (m2, b) ->
  get_frame_info (stack m2) b = None.

(* Properties of [free] *)

Axiom free_get_frame_info:
  forall m1 b lo hi m2 b',
    free m1 b lo hi = Some m2 ->
    get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.

Axiom perm_free:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  forall b' o' k p,
  perm m' b' o' k p <-> ((~ (b' = b /\ lo <= o' < hi)) /\ perm m b' o' k p).

Axiom free_no_perm_stack:
  forall m b sz m',
  free m b 0 sz = Some m' ->
  forall bi,
  in_stack' (stack m) (b, bi) ->
  frame_size bi = Z.max 0 sz ->
  forall o k p,
    ~ perm m' b o k p.

(* Properties of [free_list] *)

Axiom perm_free_list:
  forall l m m' b ofs k p,
  free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).

Axiom free_no_perm_stack':
  forall m b sz m',
  free m b 0 sz = Some m' ->
  forall bi f0 r s0 l,
  stack m = (Some f0, r) :: s0 ->
  frame_adt_blocks f0 = (b, bi) :: l ->
  frame_size bi = Z.max 0 sz ->
  forall o k p,
  ~ perm m' b o k p.

Axiom free_top_tframe_no_perm:
  forall m b sz m' bi f0 r s0,
  free m b 0 sz = Some m' ->
  stack m = (Some f0, r) :: s0 ->
  frame_adt_blocks f0 = (b, bi) :: nil ->
  frame_size bi = Z.max 0 sz ->
  top_frame_no_perm m'.

Axiom free_top_tframe_no_perm':
  forall m b sz m' bi f0 r s0,
  free m b 0 sz = Some m' ->
  stack m = (Some f0, r) :: s0 ->
  frame_adt_blocks f0 = (b, bi) :: nil ->
  frame_size bi = sz ->
  top_frame_no_perm m'.

(** Pointer integrity properties *)

(* Axiom store_same_ptr:
  forall m1 b o v m2,
  v <> Vundef ->
  Val.has_type v Tptr ->
  loadbytes m1 b o (size_chunk Mptr) = Some (encode_val Mptr v) ->
  store Mptr m1 b o v = Some m2 -> m1 = m2. *)

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

Axiom storev_int64_split:
  forall m a v m',
  storev Mint64 m a v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.

(* Properties of [store] *)

Axiom store_get_frame_info:
  forall chunk m1 b o v m2,
  (store chunk m1 b o v = Some m2) ->
  forall b', get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.

Axiom store_is_stack_top:
   forall chunk m1 b o v m2, 
   store chunk m1 b o v = Some m2 ->
   forall b', is_stack_top (stack m2) b' <-> is_stack_top (stack m1) b'.

(* Properties of [storev] *)

Axiom storev_nextblock :
  forall m chunk addr v m',
  storev chunk m addr v = Some m' ->
  nextblock m' = nextblock m.

Axiom storev_perm_inv:
  forall m chunk addr v m',
  storev chunk m addr v = Some m' ->
  forall b o k p,
  perm m' b o k p ->
  perm m b o k p.

(* Properties of [storebytes] *)

(* Load-store properties *)

Axiom  load_store_similar_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v).

Axiom loadbytes_storebytes_disjoint:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z_of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.

(** Load-alloc properties *)

Axiom loadbytes_alloc_unchanged:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n.
Axiom loadbytes_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef.

(* Load-free properties *)

Axiom loadbytes_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs n,
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.

Axiom loadbytes_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes.

(** Properties of [drop_perm] **)

Axiom loadbytes_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs n,
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n.


(** Properties of [extends] *)

Axiom extends_extends_compos:
  forall m1 m2 m3,
  extends m1 m2 -> extends m2 m3 -> extends m1 m3.

Axiom is_stack_top_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (exists (o : Z) (k : perm_kind) (p : permission), perm m1 b o k p) ->
  is_stack_top (stack m1) b ->
  is_stack_top (stack m2) b.

(** SACC: The [magree] predicate is a variant of [extends] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [lessdef] relation. Needed by Deadcodeproof. *)

Definition locset := block -> Z -> Prop.

Parameter magree : forall (m1 m2 : mem) (P : locset), Prop.

(** ** Properties of [magree]. *)

(*X* SACC:*)
Axiom ma_perm:
  forall m1 m2 (P: locset),
  magree m1 m2 P ->
  forall b ofs k p,
  perm m1 b ofs k p -> perm m2 b ofs k p.

(*X* SACC:*)
Axiom magree_monotone:
  forall m1 m2 (P Q: locset),
  magree m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree m1 m2 Q.

(*X* SACC:*)
Axiom mextends_agree:
  forall m1 m2 P, extends m1 m2 -> magree m1 m2 P.

(*X*)
Axiom magree_extends:
  forall m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree m1 m2 P -> extends m1 m2.

(*X* SACC:*)
Axiom magree_loadbytes:
  forall m1 m2 P b ofs n bytes,
  magree m1 m2 P ->
  loadbytes m1 b ofs n = Some bytes ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  exists bytes', loadbytes m2 b ofs n = Some bytes' /\ list_forall2 memval_lessdef bytes bytes'.

(*X* SACC:*)
Axiom magree_load:
  forall m1 m2 P chunk b ofs v,
  magree m1 m2 P ->
  load chunk m1 b ofs = Some v ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  exists v', load chunk m2 b ofs = Some v' /\ Val.lessdef v v'.

(*X* SACC:*)
Axiom magree_storebytes_parallel:
  forall m1 m2 (P Q: locset) b ofs bytes1 m1' bytes2,
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + Z_of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2', storebytes m2 b ofs bytes2 = Some m2' /\ magree m1' m2' Q.

(*X* SACC:*)
Axiom magree_storebytes_left:
  forall m1 m2 P b ofs bytes1 m1',
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes1) -> ~(P b i)) ->
  magree m1' m2 P.

(*X* SACC:*)
Axiom magree_store_left:
  forall m1 m2 P chunk b ofs v1 m1',
  magree m1 m2 P ->
  store chunk m1 b ofs v1 = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b i)) ->
  magree m1' m2 P.

(*X* SACC:*)
Axiom magree_free:
  forall m1 m2 (P Q: locset) b lo hi m1',
  magree m1 m2 P ->
  free m1 b lo hi = Some m1' ->
  (forall b' i, Q b' i ->
   b' <> b \/ ~(lo <= i < hi) ->
   P b' i) ->
  exists m2', free m2 b lo hi = Some m2' /\ magree m1' m2' Q.

(*X* SACC:*)
Axiom magree_valid_access:
  forall m1 m2 (P: locset) chunk b ofs p,
  magree m1 m2 P ->
  valid_access m1 chunk b ofs p ->
  valid_access m2 chunk b ofs p.

(** Weak Memory injections *)

Parameter weak_inject: meminj -> frameinj -> mem -> mem -> Prop.

(** Properties of [inject]*)

Axiom inject_delta_pos:
  forall f g m1 m2 b1 b2 delta,
  inject f g m1 m2 ->
  f b1 = Some (b2, delta) ->
  delta >= 0.

Axiom inject_ext:
  forall f f' g m1 m2,
  inject f g m1 m2 ->
  (forall b, f b = f' b) ->
  inject f' g m1 m2.

(*X* SACC:*)
Axiom range_perm_inject:
  forall f g m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p.

(*X* SACC:*)
Axiom valid_pointer_inject': 
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

(*X* SACC:*)
Axiom weak_valid_pointer_inject': 
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

(*X* SACC: The following is needed by Separation, to prove storev_parallel_rule *)
Axiom address_inject':
  forall f g m1 m2 chunk b1 ofs1 b2 delta,
  inject f g m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.

(*X* SACC:*)
Axiom disjoint_or_equal_inject:
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

(*X* SACC:*)
Axiom aligned_area_inject:
  forall f g m m' b ofs al sz b' delta,
  inject f g m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta).

(*X* SACC:*)
Axiom free_left_inject:
  forall f g m1 m2 b lo hi m1',
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f g m1' m2.

(*X* SACC:*)
Axiom free_list_left_inject:
  forall f g m2 l m1 m1',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f g m1' m2.

(*X* SACC:*)
Axiom free_right_inject:
  forall f g m1 m2 b lo hi m2',
  inject f g m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2'.

(*X* SACC:*)
Axiom store_right_inject:
  forall f g m1 m2 chunk b ofs v m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
   f b' = Some(b, delta) ->
   ofs' + delta = ofs ->
   exists vl, loadbytes m1 b' ofs' (size_chunk chunk) = Some vl /\
              list_forall2 (memval_inject f) vl (encode_val chunk v)) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f g m1 m2'.

(*X* SACC:*)
Axiom drop_parallel_inject:
  forall f g m1 m2 b1 b2 delta lo hi p m1',
  inject f g m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ inject f g m1' m2'.

(*X* SACC:*)
Axiom drop_right_inject: 
  forall f g m1 m2 b lo hi p m2',
  inject f g m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs' k p',
   f b' = Some(b, delta) ->
   perm m1 b' ofs' k p' ->
   lo <= ofs' + delta < hi -> p' = p) ->
   inject f g m1 m2'.

(*X* SACC:*)
Axiom drop_extended_parallel_inject:
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

(*X* SACC: Needed by Stackingproof, with Linear2 to Mach,
   to compose extends (in Linear2) and inject. *)
Axiom extends_inject_compose:
  forall f g m1 m2 m3,
  extends m1 m2 -> inject f g m2 m3 -> inject f g m1 m3.

(*X* SACC:*)
Axiom inject_stack_inj_wf:
  forall f g m1 m2,
  inject f g m1 m2 ->
  sum_list g = length (stack m1) /\ length g = length (stack m2).

Axiom is_stack_top_inject:
  forall f g m1 m2 b1 b2 delta,
  inject f g m1 m2 ->
  f b1 = Some (b2, delta) ->
  (exists (o : Z) (k : perm_kind) (p : permission), perm m1 b1 o k p) ->
  is_stack_top ( (stack m1)) b1 -> is_stack_top ( (stack m2)) b2.

Axiom record_stack_block_inject_left_zero:
  forall m1 m1' m2 j g f1 f2,
  inject j g m1 m2 ->
  frame_at_pos (stack m2) O f2 ->
  tframe_inject j (perm m1) (Some f1,nil) f2 ->
  record_stack_blocks m1 f1 = Some m1' ->
  inject j g m1' m2.

Axiom unrecord_stack_block_inject_left_zero:
  forall (m1 m1' m2 : mem) (j : meminj) n g,
  inject j (S n :: g) m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  (1 <= n)%nat ->
  inject j (n :: g) m1' m2.

Axiom self_inject:
  forall f m,
  (forall b, f b = None \/ f b = Some (b, 0)) ->
  (forall b, f b <> None -> valid_block m b) ->
  (forall b,
     f b <> None ->
     forall o b' o' q n,
       loadbytes m b o 1 = Some (Fragment (Vptr b' o') q n :: nil) ->
       f b' <> None) ->
  inject f (flat_frameinj (length (stack m))) m m.

Axiom frame_inject_flat:
  forall thr f,
  Forall (fun bfi => Plt (fst bfi) thr) (frame_adt_blocks f) ->
  frame_inject (flat_inj thr) f f.

(** ** Properties of [weak_inject]. *)

(*X* SACC:*)
Axiom empty_weak_inject: forall f m, 
  stack m = nil ->
  (forall b b' delta, f b = Some(b', delta) -> delta >= 0) ->
  (forall b b' delta, f b = Some(b', delta) -> valid_block m b') ->
  weak_inject f nil empty m.

(*X* SACC:*)
Axiom weak_inject_to_inject: forall f g m1 m2,
  weak_inject f g m1 m2 -> 
  (forall b p, f b = Some p -> valid_block m1 b) ->
  inject f g m1 m2.

(*X* SACC:*)
Axiom store_mapped_weak_inject:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  weak_inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ weak_inject f g n1 n2.

(*X* SACC:*)
Axiom alloc_left_mapped_weak_inject:
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

(*X* SACC:*)
Axiom alloc_left_unmapped_weak_inject:
  forall f g m1 m2 lo hi m1' b1,
  f b1 = None ->
  weak_inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  weak_inject f g m1' m2.

(*X* SACC:*)
Axiom drop_parallel_weak_inject:
  forall f g m1 m2 b1 b2 delta lo hi p m1',
  weak_inject f g m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ weak_inject f g m1' m2'.

(*X* SACC:*)
Axiom drop_extended_parallel_weak_inject:
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

(** ** Properties of [inject_neutral] *)

(*X* SACC:*)
Axiom neutral_inject:
  forall m, inject_neutral (nextblock m) m ->
  inject (flat_inj (nextblock m)) (flat_frameinj (length (stack m))) m m.

(** Invariance properties between two memory states *)

Parameter unchanged_on: forall (P: block -> Z -> Prop) (m_before m_after: mem), Prop.

(** ** Properties of [unchanged_on] and [strong_unchanged_on] *)

Axiom unchanged_on_refl:
  forall P m, unchanged_on P m m.
Axiom unchanged_on_nextblock:
  forall P m1 m2,
  unchanged_on P m1 m2 ->
  Ple (nextblock m1) (nextblock m2).
Axiom unchanged_on_trans:
  forall P m1 m2 m3, 
  unchanged_on P m1 m2 -> 
  unchanged_on P m2 m3 -> 
  unchanged_on P m1 m3.
Axiom perm_unchanged_on:
  forall P m m' b ofs k p,
  unchanged_on P m m' -> 
  P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p.
Axiom perm_unchanged_on_2:
  forall P m m' b ofs k p,
  unchanged_on P m m' -> 
  P b ofs -> 
  valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p.
Axiom loadbytes_unchanged_on_1:
  forall P m m' b ofs n,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n.
Axiom loadbytes_unchanged_on:
  forall P m m' b ofs n bytes,
  unchanged_on P m m' ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m b ofs n = Some bytes -> loadbytes m' b ofs n = Some bytes.
Axiom load_unchanged_on_1:
  forall P m m' chunk b ofs,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs.
Axiom load_unchanged_on:
  forall P m m' chunk b ofs v,
  unchanged_on P m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs = Some v -> load chunk m' b ofs = Some v.
Axiom unchanged_on_implies:
  forall (P Q: block -> Z -> Prop) m m',
  unchanged_on P m m' ->
  (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
  unchanged_on Q m m'.
Axiom store_unchanged_on:
  forall P chunk m b ofs v m',
  store chunk m b ofs v = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
  unchanged_on P m m'.
Axiom storebytes_unchanged_on:
  forall P m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  unchanged_on P m m'.
Axiom alloc_unchanged_on:
  forall P m lo hi m' b,
  alloc m lo hi = (m', b) ->
  unchanged_on P m m'.
Axiom free_unchanged_on:
  forall P m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on P m m'.
Axiom drop_perm_unchanged_on:
  forall P m b lo hi p m',
  drop_perm m b lo hi p = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on P m m'.

(** The following property is needed by Separation, to prove
minjection. HINT: it can be used only for [strong_unchanged_on], not
for [unchanged_on]. *)

Axiom inject_unchanged_on:
   forall j g m0 m m',
   inject j g m0 m ->
   unchanged_on
     (fun (b : block) (ofs : Z) =>
        exists (b0 : block) (delta : Z),
          j b0 = Some (b, delta) /\
          perm m0 b0 (ofs - delta) Max Nonempty) m m' ->
   stack m' = stack m ->
   inject j g m0 m'.

(* Perm equivalences *)

Axiom store_perm:
  forall chunk m b' o' v m',
  store chunk m b' o' v = Some m' ->
  forall b o k p,
  perm m' b o k p <-> perm m b o k p.

Axiom storev_perm:
  forall chunk m addr v m',
  storev chunk m addr v = Some m' ->
  forall b o k p,
  perm m' b o k p <-> perm m b o k p.

Axiom free_perm:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  forall b' o k p,
  perm m' b' o k p <-> if peq b b' && zle lo o && zlt o hi then False else perm m b' o k p.

Axiom alloc_perm:
  forall m lo hi m' b,
  alloc m lo hi = (m',b) ->
  forall b' o k p,
  perm m' b' o k p <-> if peq b b' then lo <= o < hi else perm m b' o k p.

Axiom record_perm:
  forall m fi m',
  record_stack_blocks m fi = Some m' ->
  forall b o k p,
  perm m' b o k p <-> perm m b o k p.

Axiom unrecord_perm:
  forall m m',
  unrecord_stack_block m = Some m' ->
  forall b o k p,
  perm m' b o k p <-> perm m b o k p.

Axiom drop_perm_perm:
  forall m b lo hi p m',
  drop_perm m b lo hi p = Some m' ->
  forall b' o k p',
  perm m' b' o k p' <-> (perm m b' o k p' /\( b = b' -> lo <= o < hi -> perm_order p p')).

(* Original operations don't modify the stack. *)
Axiom store_stack_unchanged:
  forall chunk m1 b1 ofs v1 n1,
    store chunk m1 b1 ofs v1 = Some n1 ->
    stack n1 = stack m1.

Axiom storev_stack_unchanged:
  forall m chunk addr v m',
    storev chunk m addr v = Some m' ->
    stack m' = stack m.

Axiom storebytes_stack_unchanged:
  forall m1 b o bytes m2,
  storebytes m1 b o bytes = Some m2 ->
  stack m2 = stack m1.

Axiom alloc_stack_unchanged:
  forall m1 lo hi m2 b,
  alloc m1 lo hi = (m2, b) ->
  stack m2 = stack m1.

Axiom free_stack_unchanged:
  forall m1 b lo hi m2,
  free m1 b lo hi = Some m2 ->
  stack m2 = stack m1.

Axiom freelist_stack_unchanged:
  forall bl m m',
  free_list m bl = Some m' ->
  stack m' = stack m.

Axiom drop_perm_stack_unchanged:
   forall m1 b lo hi p m2,
   drop_perm m1 b lo hi p = Some m2 ->
    stack m2 = stack m1.

(*X* SACC: *)
Definition valid_frame f m :=
  forall b, in_frame f b -> valid_block m b.

(*X* SACC: *)
Definition mem_unchanged (T: mem -> mem -> Prop) :=
  forall m1 m2, T m1 m2 ->
           nextblock m2 = nextblock m1
           /\ (forall b o k p, perm m2 b o k p <-> perm m1 b o k p)
           /\ (forall P, unchanged_on P m1 m2)
           /\ (forall b o chunk, load chunk m2 b o = load chunk m1 b o).

(* Properties of [push_new_stage] *)


Axiom push_new_stage_nextblock: 
  forall m, 
  nextblock (push_new_stage m) = nextblock m.

Axiom push_new_stage_length_stack:
  forall m,
  length (stack (push_new_stage m)) = S (length (stack m)).

Axiom push_new_stage_load: 
  forall chunk m b o,
  load chunk (push_new_stage m) b o = load chunk m b o.

Axiom loadbytes_push:
  forall m b o n,
  loadbytes (push_new_stage m) b o n = loadbytes m b o n.

Axiom push_new_stage_inject:
  forall j g m1 m2,
  inject j g m1 m2 ->
  inject j (1%nat :: g) (push_new_stage m1) (push_new_stage m2).

Axiom inject_push_new_stage_left:
  forall j n g m1 m2,
  inject j (n::g) m1 m2 ->
  inject j (S n :: g) (push_new_stage m1) m2.

Axiom inject_push_new_stage_right:
  forall j n g m1 m2,
  inject j (S n :: g) m1 m2 ->
  top_tframe_tc (stack m1) ->
  (O < n)%nat ->
  inject j (1%nat :: n :: g) m1 (push_new_stage m2).

Axiom push_new_stage_stack:
  forall m,
  stack (push_new_stage m) = (None, nil) :: stack m.

Axiom push_new_stage_perm:
  forall m b o k p,
  perm (push_new_stage m) b o k p <-> perm m b o k p.

Axiom extends_push:
  forall m1 m2,
  extends m1 m2 ->
  extends (push_new_stage m1) (push_new_stage m2).

Axiom push_new_stage_unchanged_on:
  forall P m,
  unchanged_on P m (push_new_stage m).

Axiom push_new_stage_loadv:
  forall chunk m v,
  loadv chunk (push_new_stage m) v = loadv chunk m v.

Axiom storebytes_push:
  forall m b o bytes m',
  storebytes (push_new_stage m) b o bytes = Some m' ->
  exists m2,
    storebytes m b o bytes = Some m2.

Axiom magree_push:
  forall P m1 m2,
  magree m1 m2 P ->
  magree (push_new_stage m1) (push_new_stage m2) P.

Axiom push_new_stage_inject_flat:
   forall j m1 m2,
   inject j (flat_frameinj (length (stack m1))) m1 m2 ->
   inject j (flat_frameinj (length (stack (push_new_stage m1))))
            (push_new_stage m1) (push_new_stage m2).

(* Properties of [tailcall_stage] *)

Axiom tailcall_stage_unchanged_on:
  forall P m1 m2,
  tailcall_stage m1 = Some m2 ->
  unchanged_on P m1 m2.

Axiom magree_tailcall_stage:
  forall P m1 m2 m1',
  magree m1 m2 P ->
  tailcall_stage m1 = Some m1' ->
  top_frame_no_perm m2 ->
  exists m2', tailcall_stage m2 = Some m2' /\ magree m1' m2' P.

Axiom tailcall_stage_tc:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  top_tframe_tc (stack m2).

Axiom tailcall_stage_perm:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  forall b o k p,
  perm m2 b o k p <-> perm m1 b o k p.

Axiom tailcall_stage_tl_stack:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  tl (stack m2) = tl (stack m1).

Axiom tailcall_stage_extends:
  forall m1 m2 m1',
  extends m1 m2 ->
  tailcall_stage m1 = Some m1' ->
  top_frame_no_perm m2 ->
  exists m2', tailcall_stage m2 = Some m2' /\ extends m1' m2'.

Axiom tailcall_stage_inject:
  forall j g m1 m2 m1',
  inject j g m1 m2 ->
  tailcall_stage m1 = Some m1' ->
  top_frame_no_perm m2 ->
  exists m2', tailcall_stage m2 = Some m2' /\ inject j g m1' m2'.

Axiom tailcall_stage_stack_equiv:
  forall m1 m2 m1' m2',
  tailcall_stage m1 = Some m1' ->
  tailcall_stage m2 = Some m2' ->
  stack_equiv (stack m1)  (stack m2) ->
  stack_equiv (stack m1') (stack m2').

Axiom tailcall_stage_same_length_pos:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  length (stack m2) = length (stack m1) /\ lt O (length (stack m1)).

Axiom tailcall_stage_nextblock:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  nextblock m2 = nextblock m1.

Axiom tailcall_stage_inject_left:
  forall j n g m1 m2 m1',
  inject j (n :: g) m1 m2 ->
  tailcall_stage m1 = Some m1' ->
  inject j (n::g) m1' m2.

Axiom tailcall_stage_right_extends:
  forall m1 m2,
  extends m1 m2 ->
  top_frame_no_perm m1 ->
  top_frame_no_perm m2 ->
  exists m2', tailcall_stage m2 = Some m2' /\ extends m1 m2'.

Axiom tailcall_stage_stack_eq:
  forall m1 m2,
  tailcall_stage m1 = Some m2 ->
  exists f r,
  stack m1 = f :: r /\ stack m2 = (None, opt_cons (fst f) (snd f))::r.

Axiom stack_inject_tailcall_stage:
  forall j g m f1 l1 s1 f2 l2 s2,
  stack_inject j m (1%nat::g) ((Some f1,l1)::s1) ((Some f2, l2)::s2) ->
  stack_inject j m (1%nat::g) ((None, f1::l1)::s1) ((None, f2::l2)::s2).

Axiom tailcall_stage_inject_flat:
  forall j m1 m2 m1',
  inject j (flat_frameinj (length (stack m1))) m1 m2 ->
  tailcall_stage m1 = Some m1' ->
  top_frame_no_perm m2 ->
  exists m2',
    tailcall_stage m2 = Some m2' /\ inject j (flat_frameinj (length (stack m1'))) m1' m2'.

(* Properties of [record_stack_block] *)

Axiom record_stack_blocks_original_stack:
  forall m1 f1 m2,
    record_stack_blocks m1 f1 = Some m2 ->
    exists f r,
      stack m1 = (None,f)::r.

Axiom record_stack_blocks_stack_eq:
  forall m1 f m2,
  record_stack_blocks m1 f = Some m2 ->
  exists tf r,
    stack m1 = (None,tf)::r /\ stack m2 = (Some f,tf)::r.

Axiom record_stack_blocks_length_stack:
  forall m1 f m2,
  record_stack_blocks m1 f = Some m2 ->
  length (stack m2) = length (stack m1).

Axiom record_stack_blocks_inject_left:
  forall m1 m1' m2 j g f1 f2,
  inject j g m1 m2 ->
  frame_at_pos (stack m2) 0 f2 ->
  tframe_inject j (perm m1) (Some f1, nil) f2 ->
  record_stack_blocks m1 f1 = Some m1' ->
  inject j g m1' m2.

Axiom record_stack_blocks_inject_parallel:
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

Axiom record_stack_blocks_extends:
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

Axiom record_stack_blocks_mem_unchanged:
  forall bfi,
  mem_unchanged (fun m1 m2 => record_stack_blocks m1 bfi = Some m2).

Axiom record_stack_blocks_stack:
  forall m fi m' f s,
  record_stack_blocks m fi = Some m' ->
  stack m = f::s -> stack m' = (Some fi , snd f) :: s.

Axiom record_stack_blocks_inject_neutral:
  forall thr m fi m',
  inject_neutral thr m ->
  record_stack_blocks m fi = Some m' ->
  Forall (fun b => Plt b thr) (map fst (frame_adt_blocks fi)) ->
  inject_neutral thr m'.

Axiom record_stack_block_inject_flat:
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

Axiom record_stack_blocks_top_tframe_no_perm:
  forall m1 f m2,
  record_stack_blocks m1 f = Some m2 ->
  top_tframe_tc (stack m1).

Axiom record_stack_block_unchanged_on:
  forall m bfi m' (P: block -> Z -> Prop),
  record_stack_blocks m bfi = Some m' ->
  unchanged_on P m m'.

Axiom record_stack_block_perm:
  forall m bfi m',
  record_stack_blocks m bfi = Some m' ->
  forall b' o k p,
    perm m' b' o k p ->
    perm m b' o k p.

Axiom record_stack_block_perm': 
  forall m m' bofi,
  record_stack_blocks m bofi = Some m' ->
  forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
  perm m b' o k p -> perm m' b' o k p.

Axiom record_stack_block_valid:
  forall m bf m',
  record_stack_blocks m bf = Some m' ->
  forall b', valid_block m b' -> valid_block m' b'.

Axiom record_stack_block_nextblock:
  forall m bf m',
  record_stack_blocks m bf = Some m' ->
  nextblock m' = nextblock m.

Axiom record_stack_block_is_stack_top:
  forall m b fi m',
  record_stack_blocks m fi = Some m' ->
  in_frame fi b ->
  is_stack_top (stack m') b.

Axiom record_push_inject:
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

Axiom record_push_inject_flat:
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

Axiom record_stack_blocks_inject_parallel_flat:
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

Axiom record_push_inject_alloc: 
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

Axiom record_push_inject_flat_alloc:
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

Axiom record_push_extends_flat_alloc: 
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

(* Properties of [unrecord_stack_block] *)

Axiom unrecord_stack_block_inject_parallel:
  forall (m1 m1' m2 : mem) (j : meminj) g,
  inject j (1%nat :: g) m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  exists m2', unrecord_stack_block m2 = Some m2' /\ inject j g m1' m2'.

Axiom unrecord_stack_block_inject_left:
  forall (m1 m1' m2 : mem) (j : meminj) n g,
  inject j (S n :: g) m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  (1 <= n)%nat ->
  top_frame_no_perm m1 ->
  inject j (n :: g) m1' m2.

Axiom unrecord_stack_block_extends:
  forall m1 m2 m1',
  extends m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  exists m2',
  unrecord_stack_block m2 = Some m2' /\
  extends m1' m2'.

Axiom unrecord_stack_block_mem_unchanged:
  mem_unchanged (fun m1 m2 => unrecord_stack_block m1 = Some m2).

Axiom unrecord_stack_eq:
  forall m m',
  unrecord_stack_block m = Some m' ->
  exists b, stack m = b :: stack m'.

Axiom unrecord_stack_block_succeeds:
  forall m b r,
  stack m = b :: r ->
  exists m', unrecord_stack_block m = Some m' /\ stack m' = r.

Axiom unrecord_stack_block_inject_neutral:
  forall thr m m',
  inject_neutral thr m ->
  unrecord_stack_block m = Some m' ->
  inject_neutral thr m'.

Axiom unrecord_stack_block_inject_parallel_flat:
  forall (m1 m1' m2 : mem) (j : meminj),
  inject j (flat_frameinj (length (stack m1))) m1 m2 ->
  unrecord_stack_block m1 = Some m1' ->
  exists m2',
    unrecord_stack_block m2 = Some m2' /\
    inject j (flat_frameinj (length (stack m1'))) m1' m2'.

Axiom unrecord_stack_block_unchanged_on:
  forall m m' P,
  unrecord_stack_block m = Some m' ->
  unchanged_on P m m'.

Axiom unrecord_stack_block_perm:
  forall m m',
  unrecord_stack_block m = Some m' ->
  forall b' o k p,
  perm m' b' o k p ->
  perm m b' o k p.

Axiom unrecord_stack_block_perm': 
  forall m m' : mem,
  unrecord_stack_block m = Some m' ->
  forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
  perm m b' o k p -> perm m' b' o k p.

Axiom unrecord_stack_block_nextblock:
  forall m m',
  unrecord_stack_block m = Some m' ->
  nextblock m' = nextblock m.

Axiom unrecord_stack_block_get_frame_info:
  forall m m' b,
  unrecord_stack_block m = Some m' ->
  ~ is_stack_top (stack m) b ->
  get_frame_info (stack m') b = get_frame_info (stack m) b.

Axiom magree_unrecord:
  forall m1 m2 P,
  magree m1 m2 P ->
  forall m1',
  unrecord_stack_block m1 = Some m1' ->
  exists m2',
  unrecord_stack_block m2 = Some m2' /\ magree m1' m2' P.

(* Interaction of [unrecord_stack] with [push_new_stage] *)

Axiom unrecord_push:
  forall m, unrecord_stack_block (push_new_stage m) = Some m.

Axiom push_storebytes_unrecord:
  forall m b o bytes m1 m2,
  storebytes m b o bytes = Some m1 ->
  storebytes (push_new_stage m) b o bytes = Some m2 ->
  unrecord_stack_block m2 = Some m1.

Axiom push_store_unrecord:
  forall m b o chunk v m1 m2,
  store chunk m b o v = Some m1 ->
  store chunk (push_new_stage m) b o v = Some m2 ->
  unrecord_stack_block m2 = Some m1.

(* Interaction of [tailcall_stage] and [push_new_stage] *)

Axiom inject_new_stage_left_tailcall_right:
  forall j n g m1 m2,
  inject j (n :: g) m1 m2 ->
  (forall l, 
    take ( n) (stack m1) = Some l ->
    Forall (fun tf => forall b, in_frames tf b -> forall o k p, ~ perm m1 b o k p) l) ->
  top_frame_no_perm m2 ->
  exists m2',
    tailcall_stage m2 = Some m2' /\
    inject j (S n :: g) (push_new_stage m1) m2'.

Axiom inject_tailcall_left_new_stage_right:
  forall (j : meminj) (n : nat) (g : list nat) (m1 m2 m1' : mem),
  inject j (S n :: g) m1 m2 ->
  lt O n ->
  tailcall_stage m1 = Some m1' ->
  inject j (1%nat:: n :: g) m1' (push_new_stage m2).

End MEM.
