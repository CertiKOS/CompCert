Require Import ZArith Integers Values.
Require Import Memdata Lists.List.
Require Import Ascii String.
Import ListNotations.

Definition encode_int_big (n:nat) (i: Z) : list byte :=
  rev (bytes_of_int n i).

Definition encode_int_little (n:nat) (i: Z) : list byte :=
  bytes_of_int n i.

Definition encode_int32 (i:Z) : list byte :=
  encode_int 4 i.

Definition encode_int16 (i:Z) : list byte :=
  encode_int 2 i.

Definition zero_bytes (n:nat) : list byte :=
  List.map (fun _ => Byte.zero) (seq 1 n).

Definition ascii_to_byte (c: ascii) : byte :=
  Byte.repr (Z.of_nat (nat_of_ascii c)).

Fixpoint string_to_bytes (s:string) : list byte :=
  match s with
  | EmptyString => []
  | String c s' => (ascii_to_byte c) :: string_to_bytes s'
  end.

Notation "CB[ c ]" := (ascii_to_byte c) (right associativity) : string_byte_scope.
Notation "SB[ str ]" := (string_to_bytes str) (right associativity) : string_byte_scope.

Definition decode_int32 (lb: list byte) : Z :=
  decode_int lb.

Definition decode_int16 (lb: list byte) : Z :=
  decode_int lb.

Lemma decode_encode_int32 z :
  (decode_int32 (encode_int32 z) = z mod two_p (Z.of_nat 32))%Z.
Proof.
  unfold decode_int32, encode_int32.
  rewrite decode_encode_int. reflexivity.
Qed.

Lemma decode_encode_int16 z :
  (decode_int16 (encode_int16 z) = z mod two_p (Z.of_nat 16))%Z.
Proof.
  unfold decode_int16, encode_int16.
  rewrite decode_encode_int. reflexivity.
Qed.
