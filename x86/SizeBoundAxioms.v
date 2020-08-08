(* *******************  *)
(* Author: Yutin Wang *)
(* Date:   Jan 30, 2020 *)
(* *******************  *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import RelocProgram RelocProgSemantics RelocProgSemantics1 RelocElf.
Require Import RelocElfgen TablesEncode Symbtablegen.


Axiom unsigned_repr: forall n, Ptrofs.unsigned (Ptrofs.repr n) = n.
Axiom code_size_bound : forall c, code_size c < Ptrofs.max_unsigned.
Axiom sections_size_bound: forall s, elf_header_size + get_sections_size s < two_power_pos 32.
Axiom defs_size_inbound: forall defs, sections_size (create_sec_table defs) <= Ptrofs.max_unsigned.
