Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events.
Require Import FlatAsmGlobenv FlatAsmBuiltin FlatAsmProgram.
Require Import Asm.

Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Section WITHGE.

Context {F V I: Type}.
Variable ge: Genv.t F V I.
  
(** Evaluating an addressing mode *)

Definition eval_addrmode32 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.add  (match base with
             | None => Vint Int.zero
             | Some r => rs r
            end)
  (Val.add (match ofs with
             | None => Vint Int.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mul (rs r) (Vint (Int.repr sc))
             end)
           (match const with
            | inl ofs => Vint (Int.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode64 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.addl (match base with
             | None => Vlong Int64.zero
             | Some r => rs r
            end)
  (Val.addl (match ofs with
             | None => Vlong Int64.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mull (rs r) (Vlong (Int64.repr sc))
             end)
           (match const with
            | inl ofs => Vlong (Int64.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode (a: addrmode) (rs: regset) : val :=
  if Archi.ptr64 then eval_addrmode64 a rs else eval_addrmode32 a rs.

End WITHGE.


(** [CompCertiKOS:test-compcert-param-mem-accessors] For CertiKOS, we
need to parameterize over [exec_load] and [exec_store], which will be
defined differently depending on whether we are in kernel or user
mode. *)

Class MemAccessors
      `{!Mem.MemoryModelOps mem}
      (exec_load: forall F V I: Type, Genv.t F V I -> memory_chunk -> mem -> addrmode -> regset -> preg -> ptrofs -> outcome)
      (exec_store: forall F V I: Type, Genv.t F V I -> memory_chunk -> mem -> addrmode -> regset -> preg -> list preg -> ptrofs -> outcome)
: Prop := {}.

Section MEM_ACCESSORS_DEFAULT.

(** [CompCertiKOS:test-compcert-param-mem-accessors] Compcert does not
care about kernel vs. user mode, and uses its memory model to define
its memory accessors. *)

Definition exec_load {F V I} (ge: Genv.t F V I) (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) (sz:ptrofs):=
  match Mem.loadv chunk m (eval_addrmode ge a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v) sz) m
  | None => Stuck
  end.

Definition exec_store {F V I} (ge: Genv.t F V I) (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) (sz:ptrofs) :=
  match Mem.storev chunk m (eval_addrmode ge a rs) (rs r1) with
  | Some m' =>
    Next (nextinstr_nf (undef_regs destroyed rs) sz) m'
  | None => Stuck
  end.

Instance mem_accessors_default: MemAccessors (@exec_load) (@exec_store).

End MEM_ACCESSORS_DEFAULT.

End WITHEXTERNALCALLS.