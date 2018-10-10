Require compcert.backend.RTL.
Require SmallstepX.
Require EventsX.

Import AST.
Import Values.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Export RTL.

Require Import ZArith.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable fn_stack_requirements: ident -> Z.

(** Execution of RTL functions with C-style arguments (long long 64-bit integers allowed) *)

Inductive initial_state (p: RTL.program) (i: ident) (m: mem) (sg: signature) (args: list val): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    f
    (Hf: Genv.find_funct_ptr (Genv.globalenv p) b = Some f)
    (** We need to keep the signature because it is required for lower-level languages *)
    (Hsig: sg = funsig f)
  :
      initial_state p i m sg args (Callstate nil f args (Mem.push_new_stage m) (fn_stack_requirements i))
.

Inductive final_state (sg: signature): state -> (val * mem) -> Prop :=
| final_state_intro
    v
    m m' (USB: Mem.unrecord_stack_block m = Some m'):
    final_state sg (Returnstate nil v m) (v, m')
.

Definition semantics
           (p: RTL.program) (i: ident) (m: mem) (sg: signature) (args: list val) : Smallstep.semantics _ :=

  Semantics (RTL.step fn_stack_requirements) (initial_state p i m sg args) (final_state sg) (Genv.globalenv p).

Lemma initial_stack_inv:
  forall p i m sg args s,
    initial_state p i m sg args s ->
    RTL.stack_inv s.
Proof.
  intros p i m sg args s IS; inversion IS; subst.
  econstructor.
  rewrite_stack_blocks. constructor. reflexivity.
  simpl; constructor.
Qed.

End WITHCONFIG.
