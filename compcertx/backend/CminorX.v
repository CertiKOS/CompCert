Require compcert.backend.Cminor.
Require SmallstepX.
Require EventsX.

Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Export Cminor.

Require Import ZArith.

Section WITHCONFIG.
Context `{external_calls_prf: ExternalCalls}.

Variable fn_stack_requirements: ident -> Z.

(** Execution of Cminor functions with C-style arguments (long long 64-bit integers allowed) *)

Inductive initial_state (p: Cminor.program) (i: ident) (m: mem) (sg: signature) (args: list val): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    f
    (Hf: Genv.find_funct_ptr (Genv.globalenv p) b = Some f)
    (** We need to keep the signature because it is required for lower-level languages *)
    (Hsig: sg = funsig f)
  :
     initial_state p i m sg args (Callstate f args Kstop (Mem.push_new_stage m) (fn_stack_requirements i))
.

Lemma stack_inv_initial:
  forall p i m sg args S
    (INIT: initial_state p i m sg args S),
    stack_inv S.
Proof.
  intros; inversion INIT; subst; econstructor.
  rewrite_stack_blocks; constructor. reflexivity.
  constructor.
Qed.

Inductive final_state (sg: signature): state -> (val * mem) -> Prop :=
| final_state_intro
    v
    m m' (USB: Mem.unrecord_stack_block m = Some m'):
    final_state sg (Returnstate v Kstop m) (v, m')
.

(** We define the per-module semantics of RTL as adaptable to both C-style and Asm-style;
    by default it is C-style. *)

Definition semantics
           (p: Cminor.program) (i: ident) (m: mem)
           (sg: signature) (args: list val) :=
  Semantics (Cminor.step fn_stack_requirements) (initial_state p i m sg args) (final_state sg) (Genv.globalenv p).

End WITHCONFIG.
