Require Import Coqlib Integers.

Require Import Events LanguageInterface Smallstep Globalenvs Values Memory.
Require Import AST Ctypes Clight.

Require Import List Maps.
Import ListNotations.

Notation hello_bytes := [ Byte.repr 104; Byte.repr 101; Byte.repr 108; Byte.repr 108; Byte.repr 111 ].
Notation urbby_bytes := [ Byte.repr 117; Byte.repr 114; Byte.repr 98; Byte.repr 98; Byte.repr 121].
Definition rot13_bytes : list byte -> list byte. Admitted.
Lemma rot13_bytes_hello: rot13_bytes hello_bytes = urbby_bytes. Admitted.
Lemma rot13_bytes_urbby: rot13_bytes urbby_bytes = hello_bytes. Admitted.

Notation tvoid := (Tvoid).
Notation tchar := (Tint I8 Unsigned noattr).
Notation tint := (Tint I32 Unsigned noattr).
Notation tarray := (fun ty size => Tarray ty size noattr).
Notation tptr := (fun ty => Tpointer ty noattr).

Definition rw_parameters := Tcons tint (Tcons (tptr tchar) (Tcons tint Tnil)).
Definition write_sig : signature :=
  signature_of_type rw_parameters tvoid cc_default.
Definition write_type :=
  Tfunction rw_parameters tint cc_default.
Definition write : fundef :=
  External (EF_external "write" write_sig) rw_parameters tint cc_default.
Definition read_sig : signature :=
  signature_of_type rw_parameters tint cc_default.
Definition read_type :=
  Tfunction rw_parameters tint cc_default.
Definition read : fundef :=
  External (EF_external "read" write_sig) rw_parameters tint cc_default.

Definition main_sig := signature_of_type Tnil tint cc_default.

Definition secret_main_id: positive := 1.
Definition secret_msg_id: positive := 2.
Definition secret_write_id: positive := 3.

Definition msg_globvar : globvar type :=
  {|
    gvar_info := tarray tchar 5%Z;
    gvar_init := [ Init_int8 (Int.repr 104); (* h *)
                   Init_int8 (Int.repr 101); (* e *)
                   Init_int8 (Int.repr 108); (* l *)
                   Init_int8 (Int.repr 108); (* l *)
                   Init_int8 (Int.repr 111) ]; (* o *)
    gvar_readonly := false;
    gvar_volatile := false;
  |}.

Definition secret_main_body : statement :=
  Ssequence
    (* write(1, msg, sizeof msg - 1) *)
    (Scall None (Evar secret_write_id write_type)
       [ Econst_int (Int.repr 1) tint;
         Evar secret_msg_id (tptr tchar);
         Econst_int (Int.repr 5) tint ]) (* sizeof msg - 1 *)
    (Sreturn None).

Definition secret_main : function :=
  {|
    fn_return := tvoid;
    fn_callconv := cc_default;
    fn_params := [];
    fn_temps := [];
    fn_vars := [];
    fn_body := secret_main_body;
  |}.

Program Definition secret_program : Clight.program :=
  {|
    prog_defs := [ (secret_main_id, Gfun (Internal secret_main));
                   (secret_msg_id, Gvar msg_globvar);
                   (secret_write_id, Gfun write)
    ];
    prog_public := [ secret_main_id ];
    prog_main := Some secret_main_id;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.

Section INIT_C.
  Context (prog: program).
  Let sk := erase_program prog.
  Section WITH_SE.

    Context (se: Genv.symtbl).
    Let ge := Genv.globalenv se prog.
    Inductive init_c_initial_state (q: query li_wp) : option int -> Prop :=
    | init_c_initial_state_intro: init_c_initial_state q None.
    Inductive init_c_at_external: option int -> query li_c -> Prop :=
    | init_c_at_external_intro vf m f main:
      Genv.init_mem sk = Some m ->
      Genv.find_funct ge vf = Some f ->
      prog_main prog = Some main ->
      (prog_defmap prog) ! main = Some (Gfun f) ->
      init_c_at_external None (cq vf main_sig [] m).
    Inductive init_c_after_external: option int -> reply li_c -> option int -> Prop :=
    | init_c_after_external_intro i m:
      init_c_after_external None (cr (Vint i) m) (Some i).
    Inductive init_c_final_state: option int -> reply li_wp -> Prop :=
    | inic_c_final_state_intro i: init_c_final_state (Some i) i.

  End WITH_SE.
  Program Definition init_c: semantics li_c li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := init_c_initial_state;
          Smallstep.at_external := init_c_at_external se;
          Smallstep.after_external := init_c_after_external;
          Smallstep.final_state := init_c_final_state;
          Smallstep.globalenv := Genv.globalenv se prog;
        |};
      skel := sk;
      footprint i := False
    |}.
End INIT_C.

Definition with_ (liA liB: language_interface): language_interface :=
  {|
    query := sum (query liA) (query liB);
    reply := sum (reply liA) (reply liB);
    entry := fun q => match q with
                  | inl qA => entry qA
                  | inr qB => entry qB
                  end;
  |}.
Infix "+" := with_ (at level 50, left associativity).

Variant sys_query :=
  | write_query: list byte -> sys_query
  | read_query: int -> sys_query.

Variant sys_reply :=
  | write_reply: int -> sys_reply
  | read_reply: list byte -> sys_reply.

Definition li_sys :=
  {|
    query := sys_query;
    reply := sys_reply;
    entry q := Vundef;
  |}.

Section SYS.
  Context (prog: program).
  Let sk := erase_program prog.
  Section WITH_SE.
    Context (se: Genv.symtbl).
    Let ge := globalenv se prog.
    Variant sys_state :=
      | sys_read_query (n: int) (b: block) (ofs: ptrofs) (m: mem)
      | sys_read_reply (bytes: list byte) (b: block) (ofs: ptrofs) (m: mem)
      | sys_write_query (bytes: list byte) (m: mem)
      | sys_write_reply (n: int) (m: mem).

    Inductive sys_c_initial_state: query li_c -> sys_state -> Prop :=
    | sys_c_initial_state_read vf args m n b ofs:
      Genv.find_funct ge vf = Some write ->
      args = [ Vint (Int.repr 0); Vptr b ofs; Vint n ] ->
      sys_c_initial_state (cq vf write_sig args m) (sys_read_query n b ofs m)
    | sys_c_initial_state_write vf args m bytes bytes_val b ofs len:
      Genv.find_funct ge vf = Some read ->
      args = [ Vint (Int.repr 1); Vptr b ofs; Vint (Int.repr len) ] ->
      Mem.loadbytes m b (Ptrofs.unsigned ofs) len = Some bytes_val ->
      map Byte bytes = bytes_val ->
      sys_c_initial_state (cq vf read_sig args m) (sys_write_query bytes m).

    Inductive sys_c_at_external: sys_state -> query (li_sys + li_sys) -> Prop :=
    | sys_c_at_external_read n b ofs m:
      sys_c_at_external (sys_read_query n b ofs m) (inl (read_query n))
    | sys_c_at_external_write bytes m:
      sys_c_at_external (sys_write_query bytes m) (inr (write_query bytes)).

    Inductive sys_c_after_external: sys_state -> reply (li_sys + li_sys) -> sys_state -> Prop :=
    | sys_c_after_external_read n b ofs m bytes:
      sys_c_after_external (sys_read_query n b ofs m) (inl (read_reply bytes)) (sys_read_reply bytes b ofs m)
    | sys_c_after_external_write n m bytes:
      sys_c_after_external (sys_write_query bytes m) (inr (write_reply n)) (sys_write_reply n m).

    Inductive sys_c_final_state: sys_state -> reply li_c -> Prop :=
    | sys_c_final_state_read bytes b ofs bytes_val m len:
      len = Z.of_nat (length bytes) ->
      Mem.loadbytes m b (Ptrofs.unsigned ofs) len = Some bytes_val ->
      map Byte bytes = bytes_val ->
      sys_c_final_state (sys_read_reply bytes b ofs m) (cr (Vint (Int.repr len)) m)
    | sys_c_final_state_write n m:
      sys_c_final_state (sys_write_reply n m) (cr (Vint n) m).

  End WITH_SE.
  Definition sys_c: semantics (li_sys + li_sys) li_c :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := sys_c_initial_state se;
          Smallstep.at_external := sys_c_at_external;
          Smallstep.after_external := sys_c_after_external;
          Smallstep.final_state := sys_c_final_state;
          Smallstep.globalenv := Genv.globalenv se prog;
        |};
      skel := sk;
      footprint i := False
    |}.

End SYS.

Require Import CategoricalComp.

Definition load_c (prog: program) : semantics (li_sys + li_sys) li_wp :=
  let sk := AST.erase_program prog in
  comp_semantics' (init_c prog)
    (comp_semantics' (semantics2 prog) (sys_c prog) sk) sk.

Definition secret_c : semantics (li_sys + li_sys) li_wp := load_c secret_program.

Section SECRET_SPEC.

  Inductive secret_spec_initial_state: query li_wp -> option int -> Prop :=
  | secret_spec_initial_state_intro q: secret_spec_initial_state q None.
  Inductive secret_spec_at_external: option int -> query (li_sys + li_sys) -> Prop :=
  | secret_spec_at_external_intro bytes:
    bytes = urbby_bytes ->
    secret_spec_at_external None (inr (write_query bytes)).
  Inductive secret_spec_after_external: option int -> reply (li_sys + li_sys) -> option int -> Prop :=
  | secret_spec_after_external_intro n:
    secret_spec_after_external None (inr (write_reply n)) (Some n).
  Inductive secret_spec_final_state: option int -> reply li_wp -> Prop :=
  | secret_spec_final_state_intro n: secret_spec_final_state (Some n) n.

  Definition secret_spec: semantics (li_sys + li_sys) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := secret_spec_initial_state;
          Smallstep.at_external := secret_spec_at_external;
          Smallstep.after_external := secret_spec_after_external;
          Smallstep.final_state := secret_spec_final_state;
          Smallstep.globalenv := tt;

        |};
      skel := AST.erase_program secret_program;
      footprint i := False;
    |}.

End SECRET_SPEC.

Section SECRET_FSIM.

  Lemma secret_fsim: forward_simulation 1 1 secret_spec secret_c.
  Admitted.

End SECRET_FSIM.

Definition rot13_program : program.
Admitted.

Definition rot13_c : semantics (li_sys + li_sys) li_wp := load_c rot13_program.

Section ROT13_SPEC.

  Variant rot13_state :=
  | rot13_read | rot13_write (bytes: list byte) | rot13_ret (n: int).

  Inductive rot13_spec_initial_state: query li_wp -> rot13_state -> Prop :=
  | rot13_spec_initial_state_intro q: rot13_spec_initial_state q rot13_read.
  Inductive rot13_spec_at_external: rot13_state -> query (li_sys + li_sys) -> Prop :=
  | rot13_spec_at_external_read:
    rot13_spec_at_external rot13_read (inl (read_query (Int.repr 5)))
  | rot13_spec_at_external_write bytes:
    rot13_spec_at_external (rot13_write bytes) (inr (write_query bytes)).
  Inductive rot13_spec_after_external: rot13_state -> reply (li_sys + li_sys) -> rot13_state -> Prop :=
  | rot13_spec_after_external_read bytes bytes':
    bytes' = rot13_bytes bytes ->
    rot13_spec_after_external rot13_read (inl (read_reply bytes)) (rot13_write bytes')
  | rot13_spec_after_external_write bytes n:
    rot13_spec_after_external (rot13_write bytes) (inr (write_reply n)) (rot13_ret n).
  Inductive rot13_spec_final_state: rot13_state -> reply li_wp -> Prop :=
  | rot13_spec_final_state_intro n: rot13_spec_final_state (rot13_ret n) n.

  Definition rot13_spec: semantics (li_sys + li_sys) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := rot13_spec_initial_state;
          Smallstep.at_external := rot13_spec_at_external;
          Smallstep.after_external := rot13_spec_after_external;
          Smallstep.final_state := rot13_spec_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := AST.erase_program rot13_program;
      footprint i := False;
    |}.

End ROT13_SPEC.

Section ROT13_FSIM.

  Lemma rot13_fsim: forward_simulation 1 1 rot13_spec rot13_c.
  Admitted.

End ROT13_FSIM.

Definition empty_skel: AST.program unit unit :=
  {|
    AST.prog_defs := [];
    AST.prog_public := [];
    AST.prog_main := None;
  |}.

Section SEQ.

  Variant seq_state := | seq1 | seq2 | ret (n: int).
  Inductive seq_initial_state: query li_wp -> seq_state -> Prop :=
  | seq_initial_state_intro q: seq_initial_state q seq1.
  Inductive seq_at_external: seq_state -> query (li_wp + li_wp) -> Prop :=
  | seq_at_external1: seq_at_external seq1 (inl tt)
  | seq_at_external2: seq_at_external seq2 (inr tt).
  Inductive seq_after_external: seq_state -> reply (li_wp + li_wp) -> seq_state -> Prop :=
  | seq_after_external1 n: seq_after_external seq1 (inl n) seq2
  | seq_after_external2 n: seq_after_external seq2 (inr n) (ret n).
  Inductive seq_final_state: seq_state -> reply li_wp -> Prop :=
  | seq_final_state_intro n: seq_final_state (ret n) n.

  Definition seq: semantics (li_wp + li_wp) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := seq_initial_state;
          Smallstep.at_external := seq_at_external;
          Smallstep.after_external := seq_after_external;
          Smallstep.final_state := seq_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := empty_skel;
      footprint i := False;
    |}.

End SEQ.

Section WITH.
  Context {liA1 liA2 liB1 liB2}
    (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
  Section WITH_SE.
    Context (se: Genv.symtbl).
    Definition with_state := (Smallstep.state L1 + Smallstep.state L2)%type.
    Inductive with_initial_state: query (liB1 + liB2) -> with_state -> Prop :=
    | with_initial_state1 q s:
      Smallstep.initial_state (L1 se) q s ->
      with_initial_state (inl q) (inl s)
    | with_initial_state2 q s:
      Smallstep.initial_state (L2 se) q s ->
      with_initial_state (inr q) (inr s).
    Inductive with_at_external: with_state -> query (liA1 + liA2) -> Prop :=
    | with_at_external1 s q:
      Smallstep.at_external (L1 se) s q ->
      with_at_external (inl s) (inl q)
    | with_at_external2 s q:
      Smallstep.at_external (L2 se) s q ->
      with_at_external (inr s) (inr q).
    Inductive with_after_external: with_state -> reply (liA1 + liA2) -> with_state -> Prop :=
    | with_after_external1 s r s':
      Smallstep.after_external (L1 se) s r s' ->
      with_after_external (inl s) (inl r) (inl s')
    | with_after_external2 s r s':
      Smallstep.after_external (L2 se) s r s' ->
      with_after_external (inr s) (inr r) (inr s').
    Inductive with_final_state: with_state -> reply (liB1 + liB2) -> Prop :=
    | with_final_state1 s r:
      Smallstep.final_state (L1 se) s r ->
      with_final_state (inl s) (inl r)
    | with_final_state2 s r:
      Smallstep.final_state (L2 se) s r ->
      with_final_state (inr s) (inr r).
    Inductive with_step: with_state -> trace -> with_state -> Prop :=
    | with_step1 s1 s1' t:
      Step (L1 se) s1 t s1' -> with_step (inl s1) t (inl s1')
    | with_step2 s2 s2' t:
      Step (L2 se) s2 t s2' -> with_step (inr s2) t (inr s2').

  End WITH_SE.

  Definition with_semantics: semantics (liA1 + liA2) (liB1 + liB2) :=
    {|
      activate se :=
        {|
          Smallstep.step := with_step;
          Smallstep.initial_state := with_initial_state se;
          Smallstep.at_external := with_at_external se;
          Smallstep.after_external := with_after_external se;
          Smallstep.final_state := with_final_state se;
          Smallstep.globalenv := se;
        |};
      skel := empty_skel;
      footprint i := False;
    |}.

End WITH.

Require Import Lifting Encapsulation.

Section PIPE.

  Definition pipe_state := list byte.
  Definition pipe_in := (((li_sys + li_sys) + (li_sys + li_sys)) @ pipe_state)%li.
  Definition encap_pipe_in := ((li_sys + li_sys) + (li_sys + li_sys))%li.
  Definition pipe_out := (li_sys + li_sys)%li.
  Variant pipe_internal_state :=
    | pipe1_read_query (n: int) (s: pipe_state)
    | pipe1_read_reply (bytes: list byte) (s: pipe_state)
    | pipe1_write (bytes: list byte) (s: pipe_state)
    | pipe2_read (n: int) (s: pipe_state)
    | pipe2_write_query (bytes: list byte) (s: pipe_state)
    | pipe2_write_reply (n: int) (s: pipe_state).

  Inductive pipe_initial_state: query pipe_in -> pipe_internal_state -> Prop :=
  | pipe_initial_state1 n s:
    pipe_initial_state (inl (inl (read_query n)), s) (pipe1_read_query n s)
  | pipe_initial_state2 bytes s:
    pipe_initial_state (inl (inr (write_query bytes)), s) (pipe1_write bytes s)
  | pipe_initial_state3 n s:
    pipe_initial_state (inr (inl (read_query n)), s) (pipe2_read n s)
  | pipe_initial_state4 bytes s:
    pipe_initial_state (inr (inr (write_query bytes)), s) (pipe2_write_query bytes s).
  Inductive pipe_at_external: pipe_internal_state -> query pipe_out -> Prop :=
  | pipe_at_external1 n s:
    pipe_at_external (pipe1_read_query n s) (inl (read_query n))
  | pipe_at_external2 bytes s:
    pipe_at_external (pipe2_write_query bytes s) (inr (write_query bytes)).
  Inductive pipe_after_external: pipe_internal_state -> reply pipe_out -> pipe_internal_state -> Prop :=
  | pipe_after_external1 bytes n s:
    pipe_after_external (pipe1_read_query n s) (inl (read_reply bytes)) (pipe1_read_reply bytes s)
  | pipe_after_external2 n bytes s:
    pipe_after_external (pipe2_write_query bytes s) (inr (write_reply n)) (pipe2_write_reply n s).
  Inductive pipe_final_state: pipe_internal_state -> reply pipe_in -> Prop :=
  | pipe_final_state1 bytes s:
    pipe_final_state (pipe1_read_reply bytes s) ((inl (inl (read_reply bytes))), s)
  | pipe_final_state2 n bytes s:
    n = Int.repr (Z.of_nat (length bytes)) ->
    pipe_final_state (pipe1_write bytes s) ((inl (inr (write_reply n)), bytes ++ s))
  | pipe_final_state3 n s s' bytes:
    s = bytes ++ s' ->
    n = Int.repr (Z.of_nat (length bytes)) ->
    pipe_final_state (pipe2_read n s) ((inr (inl (read_reply bytes)), s'))
  | pipe_final_state4 n s:
    pipe_final_state (pipe2_write_reply n s) ((inr (inr (write_reply n)), s)).

  Definition pipe_operator: semantics pipe_out pipe_in :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := pipe_initial_state;
          Smallstep.at_external := pipe_at_external;
          Smallstep.after_external := pipe_after_external;
          Smallstep.final_state := pipe_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := empty_skel;
      footprint i := False;
    |}.

  Instance pset_pipe_state : PSet pipe_state :=
    { pset_init _ := [] }.

  Definition encap_pipe_operator: pipe_out +-> encap_pipe_in :=
    {|
      pstate := pipe_state;
      esem := pipe_operator;
    |}.

End PIPE.

Definition hello_skel: AST.program unit unit. Admitted.

Definition pipe (L1 L2: semantics (li_sys + li_sys) li_wp) sk: (li_sys + li_sys) +-> li_wp :=
  comp_esem'
    (semantics_embed (comp_semantics' seq (with_semantics L1 L2) sk))
    encap_pipe_operator sk.

Section HELLO_SPEC.

  (* The redundant internal step makes the simulation easier. *)
  Variant hello_state :=
    | hello1 | hello2 | hello3 (n: int) | hello4 (n: int).
  Inductive hello_spec_initial_state: query li_wp -> hello_state -> Prop :=
  | hello_spec_initial_state_intro q: hello_spec_initial_state q hello1.
  Inductive hello_spec_at_external: hello_state -> query (li_sys + li_sys) -> Prop :=
  | hello_spec_at_external_intro bytes:
    bytes = [ Byte.repr 104; Byte.repr 101; Byte.repr 108; Byte.repr 108; Byte.repr 111 ] ->
    hello_spec_at_external hello2 (inr (write_query bytes)).
  Inductive hello_spec_after_external: hello_state -> reply (li_sys + li_sys) -> hello_state -> Prop :=
  | hello_spec_after_external_intro n:
    hello_spec_after_external hello2 (inr (write_reply n)) (hello3 n).
  Inductive hello_spec_final_state: hello_state -> reply li_wp -> Prop :=
  | hello_spec_final_state_intro n: hello_spec_final_state (hello4 n) n.
  Inductive hello_spec_step: hello_state -> trace -> hello_state -> Prop :=
  | hello_spec_step1: hello_spec_step hello1 E0 hello2
  | hello_spec_step2 n: hello_spec_step (hello3 n) E0 (hello4 n).

  Definition hello_spec: semantics (li_sys + li_sys) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ := hello_spec_step;
          Smallstep.initial_state := hello_spec_initial_state;
          Smallstep.at_external := hello_spec_at_external;
          Smallstep.after_external := hello_spec_after_external;
          Smallstep.final_state := hello_spec_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := hello_skel;
      footprint i := False;
    |}.
  Definition encap_hello_spec: li_sys + li_sys +-> li_wp := semantics_embed hello_spec.

End HELLO_SPEC.

Section PIPE_CORRECT.

  Notation L1 :=
        (TensorComp.semantics_map (comp_semantics' seq (with_semantics secret_spec rot13_spec) hello_skel)
           TensorComp.lf (TensorComp.li_iso_inv TensorComp.li_iso_unit) @ pipe_state)%lts.

(* Lemma x: *)
(*   comp_state *)
(*     (TensorComp.semantics_map (comp_semantics' seq (with_semantics secret_spec rot13_spec) empty_skel) *)
(*        TensorComp.lf (TensorComp.li_iso_inv TensorComp.li_iso_unit) @ pipe_state) pipe_operator. *)
(* Proof. *)
(*   refine (st2 L1 pipe_operator _ _). cbn. *)
(*   refine (st2 _ _ _ _). cbn. split. *)
(*   refine (st1 _ _ _, _). cbn. *)
(*   refine seq1. refine []. *)
(* Defined. *)


  Inductive pipe_match_state: hello_state -> Smallstep.state (pipe secret_spec rot13_spec hello_skel) -> Prop :=
  | pipe_match_state1 buf:
    pipe_match_state hello1
      (st1 L1 pipe_operator (st1 seq (with_semantics secret_spec rot13_spec) seq1, buf))
  | pipe_match_state2 buf:
    pipe_match_state hello2
      (st2 L1 pipe_operator
         (st2 seq (with_semantics secret_spec rot13_spec) seq2 (inr (rot13_write hello_bytes)), buf)
         (pipe2_write_query hello_bytes buf))
  | pipe_match_state3 buf n:
    pipe_match_state (hello3 n)
      (st2 L1 pipe_operator
         (st2 seq (with_semantics secret_spec rot13_spec) seq2 (inr (rot13_write hello_bytes)), buf)
         (pipe2_write_reply n buf))
  | pipe_match_state4 n buf:
    pipe_match_state (hello4 n)
      (st1 L1 pipe_operator (st1 seq (with_semantics secret_spec rot13_spec) (ret n), buf)).

  Ltac step1 := eapply star_left with (t1 := E0) (t2 := E0); [ | | reflexivity ].
  Local Opaque app.

  Lemma pipe_spec_correct: E.forward_simulation &1 &1 encap_hello_spec (pipe secret_spec rot13_spec hello_skel).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
          (ltof _ (fun (_: unit) => 0%nat))
          (fun _se1 _se2 _wb _sa _sb _i s1 s2 => pipe_match_state s1 s2)
          (fun _ _ => True);
          try easy. intros; cbn. firstorder.
    intros. constructor.
    - intros. cbn in *. eprod_crush. inv H4.
      eexists tt, (st1 L1 _ (_, _)). split. repeat constructor; eauto.
      eexists tt, (tt, (tt, (tt, p0))). split; repeat constructor; eauto.
    - intros. cbn in *. eprod_crush. inv H3. inv H2.
      exists (i0, (tt, buf)). split.
      * exists (i0, tt, buf). split; repeat constructor; eauto.
        cbn. exists i0. split; repeat constructor.
      * exists (tt, (tt, (tt, buf))). split; repeat constructor; eauto.
    - intros. cbn in *. eprod_crush. inv H3. unfold id in H5. subst. inv H2.
      exists (inr (write_query hello_bytes)). split.
      * repeat constructor.
      * exists tt, tt. repeat split; eauto.
        destruct H3 as (r' & Hr1 & Hr2). unfold id in Hr1. subst. inv Hr2.
        exists (st2 L1 pipe_operator
             (st2 seq (with_semantics secret_spec rot13_spec) seq2 (inr (rot13_write hello_bytes)), buf)
             (pipe2_write_reply n buf)). split.
        -- exists (inr (write_reply n)). split; eauto. repeat constructor.
        -- exists tt, (tt, (tt, (tt, buf))). split; repeat constructor.
    - intros. cbn in *. eprod_crush. exists tt. inv H2; inv H3.
      * eexists (st2 L1 pipe_operator
                   (st2 seq (with_semantics secret_spec rot13_spec) seq2 (inr (rot13_write hello_bytes)), buf)
                   (pipe2_write_query hello_bytes buf)).
        split.
        -- left. eapply plus_left. (* seq calls secret *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_push; repeat constructor. }
           2: { instantiate (1 := E0). reflexivity. }
           step1. (* secret calls write to pipe *)
           { eapply step_push.
             instantiate (1 := (_, _)). repeat constructor. constructor. }
           step1. (* pipe returns to secret *)
           { eapply step_pop. repeat constructor.
             instantiate (1 := (_, _)). repeat constructor; cbn.
             eexists. split; eauto. reflexivity.
             repeat constructor. }
           step1. (* secret returns to seq *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_pop; repeat constructor. }
           step1. (* seq calls rot13 *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_push; repeat constructor. }
           step1. (* rot13 calls read to pipe *)
           { eapply step_push.
             instantiate (1 := (_, _)). repeat constructor. constructor. }
           step1. (* pipe returns to rot13 *)
           { eapply step_pop. repeat constructor.
             instantiate (1 := (_, _)). repeat constructor; cbn.
             eexists. split; eauto. reflexivity.
             repeat constructor. }
           step1. (* rot13 calls write to pipe *)
           { eapply step_push.
             instantiate (1 := (_, _)). repeat constructor. constructor. }
           rewrite rot13_bytes_urbby. apply star_refl.
        -- exists tt, (tt, (tt, (tt, buf))). split; repeat constructor.
      * exists (st1 L1 pipe_operator (st1 seq (with_semantics secret_spec rot13_spec) (ret n), buf)).
        split.
        -- left. eapply plus_left. (* pipe returns to rot13 *)
           { eapply step_pop. repeat constructor.
             instantiate (1 := (_, _)). repeat constructor; cbn.
             eexists. split; eauto. reflexivity.
             repeat constructor. }
           2: { instantiate (1 := E0). reflexivity. }
           step1. (* rot13 returns to seq *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_pop; repeat constructor. }
           apply star_refl.
        -- exists tt, (tt, (tt, (tt, buf))). split; repeat constructor.
  Qed.

End PIPE_CORRECT.
