Require Import LanguageInterface Smallstep Globalenvs Events.
Require Import List.
Import ListNotations.

Definition empty_skel: AST.program unit unit :=
  {|
    AST.prog_defs := [];
    AST.prog_public := [];
    AST.prog_main := None;
  |}.


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
