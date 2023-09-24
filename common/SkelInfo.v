Require Import Coqlib Maps AST Linking.
Require Import Integers Floats Values Memory.
Require Import Globalenvs.
Require Import RelationClasses.

Set Implicit Arguments.

Local Set Elimination Schemes.
Local Set Case Analysis Schemes.

Definition skel_le (sk1 sk2: AST.program unit unit): Prop :=
  (forall id g, (prog_defmap sk1) ! id = Some g -> (prog_defmap sk2) ! id = Some g)
  /\ (forall id g, (prog_defmap sk2)! id = Some g -> In id (prog_public sk2) ->
             (prog_defmap sk1)! id = Some g)
  /\ (prog_public sk2 = prog_public sk1).

Instance skel_le_refl: Reflexive skel_le.
Proof.
  intro sk. split; intros; auto.
Qed.

Instance skel_le_tran: Transitive skel_le.
Proof.
  intros sk1 sk2 sk3 [H11 [H12 H13]] [H21 [H22 H23]].
  split.
  intros. eauto.
  split.
  intros. eapply H12; eauto. rewrite <- H23. eauto.
  congruence.
Qed.

Record match_stbls' (f: meminj) (ge1: Genv.symtbl) (ge2: Genv.symtbl) := {
  mge_public':
    forall id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id;
  mge_delta:
    forall b1 b2 delta, Plt b1 (Genv.genv_next ge1) ->
    f b1 = Some (b2, delta) ->
    delta = 0;
  mge_img':
    forall b2, Plt b2 (Genv.genv_next ge2) ->
    exists b1, f b1 = Some (b2, 0);
  mge_symb':
    forall b1 b2 delta, f b1 = Some (b2, delta) ->
    forall id, (Genv.genv_symb ge1) ! id = Some b1 <-> (Genv.genv_symb ge2) ! id = Some b2;
  mge_info':
    forall b1 b2 delta, f b1 = Some (b2, delta) ->
    ge1.(Genv.genv_info) ! b1 = ge2.(Genv.genv_info) ! b2;
  mge_separated':
    forall b1 b2 delta, f b1 = Some (b2, delta) ->
    Pos.le (Genv.genv_next ge1) b1 <-> Pos.le (Genv.genv_next ge2) b2;
}.

Inductive match_stbls_static (kept: ident -> Prop) (removed: ident -> Prop)
  (f: meminj) (ge1: Genv.symtbl) (ge2: Genv.symtbl) :=
  {
    global_prop: match_stbls' f ge1 ge2;

    symbols_removed:
      forall id, removed id -> Genv.find_symbol ge2 id = None;
    symbols_kept:
      forall id, kept id -> exists b, Genv.find_symbol ge2 id = Some b;
    symbols_subset:
      forall id, Genv.has_symbol ge2 id -> Genv.has_symbol ge1 id;
  }.

Inductive skel_info :=
  | Atom (kept: ident -> Prop) (removed: ident -> Prop): skel_info
  | Compose (info1 info2: skel_info): skel_info.

Definition atom_skel_info (sk: AST.program unit unit) :=
  Atom (fun id => AST.has_symbol sk id /\ ~ In id sk.(prog_public)) (fun _ => False).

Definition skel := AST.program unit unit.
