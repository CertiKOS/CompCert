Require Import Coqlib Maps AST Linking.
Require Import Integers Floats Values Memory.
Require Import Globalenvs.
Require Import RelationClasses.

Set Implicit Arguments.

Local Set Elimination Schemes.
Local Set Case Analysis Schemes.

Record skel_prop (sk: AST.program unit unit): Prop := {
    public_defined: forall id, In id (prog_public sk) -> AST.has_symbol sk id;
    main_public: In (prog_main sk) (prog_public sk);
  }.

Record skel_le (sk1 sk2: AST.program unit unit): Prop := {
    defmap_le: forall id g, (prog_defmap sk1) ! id = Some g -> (prog_defmap sk2) ! id = Some g;
    defmap_public: forall id g, (prog_defmap sk2)! id = Some g -> In id (prog_public sk2) ->
            (prog_defmap sk1)! id = Some g;
    public_same: prog_public sk2 = prog_public sk1;
    main_same: prog_main sk2 = prog_main sk1;
  }.

Instance skel_le_refl: Reflexive skel_le.
Proof.
  intro sk. split; intros; auto.
Qed.

Instance skel_le_tran: Transitive skel_le.
Proof.
  intros sk1 sk2 sk3 H1 H2. destruct H1. destruct H2.
  split; try congruence; intros; eauto.
  eapply defmap_public0; eauto.
  rewrite <- public_same1; eauto.
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

(* Because public symbols must be preserved, we only care about the static
   symbols. But when [skel_info] is used together with [skel_le], we can infer
   that removed symbols are static. So sometimes we don't separate public and
   static symbols in [skel_info] *)
Inductive skel_info :=
  | Atom (kept: ident -> Prop) (removed: ident -> Prop): skel_info
  | Compose (info1 info2: skel_info): skel_info.

Definition atom_skel_info (sk: AST.program unit unit) :=
  Atom (fun id => AST.has_symbol sk id) (fun _ => False).

Definition skel := AST.program unit unit.

Inductive skel_info_le: skel_info -> skel_info -> Prop :=
  | skel_info_le_atom (kept1 kept2 removed1 removed2: ident -> Prop):
    (forall id, kept1 id -> kept2 id) ->
    (forall id, removed1 id -> removed2 id) ->
    skel_info_le (Atom kept1 removed1) (Atom kept2 removed2)
  | skel_info_le_compose info1 info2 info1' info2':
    skel_info_le info1 info1' ->
    skel_info_le info2 info2' ->
    skel_info_le (Compose info1 info2) (Compose info1' info2').

Instance skel_info_le_refl: Reflexive skel_info_le.
Proof.
  intro skel_info. induction skel_info; constructor; easy.
Qed.

Instance skel_info_le_tran: Transitive skel_info_le.
Proof.
  intros si1 si2 si3 H12 H23.
  revert si3 H23. induction H12.
  - intros. inv H23. constructor; firstorder.
  - intros. inv H23.
    specialize (IHskel_info_le1 _ H1).
    specialize (IHskel_info_le2 _ H3).
    constructor; eauto.
Qed.

Lemma linkorder_skel_info_le sk1 sk2:
  linkorder sk1 sk2 ->
  skel_info_le (atom_skel_info sk1) (atom_skel_info sk2).
Proof.
  intros (Hmain & Hpub & Hdefs). constructor. 2: easy.
  intros id Hid1. unfold has_symbol in *.
  exploit prog_defmap_dom; eauto. intros (g & Hg).
  specialize (Hdefs _ _ Hg) as (g' & Hg' & ? & ?).
  apply in_prog_defmap in Hg'.
  unfold prog_defs_names.
  eapply in_map with (f:=fst) in Hg'. apply Hg'.
Qed.
