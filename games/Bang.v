Require Import LogicalRelations.
Require Import List.
Require Import RTS.


Delimit Scope game_scope with game.
Bind Scope game_scope with game.

Definition garrow (GA GB : game) : game :=
  {|
    input := output GA + input GB;
    output := input GA + output GB;
  |}.

Infix "-o" := garrow (at level 55, right associativity) : game_scope.


(** * The bang game *)

(** The game [!G] consists of a finite number of copies of [G]. Both
  participants can spawn a new copy on-the-fly, or play in one of the
  already existing copies. Each move is annotated with a [nat]
  label. The label [O] causes a new copy of the game to be spawned,
  whereas the label [S n] directs the move to the [n]th most recently
  created copy.

  This scheme means that we can use a simple [list] to keep track of a
  state for each copy; see for instance the definition of the [mux]
  relations below. When a new copy is created the new state can simply
  be [cons]ed onto the existing list, and we can use [nth] to query
  the list for the state associated with a given label. In the rare
  instances where a stable identifier is needed, we can count from the
  end of the list and access the corresponding multiplexed state at
  [nth i (rev l)].

  Another advantage is that embedding CompCert semantics that perform
  a flat, well-parenthesized sequence of call-return interactions as
  external calls is extremely straightforward: each new call will be
  annotated with [0], and each return will be expected to carry a [1]
  annotation. In fact, when manipulating embedded CompCert semantics,
  [0,1] will be the only labels of interest, since any other ones will
  correspond to computations that have already concluded. In
  multiplexed state lists, the head corresponds to the currently
  active state, whereas the tail can be safely ignored. *)

Definition gbang (G : game) :=
  {|
    input := nat * input G;
    output := nat * output G;
  |}.

Notation "! G" := (gbang G) (at level 35) : game_scope.

(** ** Mux relation *)

(** When manipulating strategies involving games of the form [!G], we
  often need to multiplex an interaction so that the different copies
  of [G] are assigned to different channels. For instance, in the
  definition of flat composition the channel will fan out the the
  different modules that are being composed; in the resolution
  operator the two channels will correspond to interactions being
  passed to the environment vs. those that are looped back into the
  strategy itself.

  To facilitate this, we introduce the [mux] relation, which will
  match the possible moves in the multiplexed interaction to
  corresponding possible moves in a given channel. The channels are
  indexed by a type [I], and we maintain a table of type [list I]
  which associates a channel to each active copy in the multiplexed
  interaction. *)

(** *** Querying the routing table *)

(** The relation [muxq t i m n] relation asserts that for a routing
  table [t], the copy labeled [m] in the channel [i] corresponds to
  the copy labeled [n] in the multiplexed interaction. *)

Inductive muxq {I} : list I -> I -> nat -> nat -> Prop :=
  | muxq_base i :
      muxq nil i O O
  | muxq_next t i m n :
      muxq t i m n ->
      muxq (i::t) i (S m) (S n)
  | muxq_skip t i j m n :
      i <> j ->
      muxq t i m n ->
      muxq (j::t) i m (S n).

(** *** Single [mux] *)

(** We can now define the [mux] relation as follows. When a new copy
  is created, labels on both sides will be [O] and the channel [i]
  will be prepended to the routing table. Alternatively, we can query
  the routing table and if the multiplexed copy [m] corresponding to
  copy [n] for the channel [i], we can relate [!G] move accordingly. *)

Inductive smux {I A} (t : list I) : list I -> I -> nat * A -> nat * A -> Prop :=
    | smux_new i a :
        smux t (i::t) i (O, a) (O, a)
    | smux_ref i m n a :
        muxq t i m n ->
        smux t t i (S m, a) (S n, a).

(** *** Bilateral [mux] *)

(** In practice, most strategies we will manipulate will be for a game
  of the form [!GA -o !GB]. In such cases, we will likely want to use
  a separate multiplexer for each "side" of the interaction. To handle
  this, our main [mux] relation actually uses two routing tables, and
  will be able to relate the moves of type [nat * A + nat * B]
  resulting from this kind of games. *)

Definition muxtbl {I} : Type := list I * list I.

Inductive mux {I A B} : muxtbl -> muxtbl -> I -> relation (nat * A + nat * B) :=
  | mux_inl ta ta' tb i ai a :
      smux ta ta' i ai a ->
      mux (ta, tb) (ta', tb) i (inl ai) (inl a)
  | mux_inr ta tb tb' i bi b :
      smux tb tb' i bi b ->
      mux (ta, tb) (ta, tb') i (inr bi) (inr b).
