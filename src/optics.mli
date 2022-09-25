(**
    Existential optics in OCaml. They are intended as
    both an experiment and for personal use. Feel free
    to use it anyways.

    {2 Main optics}
 *)

module Iso :
  sig
    (** Establishes an isomorphic relation. *)
    type (_, _, _, _) t = Iso : {
      get : 's -> 'a;
      set : 'b -> 't;
    } -> ('s, 't, 'a, 'b) t

    type ('s, 'a) t' = ('s, 's, 'a, 'a) t

    val make : get:('s -> 'a) -> set:('b -> 't) -> ('s, 't, 'a, 'b) t
    (** Build an isomorphism from a pair of inverses. *)

    val make' : get:('s -> 'a) -> set:('a -> 's) -> ('s, 'a) t'
    (** Same as {!make}, but the types are contrainted. *)

    val down : ('s, 't, 'a, 'b) t -> 's -> 'a
    (** Maps a value of type ['s] down to ['a]. *)

    val up : ('s, 't, 'a, 'b) t -> 'b -> 't
    (** Maps a value of type ['b] back to ['t]. *)

    val flip : ('s, 't, 'a, 'b) t -> ('b, 'a, 't, 's) t
    (** Flip an isomorphism. *)

    val iso_map : ('s, 't, 'a, 'b) t -> ('a -> 'b) -> 's -> 't
    (** [iso_map (Iso {get;set}) f s] is the same as [s |> get |> f |> set] *)

    val down_map : ('s, 't, 'a, 'b) t -> ('t -> 's) -> 'b -> 'a
    (** [iso_map (Iso {get;set}) f b] is the same as [b |> set |> f |> get] *)

    val compose :
      ('s, 't, 'a, 'b) t -> ('a, 'b, 'e, 'f) t -> ('s, 't, 'e, 'f) t
  end

module Lens :
  sig
    (** Establishes a relation in which ['s] is subdivided into ['a] and ['c]. *)
    type (_, _, _, _) t = Lens : {
      get : 's -> 'c * 'a;
      set : 'c * 'b -> 't;
    } -> ('s, 't, 'a, 'b) t

    type ('s, 'a) t' = ('s, 's, 'a, 'a) t

    val make :
      get:('a -> 'b * 'c) -> set:('b * 'd -> 'e) -> ('a, 'e, 'c, 'd) t
    (** Build a lens from a pair of functions inversed of each other. *)

    val make' : get:('s -> 'b * 'a) -> set:('b * 'a -> 's) -> ('s, 'a) t'
    (** Same as {!make}, but it restricts the types down to {!type:t'} *)

    val view : ('s, 't, 'a, 'b) t -> 's -> 'a
    (** Extracts the subpart ['a] out of ['s]. *)

    val update : ('s, 't, 'a, 'b) t -> ('a -> 'b) -> 's -> 't
    (** Updates ['a] in ['s] by passing it through a function. This may
        change the types if the lens does not have matching types. *)

    val set : ('s, 't, 'a, 'b) t -> 'b -> 's -> 't
    (** [set lens b s] replaces the inner value in [s] with [b]. *)

    val compose :
      ('a, 'b, 'c, 'd) t -> ('c, 'd, 'e, 'f) t -> ('a, 'b, 'e, 'f) t
  end

module Prism :
  sig
    (** Establishes a relation in which we focus on whether ['s]
        may be an ['a]. *)
    type (_, _, _, _) t = Prism : {
      get : 's -> ('c, 'a) Either.t;
      set : ('c, 'b) Either.t -> 't;
    } -> ('s, 't, 'a, 'b) t

    type ('s, 'a) t' = ('s, 's, 'a, 'a) t

    val make :
      get:('s -> ('c, 'a) Either.t) ->
      set:(('c, 'b) Either.t -> 't) -> ('s, 't, 'a, 'b) t
    (** Build a prism from a pair of functions inversed of each other. *)

    val make' :
      get:('s -> ('b, 'a) Either.t) ->
      set:(('b, 'a) Either.t -> 's) -> ('s, 'a) t'
    (** Same as {!make}, but it restricts the types down to {!type:t'} *)

    val preview : ('s, 't, 'a, 'b) t -> 's -> 'a option
    (** [preview prism s] returns [Some a] in case of success, [None] otherwise. *)

    val review : ('s, 't, 'a, 'b) t -> 'b -> 't
    (** [review prism d] returns [d] transformed back into [t]. *)

    val exists : ('s, 't, 'a, 'b) t -> 's -> bool
    (** [exists s] responds to whether ['a] is ['s] *)

    val isn't : ('a, 'b, 'c, 'd) t -> 'a -> bool
    (** [isn't s] is [not (exists s)] *)

    val compose :
      ('a, 'b, 'c, 'd) t -> ('c, 'd, 'e, 'f) t -> ('a, 'b, 'e, 'f) t
  end

module Affine :
  sig
    (** Establishes a relation in which we focus on part of
        a particular possible case of ['s].  *)
    type (_, _, _, _) t = Affine : {
      get : 's -> ('c1, 'c2 * 'a) Either.t ;
      set : ('c1, 'c2 * 'b) Either.t -> 't;
    } -> ('s, 't, 'a, 'b) t

    type ('s, 'a) t' = ('s, 's, 'a, 'a) t

    val make :
      get:('s -> ('c1, 'c2 * 'a) Either.t) ->
      set:(('c1, 'c2 * 'b) Either.t -> 't) -> ('s, 't, 'a, 'b) t
    (** Build an affine traversal from a pair of functions inversed of each other. *)

    val make' :
      get:('s -> ('c1, 'c2 * 'a) Either.t) ->
      set:(('c1, 'c2 * 'a) Either.t -> 's) -> ('s, 'a) t'
    (** Same as {!make}, but it restricts the types down to {!type:t'} *)

    val preview : ('s, 't, 'a, 'b) t -> 's -> 'a option
    (** [preview affine s] may return [Some a] if it successfully
        extracts it out of [s], None otherwise. *)

    val update : ('s, 't, 'a, 'b) t -> ('a -> 'b) -> 's -> 't
    (** [update affine f s] may update the inner value [a] inside [s]. *)

    val set : ('s, 't, 'a, 'b) t -> 'b -> 's -> 't
    (** [set affine b s] updates the inner value in [s] with [b]. *)

    val exists : ('s, 't, 'a, 'b) t -> 's -> bool
    (** [exists affine s] is the same as [preview affine s |> Option.is_some]. *)

    val isn't : ('s, 't, 'a, 'b) t -> 's -> bool
    (** [isn't affine s] is the same as [not (exists affine s)]. *)

    val compose :
      ('a, 'b, 'c, 'd) t -> ('c, 'd, 'e, 'f) t -> ('a, 'b, 'e, 'f) t
  end

(** Every function in this module has the form of [X_and_Y], in which
    it takes two optics, of types X and Y respectively, and returns
    an optic that is the most simple but compatible combination of them.
  *)
module Compose :
  sig
    val iso_and_lens :
      ('a, 'b, 'c, 'd) Iso.t ->
      ('c, 'd, 'e, 'f) Lens.t -> ('a, 'b, 'e, 'f) Lens.t
    val lens_and_iso :
      ('a, 'b, 'c, 'd) Lens.t ->
      ('c, 'd, 'e, 'f) Iso.t -> ('a, 'b, 'e, 'f) Lens.t
    val iso_and_prism :
      ('a, 'b, 'c, 'd) Iso.t ->
      ('c, 'd, 'e, 'f) Prism.t -> ('a, 'b, 'e, 'f) Prism.t
    val prism_and_iso :
      ('a, 'b, 'c, 'd) Prism.t ->
      ('c, 'd, 'e, 'f) Iso.t -> ('a, 'b, 'e, 'f) Prism.t
    val iso_and_affine :
      ('a, 'b, 'c, 'd) Iso.t ->
      ('c, 'd, 'e, 'f) Affine.t -> ('a, 'b, 'e, 'f) Affine.t
    val affine_and_iso :
      ('a, 'b, 'c, 'd) Affine.t ->
      ('c, 'd, 'e, 'f) Iso.t -> ('a, 'b, 'e, 'f) Affine.t
    val lens_and_prism :
      ('a, 'b, 'c, 'd) Lens.t ->
      ('c, 'd, 'e, 'f) Prism.t -> ('a, 'b, 'e, 'f) Affine.t
    val prism_and_lens :
      ('a, 'b, 'c, 'd) Prism.t ->
      ('c, 'd, 'e, 'f) Lens.t -> ('a, 'b, 'e, 'f) Affine.t
    val affine_and_lens :
      ('a, 'b, 'c, 'd) Affine.t ->
      ('c, 'd, 'e, 'f) Lens.t -> ('a, 'b, 'e, 'f) Affine.t
    val affine_and_prism :
      ('a, 'b, 'c, 'd) Affine.t ->
      ('c, 'd, 'e, 'f) Prism.t -> ('a, 'b, 'e, 'f) Affine.t
    val lens_and_affine :
      ('a, 'b, 'c, 'd) Lens.t ->
      ('c, 'd, 'e, 'f) Affine.t -> ('a, 'b, 'e, 'f) Affine.t
    val prism_and_affine :
      ('a, 'b, 'c, 'd) Prism.t ->
      ('c, 'd, 'e, 'f) Affine.t -> ('a, 'b, 'e, 'f) Affine.t
  end

(**
    {2 Exported optics}

    Each optic has two versions - one with a same-type restriction
    in which modifications over the focused part must not change the
    inner type; and the version in which there's no such restriction.
  *)

type ('s, 't, 'a, 'b) iso = ('s, 't, 'a, 'b) Iso.t
(** Establishes an isomorphic relation. *)

type ('s, 't, 'a, 'b) lens = ('s, 't, 'a, 'b) Lens.t
(** Establishes a relation in which ['s] is subdivided into ['a] and ['c]. *)

type ('s, 't, 'a, 'b) prism = ('s, 't, 'a, 'b) Prism.t
(** Establishes a relation in which we focus on whether ['s]
    may be an ['a]. *)

type ('s, 't, 'a, 'b) affine = ('s, 't, 'a, 'b) Affine.t
(** Establishes a relation in which we focus on part of
    a particular possible case of ['s].  *)

type ('s, 'a) iso' = ('s, 'a) Iso.t'
type ('s, 'a) lens' = ('s, 'a) Lens.t'
type ('s, 'a) prism' = ('s, 'a) Prism.t'
type ('s, 'a) affine' = ('s, 'a) Affine.t'

(**
    {2 Composition aliases}

    The following functions act as aliases for the composition
    functions inside {!Compose} and the other modules.

    They all have the same naming and usage convention.
    [XY Y' X'] builds a new optic by composition of [X'] and [Y'],
    where [X] and [Y] are letters which are the first letter of
    a type of optic ([i] = {!iso}, [l] = {!lens}, [p] = {!prism}
    and [a] = {!affine}), while [X'] and [Y'] are the types suggested
    by [X] and [Y].

    Do notice how the arguments are inverted. The intended usage is to
    apply these functions in a pipeline, i.e. [some_lens |> lp some_prism |> ai some_iso].
    By inverting them, the aliases' naming convention coincide with
    what they take from the left and the right in a pipeline.
  *)

val ii :
  ('a, 'b, 'c, 'd) iso ->
  ('e, 'f, 'a, 'b) iso -> ('e, 'f, 'c, 'd) iso
val il :
  ('a, 'b, 'c, 'd) lens ->
  ('e, 'f, 'a, 'b) iso -> ('e, 'f, 'c, 'd) lens
val ip :
  ('a, 'b, 'c, 'd) prism ->
  ('e, 'f, 'a, 'b) iso -> ('e, 'f, 'c, 'd) prism
val ia :
  ('a, 'b, 'c, 'd) affine ->
  ('e, 'f, 'a, 'b) iso -> ('e, 'f, 'c, 'd) affine
val li :
  ('a, 'b, 'c, 'd) iso ->
  ('e, 'f, 'a, 'b) lens -> ('e, 'f, 'c, 'd) lens
val pi :
  ('a, 'b, 'c, 'd) iso ->
  ('e, 'f, 'a, 'b) prism -> ('e, 'f, 'c, 'd) prism
val ai :
  ('a, 'b, 'c, 'd) iso ->
  ('e, 'f, 'a, 'b) affine -> ('e, 'f, 'c, 'd) affine
val ll :
  ('a, 'b, 'c, 'd) lens ->
  ('e, 'f, 'a, 'b) lens -> ('e, 'f, 'c, 'd) lens
val pp :
  ('a, 'b, 'c, 'd) prism ->
  ('e, 'f, 'a, 'b) prism -> ('e, 'f, 'c, 'd) prism
val lp :
  ('a, 'b, 'c, 'd) prism ->
  ('e, 'f, 'a, 'b) lens -> ('e, 'f, 'c, 'd) affine
val pl :
  ('a, 'b, 'c, 'd) lens ->
  ('e, 'f, 'a, 'b) prism -> ('e, 'f, 'c, 'd) affine
val aa :
  ('a, 'b, 'c, 'd) affine ->
  ('e, 'f, 'a, 'b) affine -> ('e, 'f, 'c, 'd) affine
val al :
  ('a, 'b, 'c, 'd) lens ->
  ('e, 'f, 'a, 'b) affine -> ('e, 'f, 'c, 'd) affine
val ap :
  ('a, 'b, 'c, 'd) prism ->
  ('e, 'f, 'a, 'b) affine -> ('e, 'f, 'c, 'd) affine
val la :
  ('a, 'b, 'c, 'd) affine ->
  ('e, 'f, 'a, 'b) lens -> ('e, 'f, 'c, 'd) affine
val pa :
  ('a, 'b, 'c, 'd) affine ->
  ('e, 'f, 'a, 'b) prism -> ('e, 'f, 'c, 'd) affine

(** {2 Function aliases} *)

val down : ('s, 't, 'a, 'b) iso -> 's -> 'a
(** Same as {!Iso.down}. *)

val up : ('s, 't, 'a, 'b) iso -> 'b -> 't
(** Same as {!Iso.up}. *)

val view : ('s, 't, 'a, 'b) lens -> 's -> 'a
(** Same as {!Lens.view}. *)

val update : ('s, 't, 'a, 'b) lens -> ('a -> 'b) -> 's -> 't
(** Same as {!Lens.update}. *)

val set : ('s, 't, 'a, 'b) lens -> 'b -> 's -> 't
(** Same as {!Lens.set}. *)

val preview : ('s, 't, 'a, 'b) prism -> 's -> 'a option
(** Same as {!Prism.preview}. *)

val review : ('s, 't, 'a, 'b) prism -> 'b -> 't
(** Same as {!Prism.review}. *)

val preview' : ('s, 't, 'a, 'b) affine -> 's -> 'a option
(** Same as {!Affine.preview}. *)

val update' : ('s, 't, 'a, 'b) affine -> ('a -> 'b) -> 's -> 't
(** Same as {!Affine.update}. *)

val set' : ('s, 't, 'a, 'b) affine -> 'b -> 's -> 't
(** Same as {!Affine.set}. *)

(**
    {2 Generic builtin optics}

    Because of OCaml's value restrictions, optics
    need to be instantiated right when they're intended for
    usage, which is why they're all functions.
  *)

val _1 : unit -> ('a * 'b, 'a) lens'
(** A {!lens} over the first element of a 2-tuple. *)

val _2 : unit -> ('a * 'b, 'b) lens'
(** A {!lens} over the second element of a 2-tuple. *)

val _right : unit -> (('a, 'b) Either.t, 'b) prism'
(** A {!prism} over the right value of an [either] value. *)

val _left : unit -> (('a, 'b) Either.t, 'a) prism'
(** A {!prism} over the left value of an [either] value. *)

val _hd : unit -> ('a list, 'a) affine'
(** An {!affine} over the head of a list. *)

val _tl : unit -> ('a list, 'a list) affine'
(** An {!affine} over the tail of a list. *)
