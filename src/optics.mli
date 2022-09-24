(**
    Existential optics in OCaml.

    Intended to be an experiment, but also a simple implementation
    of several optics. Generally, it is recommended to open
    this module wherever it is needed.
 *)

module Iso :
  sig
    type (_, _, _, _) t = Iso : {
      get : 's -> 'a;
      set : 'b -> 't;
    } -> ('s, 't, 'a, 'b) t
    (** Establishes an isomorphic relation. *)

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

    val update : ('s, 'b, 'c, 'd) t -> ('c -> 'd) -> 'a -> 'b
    (** Updates ['a] in ['s] by passing it through a function. This may
        change the types if the lens does not have matching types. *)

    val set : ('s, 't, 'a, 'b) t -> 'b -> 's -> 't
    (** [set lens b s] replaces the inner value in [s] with [b]. *)

    val compose :
      ('a, 'b, 'c, 'd) t -> ('c, 'd, 'e, 'f) t -> ('a, 'b, 'e, 'f) t
  end

module Prism :
  sig
    (** Establishes a relation in which ['s] may be an ['a]. *)
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
    type (_, _, _, _) t = Affine : {
      get : 's -> ('c1, 'c2 * 'a) Either.t ;
      set : ('c1, 'c2 * 'b) Either.t -> 't;
    } -> ('s, 't, 'a, 'b) t

    type ('s, 'a) t' = ('s, 's, 'a, 'a) t
    val make :
      get:('a -> ('b, 'c * 'd) Either.t) ->
      set:(('b, 'c * 'e) Either.t -> 'f) -> ('a, 'f, 'd, 'e) t
    val make' :
      get:('s -> ('b, 'c * 'a) Either.t) ->
      set:(('b, 'c * 'a) Either.t -> 's) -> ('s, 'a) t'
    val preview : ('a, 'b, 'c, 'd) t -> 'a -> 'c option
    val update : ('a, 'b, 'c, 'd) t -> ('c -> 'd) -> 'a -> 'b
    val set : ('a, 'b, 'c, 'd) t -> 'd -> 'a -> 'b
    val exists : ('a, 'b, 'c, 'd) t -> 'a -> bool
    val isn't : ('a, 'b, 'c, 'd) t -> 'a -> bool
    val compose :
      ('a, 'b, 'c, 'd) t -> ('c, 'd, 'e, 'f) t -> ('a, 'b, 'e, 'f) t
  end
type ('s, 't, 'a, 'b) iso = ('s, 't, 'a, 'b) Iso.t
type ('s, 't, 'a, 'b) lens = ('s, 't, 'a, 'b) Lens.t
type ('s, 't, 'a, 'b) prism = ('s, 't, 'a, 'b) Prism.t
type ('s, 't, 'a, 'b) affine = ('s, 't, 'a, 'b) Affine.t
type ('s, 'a) iso' = ('s, 'a) Iso.t'
type ('s, 'a) lens' = ('s, 'a) Lens.t'
type ('s, 'a) prism' = ('s, 'a) Prism.t'
type ('s, 'a) affine' = ('s, 'a) Affine.t'
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

val ( % ) :
  ('a, 'b, 'c, 'd) Lens.t ->
  ('c, 'd, 'e, 'f) Lens.t -> ('a, 'b, 'e, 'f) Lens.t
val ii :
  ('a, 'b, 'c, 'd) Iso.t -> ('e, 'f, 'a, 'b) Iso.t -> ('e, 'f, 'c, 'd) Iso.t
val il :
  ('a, 'b, 'c, 'd) Lens.t ->
  ('e, 'f, 'a, 'b) Iso.t -> ('e, 'f, 'c, 'd) Lens.t
val ip :
  ('a, 'b, 'c, 'd) Prism.t ->
  ('e, 'f, 'a, 'b) Iso.t -> ('e, 'f, 'c, 'd) Prism.t
val ia :
  ('a, 'b, 'c, 'd) Affine.t ->
  ('e, 'f, 'a, 'b) Iso.t -> ('e, 'f, 'c, 'd) Affine.t
val li :
  ('a, 'b, 'c, 'd) Iso.t ->
  ('e, 'f, 'a, 'b) Lens.t -> ('e, 'f, 'c, 'd) Lens.t
val pi :
  ('a, 'b, 'c, 'd) Iso.t ->
  ('e, 'f, 'a, 'b) Prism.t -> ('e, 'f, 'c, 'd) Prism.t
val ai :
  ('a, 'b, 'c, 'd) Iso.t ->
  ('e, 'f, 'a, 'b) Affine.t -> ('e, 'f, 'c, 'd) Affine.t
val ll :
  ('a, 'b, 'c, 'd) Lens.t ->
  ('e, 'f, 'a, 'b) Lens.t -> ('e, 'f, 'c, 'd) Lens.t
val pp :
  ('a, 'b, 'c, 'd) Prism.t ->
  ('e, 'f, 'a, 'b) Prism.t -> ('e, 'f, 'c, 'd) Prism.t
val lp :
  ('a, 'b, 'c, 'd) Prism.t ->
  ('e, 'f, 'a, 'b) Lens.t -> ('e, 'f, 'c, 'd) Affine.t
val pl :
  ('a, 'b, 'c, 'd) Lens.t ->
  ('e, 'f, 'a, 'b) Prism.t -> ('e, 'f, 'c, 'd) Affine.t
val aa :
  ('a, 'b, 'c, 'd) Affine.t ->
  ('e, 'f, 'a, 'b) Affine.t -> ('e, 'f, 'c, 'd) Affine.t
val al :
  ('a, 'b, 'c, 'd) Lens.t ->
  ('e, 'f, 'a, 'b) Affine.t -> ('e, 'f, 'c, 'd) Affine.t
val ap :
  ('a, 'b, 'c, 'd) Prism.t ->
  ('e, 'f, 'a, 'b) Affine.t -> ('e, 'f, 'c, 'd) Affine.t
val la :
  ('a, 'b, 'c, 'd) Affine.t ->
  ('e, 'f, 'a, 'b) Lens.t -> ('e, 'f, 'c, 'd) Affine.t
val pa :
  ('a, 'b, 'c, 'd) Affine.t ->
  ('e, 'f, 'a, 'b) Prism.t -> ('e, 'f, 'c, 'd) Affine.t

val down : ('a, 'b, 'c, 'd) Iso.t -> 'a -> 'c
val up : ('a, 'b, 'c, 'd) Iso.t -> 'd -> 'b
val view : ('a, 'b, 'c, 'd) Lens.t -> 'a -> 'c
val update : ('a, 'b, 'c, 'd) Lens.t -> ('c -> 'd) -> 'a -> 'b
val set : ('a, 'b, 'c, 'd) Lens.t -> 'd -> 'a -> 'b
val preview : ('a, 'b, 'c, 'd) Prism.t -> 'a -> 'c option
val review : ('a, 'b, 'c, 'd) Prism.t -> 'd -> 'b
val preview' : ('a, 'b, 'c, 'd) Affine.t -> 'a -> 'c option
val update' : ('a, 'b, 'c, 'd) Affine.t -> ('c -> 'd) -> 'a -> 'b
val set' : ('a, 'b, 'c, 'd) Affine.t -> 'd -> 'a -> 'b
val _1 : unit -> ('a * 'b, 'a) Lens.t'
val _2 : unit -> ('a * 'b, 'b) Lens.t'
val _right : unit -> (('a, 'b) Either.t, 'b) Prism.t'
val _left : unit -> (('a, 'b) Either.t, 'a) Prism.t'
val _hd : unit -> ('a list, 'a) Affine.t'
val _tl : unit -> ('a list, 'a list) Affine.t'
