module Iso :
  sig
    type ('a, 'b) t = { get : 'a -> 'b; set : 'b -> 'a; }
    val make : get:('a -> 'b) -> set:('b -> 'a) -> ('a, 'b) t
    val down : ('a, 'b) t -> 'a -> 'b
    val up : ('a, 'b) t -> 'b -> 'a
    val flip : ('a, 'b) t -> ('b, 'a) t
    val iso_map : ('a, 'b) t -> ('b -> 'b) -> 'a -> 'a
    val down_map : ('a, 'b) t -> ('a -> 'a) -> 'b -> 'b
    val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
  end

module Lens :
  sig
    type ('s, 'a, 'b) t = { get : 's -> 'b * 'a; set : 'b * 'a -> 's; }
    val make : get:('s -> 'b * 'a) -> set:('b * 'a -> 's) -> ('s, 'a, 'b) t
    val view : ('s, 'a, 'b) t -> 's -> 'a
    val update : ('a, 'b, 'c) t -> ('b -> 'b) -> 'a -> 'a
    val set : ('a, 'b, 'c) t -> 'b -> 'a -> 'a
    val compose :
      ('s1, 's2, 'b1) t -> ('s2, 'a2, 'b2) t -> ('s1, 'a2, 'b1 * 'b2) t
  end

module Prism :
  sig
    type ('s, 'a, 'c) t = {
      get : 's -> ('c, 'a) Either.t;
      set : ('c, 'a) Either.t -> 's;
    }
    val make :
      get:('s -> ('c, 'a) Either.t) ->
      set:(('c, 'a) Either.t -> 's) -> ('s, 'a, 'c) t
    val preview : ('a, 'b, 'c) t -> 'a -> ('c, 'b) Either.t
    val review : ('a, 'b, 'c) t -> 'b -> 'a
    val exists : ('a, 'b, 'c) t -> 'a -> bool
    val isn't : ('a, 'b, 'c) t -> 'a -> bool
    val compose :
      ('s1, 's2, 'b1) t ->
      ('s2, 'a2, 'a2) t -> ('s1, 'a2, ('b1, 'a2) Either.t) t
  end

module Affine :
  sig
    type ('s, 'a, 'b, 'c) t = {
      get : 's -> ('c, 'b * 'a) Either.t;
      set : ('c, 'b * 'a) Either.t -> 's;
    }
    val make :
      get:('s -> ('c, 'b * 'a) Either.t) ->
      set:(('c, 'b * 'a) Either.t -> 's) -> ('s, 'a, 'b, 'c) t
    val preview : ('a, 'b, 'c, 'd) t -> 'a -> ('d, 'b) Either.t
    val update : ('a, 'b, 'c, 'd) t -> ('b -> 'b) -> 'a -> 'a
    val set : ('a, 'b, 'c, 'd) t -> 'b -> 'a -> 'a
    val exists : ('a, 'b, 'c, 'd) t -> 'a -> bool
    val isn't : ('a, 'b, 'c, 'd) t -> 'a -> bool
    val compose :
      ('s1, 's2, 'b1, 'c1) t ->
      ('s2, 'a2, 'b2, 'c2) t ->
      ('s1, 'a2, 'b1 * 'b2, ('c1, 'b1 * 'c2) Either.t) t
  end

type ('s, 'a) iso = ('s, 'a) Iso.t
type ('s, 'a, 'c) lens = ('s, 'a, 'c) Lens.t
type ('s, 'a, 'c) prism = ('s, 'a, 'c) Prism.t
type ('s, 'a, 'b, 'c) affine = ('s, 'a, 'b, 'c) Affine.t

module Compose :
  sig
    val iso_and_lens : ('a, 'b) iso -> ('b, 'c, 'd) lens -> ('a, 'c, 'd) lens
    val lens_and_iso : ('a, 'a, 'c) lens -> ('a, 'c) iso -> ('a, 'c, 'c) lens
    val iso_and_prism :
      ('a, 'b) iso -> ('b, 'c, 'd) prism -> ('a, 'c, 'd) prism
    val prism_and_iso :
      ('a, 'b, 'd) prism -> ('b, 'd) iso -> ('a, 'd, 'd) prism
    val iso_and_affine :
      ('a, 'b) iso -> ('b, 'c, 'd, 'e) affine -> ('a, 'c, 'd, 'e) affine
    val affine_and_iso :
      ('a, 'b, 'c, 'd) affine -> ('b, 'e) iso -> ('a, 'e, 'c, 'd) affine
    val lens_and_prism :
      ('a, 'b, 'c) lens -> ('b, 'd, 'e) prism -> ('a, 'd, 'c, 'c * 'e) affine
    val prism_and_lens :
      ('a, 'b, 'c) prism -> ('b, 'd, 'e) lens -> ('a, 'd, 'e, 'c) affine
    val affine_and_lens :
      ('s1, 'a1, 'b1, 'c1) affine ->
      ('a1, 'a2, 'c2) lens -> ('s1, 'a2, 'b1 * 'c2, 'c1) affine
    val affine_and_prism :
      ('s1, 'a1, 'b1, 'c1) affine ->
      ('a1, 'a2, 'c2) prism ->
      ('s1, 'a2, 'b1, ('c1, 'b1 * 'c2) Either.t) affine
    val lens_and_affine :
      ('s1, 'a1, 'c1) lens ->
      ('a1, 'a2, 'b2, 'c2) affine -> ('s1, 'a2, 'c1 * 'b2, 'c1 * 'c2) affine
    val prism_and_affine :
      ('s1, 's2, 'c1) prism ->
      ('s2, 'a2, 'b2, 'c2) affine ->
      ('s1, 'a2, 'b2, ('c1, 'c2) Either.t) affine
  end

(** {6 Optics composition}

    All the following functions (outside of the operator(s)) have their arguments reversed.
    They are intended to be used in a pipe chain, such that the value to the left is composed
    into the value of the right.

    As a generic example, [a1 |> ab b2] pipes [a1]'s output into [b2]'s input. The resulting
    optic takes [a1]'s input and focuses on [b2]'s output. The function that has to be used
    in order to compose such optics together must be of type [a1 -> b2 -> c], where
    [a1] and [b2] are [a1] and [b2]'s types.
  *)

val ( % ) :
  ('a, 'b, 'c) Lens.t -> ('b, 'd, 'e) Lens.t -> ('a, 'd, 'c * 'e) Lens.t
val ii : ('a, 'b) Iso.t -> ('c, 'a) Iso.t -> ('c, 'b) Iso.t
val il : ('a, 'b, 'c) lens -> ('d, 'a) iso -> ('d, 'b, 'c) lens
val ip : ('a, 'b, 'c) prism -> ('d, 'a) iso -> ('d, 'b, 'c) prism
val ia : ('a, 'b, 'c, 'd) affine -> ('e, 'a) iso -> ('e, 'b, 'c, 'd) affine
val li : ('a, 'b) iso -> ('a, 'a, 'b) lens -> ('a, 'b, 'b) lens
val pi : ('a, 'b) iso -> ('c, 'a, 'b) prism -> ('c, 'b, 'b) prism
val ai : ('a, 'b, 'c, 'd) affine -> ('e, 'a) iso -> ('e, 'b, 'c, 'd) affine
val ll :
  ('a, 'b, 'c) Lens.t -> ('d, 'a, 'e) Lens.t -> ('d, 'b, 'e * 'c) Lens.t
val pp :
  ('a, 'b, 'b) Prism.t ->
  ('c, 'a, 'd) Prism.t -> ('c, 'b, ('d, 'b) Either.t) Prism.t
val lp :
  ('a, 'b, 'c) prism -> ('d, 'a, 'e) lens -> ('d, 'b, 'e, 'e * 'c) affine
val pl : ('a, 'b, 'c) lens -> ('d, 'a, 'e) prism -> ('d, 'b, 'c, 'e) affine
val aa :
  ('a, 'b, 'c, 'd) Affine.t ->
  ('e, 'a, 'f, 'g) Affine.t ->
  ('e, 'b, 'f * 'c, ('g, 'f * 'd) Either.t) Affine.t
val al :
  ('a, 'b, 'c) lens ->
  ('d, 'a, 'e, 'f) affine -> ('d, 'b, 'e * 'c, 'f) affine
val ap :
  ('a, 'b, 'c) prism ->
  ('d, 'a, 'e, 'f) affine -> ('d, 'b, 'e, ('f, 'e * 'c) Either.t) affine
val la :
  ('a, 'b, 'c, 'd) affine ->
  ('e, 'a, 'f) lens -> ('e, 'b, 'f * 'c, 'f * 'd) affine
val pa :
  ('a, 'b, 'c, 'd) affine ->
  ('e, 'a, 'f) prism -> ('e, 'b, 'c, ('f, 'd) Either.t) affine

(** {6 Operations} *)

val down : ('a, 'b) Iso.t -> 'a -> 'b
val up : ('a, 'b) Iso.t -> 'b -> 'a
val view : ('a, 'b, 'c) Lens.t -> 'a -> 'b
val update : ('a, 'b, 'c) Lens.t -> ('b -> 'b) -> 'a -> 'a
val set : ('a, 'b, 'c) Lens.t -> 'b -> 'a -> 'a
val preview : ('a, 'b, 'c) Prism.t -> 'a -> ('c, 'b) Either.t
val review : ('a, 'b, 'c) Prism.t -> 'b -> 'a

val preview' : ('a, 'b, 'c, 'd) Affine.t -> 'a -> ('d, 'b) Either.t
(** [preview' affine a] is [Either.Right b] if it succeeds at accessing the inner value.
    It returns [Either.Left d] otherwise. *)

val update' : ('a, 'b, 'c, 'd) Affine.t -> ('b -> 'b) -> 'a -> 'a
(** [update' affine f a] updates the inner value [affine] focuses in [a], by passing it through [f]. *)

val set' : ('a, 'b, 'c, 'd) Affine.t -> 'b -> 'a -> 'a
(** [set' affine b a] updates the inner value of [b]'s type in [a], if possible. *)

(** {6 Generic optics}

    Since OCaml is limited by value restriction when it comes to
    polymorphic types like these, these generic optics need to be
    instanciated before using them.

    Example usage: {_1 () |> ll _1 ()} would create
  *)

val _1 : unit -> ('a * 'b, 'a, 'b) Lens.t
(** [Lens] over the first element of a 2-uple. *)

val _2 : unit -> ('a * 'b, 'b, 'a) Lens.t
(** [Lens] over the second element of a 2-uple. *)

val _right : unit -> (('a, 'b) Either.t, 'b, 'a) Prism.t
(** [Prism] over the [Either.Right] value of an [Either.t] type. *)

val _left : unit -> (('a, 'b) Either.t, 'a, 'b) Prism.t
(** [Prism] over the [Either.Left] value of an [Either.t] type. *)

val _hd : unit -> ('a list, 'a, 'a list, unit) affine
(** [Affine] over a ['a list]'s head. *)

val _tl : unit -> ('a list, 'a list, 'a, unit) affine
(** [Affine] over a ['a list]'s tail. *)
