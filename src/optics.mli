module Iso :
  sig
    type (_, _, _, _) t =
        Iso : { get : 's -> 'a; set : 'b -> 't; } -> ('s, 't, 'a, 'b) t
    type ('s, 'a) t' = ('s, 's, 'a, 'a) t
    val make : get:('a -> 'b) -> set:('c -> 'd) -> ('a, 'd, 'b, 'c) t
    val make' : get:('s -> 'a) -> set:('a -> 's) -> ('s, 'a) t'
    val down : ('a, 'b, 'c, 'd) t -> 'a -> 'c
    val up : ('a, 'b, 'c, 'd) t -> 'd -> 'b
    val flip : ('a, 'b, 'c, 'd) t -> ('d, 'c, 'b, 'a) t
    val iso_map : ('a, 'b, 'c, 'd) t -> ('c -> 'd) -> 'a -> 'b
    val down_map : ('a, 'b, 'c, 'd) t -> ('b -> 'a) -> 'd -> 'c
    val compose :
      ('a, 'b, 'c, 'd) t -> ('c, 'd, 'e, 'f) t -> ('a, 'b, 'e, 'f) t
  end
module Lens :
  sig
    type (_, _, _, _) t =
        Lens : { get : 's -> 'c * 'a; set : 'c * 'b -> 't;
        } -> ('s, 't, 'a, 'b) t
    type ('s, 'a) t' = ('s, 's, 'a, 'a) t
    val make :
      get:('a -> 'b * 'c) -> set:('b * 'd -> 'e) -> ('a, 'e, 'c, 'd) t
    val make' : get:('s -> 'b * 'a) -> set:('b * 'a -> 's) -> ('s, 'a) t'
    val view : ('a, 'b, 'c, 'd) t -> 'a -> 'c
    val update : ('a, 'b, 'c, 'd) t -> ('c -> 'd) -> 'a -> 'b
    val set : ('a, 'b, 'c, 'd) t -> 'd -> 'a -> 'b
    val compose :
      ('a, 'b, 'c, 'd) t -> ('c, 'd, 'e, 'f) t -> ('a, 'b, 'e, 'f) t
  end
module Prism :
  sig
    type (_, _, _, _) t =
        Prism : { get : 's -> ('c, 'a) Either.t;
          set : ('c, 'b) Either.t -> 't;
        } -> ('s, 't, 'a, 'b) t
    type ('s, 'a) t' = ('s, 's, 'a, 'a) t
    val make :
      get:('a -> ('b, 'c) Either.t) ->
      set:(('b, 'd) Either.t -> 'e) -> ('a, 'e, 'c, 'd) t
    val make' :
      get:('s -> ('b, 'a) Either.t) ->
      set:(('b, 'a) Either.t -> 's) -> ('s, 'a) t'
    val preview : ('a, 'b, 'c, 'd) t -> 'a -> 'c option
    val review : ('a, 'b, 'c, 'd) t -> 'd -> 'b
    val exists : ('a, 'b, 'c, 'd) t -> 'a -> bool
    val isn't : ('a, 'b, 'c, 'd) t -> 'a -> bool
    val compose :
      ('a, 'b, 'c, 'd) t -> ('c, 'd, 'e, 'f) t -> ('a, 'b, 'e, 'f) t
  end
module Affine :
  sig
    type (_, _, _, _) t =
        Affine : { get : 's -> ('c1, 'c2 * 'a) Either.t;
          set : ('c1, 'c2 * 'b) Either.t -> 't;
        } -> ('s, 't, 'a, 'b) t
    type ('s, 'a) t' = ('s, 's, 'a, 'a) t
    val make :
      get:('a -> ('b, 'c * 'd) Either.t) ->
      set:(('b, 'c * 'e) Either.t -> 'f) -> ('a, 'f, 'd, 'e) t
    val make' :
      get:('s -> ('b, 'c * 'a) Either.t) ->
      set:(('b, 'c * 'a) Either.t -> 's) -> ('s, 'a) t'
    val preview : ('a, 'b, 'c option, 'd) t -> 'a -> 'c option
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
val preview' : ('a, 'b, 'c option, 'd) Affine.t -> 'a -> 'c option
val update' : ('a, 'b, 'c, 'd) Affine.t -> ('c -> 'd) -> 'a -> 'b
val set' : ('a, 'b, 'c, 'd) Affine.t -> 'd -> 'a -> 'b
val _1 : unit -> ('a * 'b, 'c * 'b, 'a, 'c) Lens.t
val _2 : unit -> ('a * 'b, 'a * 'c, 'b, 'c) Lens.t
val _right : unit -> (('a, 'b) Either.t, ('a, 'c) Either.t, 'b, 'c) Prism.t
val _left : unit -> (('a, 'b) Either.t, ('c, 'b) Either.t, 'a, 'c) Prism.t
val _hd : unit -> ('a list, 'a list, 'a, 'a) Affine.t
val _tl : unit -> ('a list, 'a list, 'a list, 'a list) Affine.t
