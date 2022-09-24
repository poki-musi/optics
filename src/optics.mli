module Iso :
  sig
    type (_, _) t = Iso : {
      get : 's -> 'a;
      set : 'a -> 's;
    } -> ('s, 'a) t
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
    type ('s, 'a) t = Lens : {
      get : 's -> 'c * 'a;
      set : 'c * 'a -> 's;
    } -> ('s, 'a) t
    val make : get:('a -> 'b * 'c) -> set:('b * 'c -> 'a) -> ('a, 'c) t
    val view : ('a, 'b) t -> 'a -> 'b
    val update : ('a, 'b) t -> ('b -> 'b) -> 'a -> 'a
    val set : ('a, 'b) t -> 'b -> 'a -> 'a
    val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
  end
module Prism :
  sig
    type ('s, 'a) t =
        Prism : { get : 's -> ('c, 'a) Either.t;
          set : ('c, 'a) Either.t -> 's;
        } -> ('s, 'a) t
    val make :
      get:('a -> ('b, 'c) Either.t) ->
      set:(('b, 'c) Either.t -> 'a) -> ('a, 'c) t
    val preview : ('a, 'b) t -> 'a -> 'b option
    val review : ('a, 'b) t -> 'b -> 'a
    val exists : ('a, 'b) t -> 'a -> bool
    val isn't : ('a, 'b) t -> 'a -> bool
    val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
  end
module Affine :
  sig
    type ('s, 'a) t =
        Affine : { get : 's -> ('c, 'b * 'a) Either.t;
          set : ('c, 'b * 'a) Either.t -> 's;
        } -> ('s, 'a) t
    val make :
      get:('a -> ('b, 'c * 'd) Either.t) ->
      set:(('b, 'c * 'd) Either.t -> 'a) -> ('a, 'd) t
    val preview : ('a, 'b option) t -> 'a -> 'b option
    val update : ('a, 'b) t -> ('b -> 'b) -> 'a -> 'a
    val set : ('a, 'b) t -> 'b -> 'a -> 'a
    val exists : ('a, 'b) t -> 'a -> bool
    val isn't : ('a, 'b) t -> 'a -> bool
    val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
  end
type ('s, 'a) iso = ('s, 'a) Iso.t
type ('s, 'a) lens = ('s, 'a) Lens.t
type ('s, 'a) prism = ('s, 'a) Prism.t
type ('s, 'a) affine = ('s, 'a) Affine.t
module Compose :
  sig
    val iso_and_lens :
      ('a, 'b) iso -> ('b, 'c) lens -> ('a, 'c) lens
    val lens_and_iso :
      ('a, 'b) lens -> ('b, 'c) iso -> ('a, 'c) lens
    val iso_and_prism :
      ('a, 'b) iso -> ('b, 'c) prism -> ('a, 'c) prism
    val prism_and_iso :
      ('a, 'b) prism -> ('b, 'c) iso -> ('a, 'c) prism
    val iso_and_affine :
      ('a, 'b) iso -> ('b, 'c) affine -> ('a, 'c) affine
    val affine_and_iso :
      ('a, 'b) affine -> ('b, 'c) iso -> ('a, 'c) affine
    val lens_and_prism :
      ('a, 'b) lens -> ('b, 'c) prism -> ('a, 'c) affine
    val prism_and_lens :
      ('a, 'b) prism -> ('b, 'c) lens -> ('a, 'c) affine
    val affine_and_lens :
      ('a, 'b) affine -> ('b, 'c) lens -> ('a, 'c) affine
    val affine_and_prism :
      ('a, 'b) affine -> ('b, 'c) prism -> ('a, 'c) affine
    val lens_and_affine :
      ('a, 'b) lens -> ('b, 'c) affine -> ('a, 'c) affine
    val prism_and_affine :
      ('a, 'b) affine -> ('b, 'c) affine -> ('a, 'c) affine
  end

val ( % ) : ('a, 'b) lens -> ('b, 'c) lens -> ('a, 'c) lens
val ii : ('a, 'b) iso -> ('c, 'a) iso -> ('c, 'b) iso
val il : ('a, 'b) lens -> ('c, 'a) iso -> ('c, 'b) lens
val ip : ('a, 'b) prism -> ('c, 'a) iso -> ('c, 'b) prism
val ia : ('a, 'b) affine -> ('c, 'a) iso -> ('c, 'b) affine
val li : ('a, 'b) iso -> ('c, 'a) lens -> ('c, 'b) lens
val pi : ('a, 'b) iso -> ('c, 'a) prism -> ('c, 'b) prism
val ai : ('a, 'b) iso -> ('c, 'a) affine -> ('c, 'b) affine
val ll : ('a, 'b) lens -> ('c, 'a) lens -> ('c, 'b) lens
val pp : ('a, 'b) prism -> ('c, 'a) prism -> ('c, 'b) prism
val lp : ('a, 'b) prism -> ('c, 'a) lens -> ('c, 'b) affine
val pl : ('a, 'b) lens -> ('c, 'a) prism -> ('c, 'b) affine
val aa : ('a, 'b) affine -> ('c, 'a) affine -> ('c, 'b) affine
val al : ('a, 'b) lens -> ('c, 'a) affine -> ('c, 'b) affine
val ap : ('a, 'b) prism -> ('c, 'a) affine -> ('c, 'b) affine
val la : ('a, 'b) affine -> ('c, 'a) lens -> ('c, 'b) affine
val pa : ('a, 'b) affine -> ('c, 'a) prism -> ('c, 'b) affine
val down : ('a, 'b) iso -> 'a -> 'b
val up : ('a, 'b) iso -> 'b -> 'a
val view : ('a, 'b) lens -> 'a -> 'b
val update : ('a, 'b) lens -> ('b -> 'b) -> 'a -> 'a
val set : ('a, 'b) lens -> 'b -> 'a -> 'a
val preview : ('a, 'b) prism -> 'a -> 'b option
val review : ('a, 'b) prism -> 'b -> 'a
val preview' : ('a, 'b option) affine -> 'a -> 'b option
val update' : ('a, 'b) affine -> ('b -> 'b) -> 'a -> 'a
val set' : ('a, 'b) affine -> 'b -> 'a -> 'a

val _1 : unit -> ('a * 'b, 'a) lens
val _2 : unit -> ('a * 'b, 'b) lens
val _right : unit -> (('a, 'b) Either.t, 'b) prism
val _left : unit -> (('a, 'b) Either.t, 'a) prism
val _hd : unit -> ('a list, 'a) affine
val _tl : unit -> ('a list, 'a list) affine
