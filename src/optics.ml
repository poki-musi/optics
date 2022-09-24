type (_, _) optic =
  | Prism :
    ('s -> ('c, 'a) Either.t) * (('c, 'a) Either.t -> 's) -> ('s, 'a) optic
  | Affine :
    ('s -> ('c, 'b * 'a) Either.t) * (('c, 'b * 'a) Either.t -> 's) -> ('s, 'a) optic

module Iso = struct
  type (_, _) t = | Iso : { get : 's -> 'a ; set : 'a -> 's } -> ('s, 'a) t

  let[@ocaml.inline] make ~get ~set = Iso {get; set}
  let[@ocaml.inline] down (Iso {get; _}) v = get v
  let[@ocaml.inline] up (Iso {set; _}) v = set v
  let[@ocaml.inline] flip (Iso {get; set}) = Iso {get=set; set=get}
  let[@ocaml.inline] iso_map (Iso {get; set}) f v = get v |> f |> set
  let[@ocaml.inline] down_map (Iso {get; set}) f v = set v |> f |> get

  let compose
    (Iso {get=get1; set=set1})
    (Iso {get=get2; set=set2})
    =
    let get v = v |> get1 |> get2 in
    let set v = v |> set2 |> set1 in
    (Iso { get; set })
end

module Lens = struct
  type ('s, 'a) t =
    Lens : { get : 's -> 'c * 'a ; set : 'c * 'a -> 's } -> ('s, 'a) t

  let[@ocaml.inline] make ~get ~set = (Lens {get; set})
  let[@ocaml.inline] view (Lens {get; _}) v = v |> get |> snd
  let[@ocaml.inline] update (Lens {get; set}) f s = let b, a = get s in set (b, f a)
  let[@ocaml.inline] set lens v = update lens (Fun.const v)

  let compose
    (Lens {get=get1; set=set1})
    (Lens {get=get2; set=set2})
    =
    let get s1 =
        let b1, s2 = get1 s1 in
        let b2, a2 = get2 s2 in
        ((b1, b2), a2)
    in let set ((b1, b2), a2) = set1 (b1, set2 (b2, a2))
    in Lens {get; set}
end

module Prism = struct
  type ('s, 'a) t = Prism : {
    get : 's -> ('c, 'a) Either.t ;
    set : ('c, 'a) Either.t -> 's
  } -> ('s, 'a) t

  let[@ocaml.inline] make ~get ~set = (Prism {get; set})
  let[@ocaml.inline] preview (Prism {get; _}) v = get v |> Either.fold ~left:(Fun.const Option.none) ~right:Option.some
  let[@ocaml.inline] review (Prism {set; _}) v = Either.Right v |> set
  let[@ocaml.inline] exists (Prism {get; _}) v = get v |> Either.is_right
  let[@ocaml.inline] isn't (Prism {get; _}) v = get v |> Either.is_left

  let compose
    (Prism {get=get1; set=set1})
    (Prism {get=get2; set=set2})
    =
    let open Either in
    let get v = match get1 v with
      | Left v -> v |> left |> left
      | Right v -> v |> get2 |> map_left right
    in
    let set = function
      | Right v ->
          v |> right |> set2 |> right |> set1
      | Left (Right v) ->
          v |> left |> set2 |> right |> set1
      | Left (Left v) ->
          v |> left |> set1
    in Prism {get; set}
end

module Affine = struct
  type ('s, 'a) t = Affine : {
    get : 's -> ('c, 'b * 'a) Either.t ;
    set : ('c, 'b * 'a) Either.t -> 's
  } -> ('s, 'a) t

  let[@ocaml.inline] make ~get ~set = Affine {get; set}
  let[@ocaml.inline] preview (Affine {get; _}) v = get v |> Either.fold ~right:snd ~left:Fun.(const None)
  let[@ocaml.inline] update (Affine {get; set}) f v = get v |> Either.map_right (fun (b, a) -> (b, f a)) |> set
  let[@ocaml.inline] set affine a v = update affine Fun.(const a) v
  let[@ocaml.inline] exists (Affine {get; _}) v = get v |> Either.is_right
  let[@ocaml.inline] isn't (Affine {get; _}) v = get v |> Either.is_left

  let compose
    (Affine {get=get1; set=set1})
    (Affine {get=get2; set=set2})
    =
    let open Either in
    let get s1 = match get1 s1 with
      | Right (b1, s2) ->
          begin match get2 s2 with
          | Left c2 -> left (right (b1, c2))
          | Right (b2, a2) -> right ((b1, b2), a2)
          end
      | Left c1 ->
          c1 |> left |> left
    in
    let set = function
      | Right ((b1, b2), a2) ->
          let s2 = right (b2, a2) |> set2
          in (b1, s2) |> right |> set1
      | Left (Right (b1, c2)) ->
          let s2 = left c2 |> set2 in
          (b1, s2) |> right |> set1
      | Left (Left c1) ->
          c1 |> left |> set1
    in Affine {get; set}
end

type ('s, 'a) iso    = ('s, 'a) Iso.t
type ('s, 'a) lens   = ('s, 'a) Lens.t
type ('s, 'a) prism  = ('s, 'a) Prism.t
type ('s, 'a) affine = ('s, 'a) Affine.t

module Compose = struct
  (** Iso composition *)

  let iso_and_lens
    (Iso.Iso {get=get1;set=set1})
    (Lens.Lens {get=get2;set=set2})
    =
    let get v = get1 v |> get2 in
    let set v = set2 v |> set1 in
    Lens.Lens { get; set }

  let lens_and_iso
    (Lens.Lens {get=get1;set=set1})
    (Iso.Iso {get=get2;set=set2})
    =
    let get v = let (b, a) = get1 v in (b, get2 a) in
    let set (b, a') = let a = set2 a' in set1 (b, a) in
    Lens.Lens { get; set }

  let iso_and_prism
    (Iso.Iso {get=get1;set=set1})
    (Prism.Prism {get=get2;set=set2})
    =
    let get v = get1 v |> get2 in
    let set v = set2 v |> set1 in
    Prism.Prism { get; set }

  let prism_and_iso
    (Prism.Prism {get=get1;set=set1})
    (Iso.Iso {get=get2;set=set2})
    =
    let get v = v |> get1 |> Either.map_right get2 in
    let set v = v |> Either.map_right set2 |> set1 in
    Prism.Prism { get; set }

  let iso_and_affine
    (Iso.Iso {get=get1;set=set1})
    (Affine.Affine {get=get2;set=set2})
    =
    let get v = get1 v |> get2 in
    let set v = set2 v |> set1 in
    Affine.Affine { get; set }

  let affine_and_iso
    (Affine.Affine {get=get1;set=set1})
    (Iso.Iso {get=get2;set=set2})
    =
    let get v = get1 v |> Either.map_right (fun (b, a) -> (b, get2 a)) in
    let set v = v |> Either.map_right (fun (b, a) -> (b, set2 a)) |> set1 in
    Affine.Affine { get; set }

  let lens_and_prism
    (Lens.Lens {get=get1; set=set1})
    (Prism.Prism {get=get2; set=set2})
    =
    let open Either in
    let get a =
      let c, b = get1 a in
      let f x = (c, x) in
      get2 b |> map ~left:f ~right:f
    in
    let set v = begin match v with
        | Left (c, e) -> c, (e |> left |> set2)
        | Right (c, d) -> c, (d |> right |> set2)
      end |> set1
    in
    Affine.Affine { get; set }

  let prism_and_lens
    (Prism.Prism {get=get1; set=set1})
    (Lens.Lens {get=get2; set=set2})
    =
    let open Either in
    let get v = get1 v |> Either.map_right get2 in
    let set v = map_right set2 v |> set1 in
    Affine.Affine { get; set }

  let affine_and_lens
    (Affine.Affine {get=get1; set=set1})
    (Lens.Lens {get=get2; set=set2})
    =
    let open Either in
    let get v = get1 v |> map_right (fun (b1, a1) ->
        let (c2, a2) = get2 a1 in ((b1, c2), a2))
    in
    let set v = match v with
     | Right ((b1, c2), a2) -> let a1 = set2 (c2, a2) in set1 (right (b1, a1))
     | Left v -> v |> left |> set1
    in
    Affine.Affine { get; set }

  let affine_and_prism
    (Affine.Affine {get=get1; set=set1})
    (Prism.Prism {get=get2; set=set2})
    =
    let open Either in
    let get v = match get1 v with
      | Left c1 -> c1 |> left |> left
      | Right (b1, a1) ->
        (get2 a1 |> function
        | Left c2 -> left (right (b1, c2))
        | Right a2 -> right (b1, a2))
    in
    let set v = match v with
      | Right (b1, a2) ->
          let a1 = right a2 |> set2 in right (b1, a1) |> set1
      | Left (Right (b1, c2)) ->
          let a1 = left c2 |> set2 in right (b1, a1) |> set1
      | Left (Left c1) ->
          (c1 |> left |> set1)
    in
    Affine.Affine { get; set }

  let lens_and_affine
    (Lens.Lens {get=get1; set=set1})
    (Affine.Affine {get=get2; set=set2})
    =
    let open Either in
    let get v =
      let (c1, a1) = get1 v in
        get2 a1 |> map
          ~left:(fun c2 -> c1, c2)
          ~right:(fun (b2, a2) -> (c1, b2), a2)
    in
    let set v = (match v with
      | Right ((c1, b2), a2) -> let a1 = set2 (right (b2, a2)) in (c1, a1)
      | Left (c1, c2) -> let a1 = c2 |> left |> set2 in (c1, a1)) |> set1
    in
    Affine.Affine { get; set }

  let prism_and_affine
    (Prism.Prism {get=get1; set=set1})
    (Affine.Affine {get=get2; set=set2})
    =
    let open Either in
    let get v = match get1 v with
      | Left c1 -> c1 |> left |> left
      | Right s2 -> begin match get2 s2 with
        | Left c2 -> left (right c2)
        | Right b2_a2 -> right b2_a2
    end in
    let set v = match v with
      | Right b2_a2 -> b2_a2 |> right |> set2 |> right |> set1
      | Left (Right c2) -> c2 |> left |> set2 |> right |> set1
      | Left (Left c1) -> c1 |> left |> set1
    in
    Affine.Affine { get; set }
end

let ( % ) = Lens.compose

let ii i2 i1 = Iso.compose i1 i2
let il l2 i1 = Compose.iso_and_lens i1 l2
let ip p2 i1 = Compose.iso_and_prism i1 p2
let ia a2 i1 = Compose.iso_and_affine i1 a2
let li i2 l1 = Compose.lens_and_iso l1 i2
let pi i2 p1 = Compose.prism_and_iso p1 i2
let ai i2 a1 = Compose.affine_and_iso a1 i2

let ll l2 l1 = Lens.compose l1 l2
let pp p2 p1 = Prism.compose p1 p2
let lp p2 l1 = Compose.lens_and_prism l1 p2
let pl l2 p1 = Compose.prism_and_lens p1 l2

let aa a2 a1 = Affine.compose a1 a2
let al l2 a1 = Compose.affine_and_lens a1 l2
let ap p2 a1 = Compose.affine_and_prism a1 p2
let la a2 l1 = Compose.lens_and_affine l1 a2
let pa a2 p1 = Compose.prism_and_affine p1 a2

let down = Iso.down
let up = Iso.up

let view = Lens.view
let update = Lens.update
let set = Lens.set

let preview = Prism.preview
let review = Prism.review

let preview' = Affine.preview
let update' = Affine.update
let set' = Affine.set

let _1 () = Lens.make
  ~get:(fun (a, b) -> (b, a))
  ~set:(fun (b, a) -> (a, b))

let _2 () = Lens.make
  ~get:(fun (a, b) -> (a, b))
  ~set:(fun (a, b) -> (a, b))

let _right () = Prism.make
  ~get:(Either.map ~left:Fun.id ~right:Fun.id)
  ~set:(Either.map ~left:Fun.id ~right:Fun.id)

let _left () = Prism.make
  ~get:Either.(fold ~left:right ~right:left)
  ~set:Either.(fold ~left:right ~right:left)

let _hd () = let open Either in Affine.make
  ~get:(function [] -> Left () | x::xs -> Right (xs, x))
  ~set:(function Left _ -> [] | Right (xs, x) -> x::xs)

let _tl () = let open Either in Affine.make
  ~get:(function [] -> Left () | x::xs -> Right (x, xs))
  ~set:(function Left _ -> [] | Right (x, xs) -> x::xs)

let _1_1_1 () = _1 () % _1 () % _1 ()
