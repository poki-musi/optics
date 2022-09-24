module Iso = struct
  type ('a, 'b) t = { get : 'a -> 'b ; set : 'b -> 'a }

  let[@ocaml.inline] make ~get ~set = {get; set}
  let[@ocaml.inline] down {get; _} v = get v
  let[@ocaml.inline] up {set; _} v = set v
  let[@ocaml.inline] flip {get; set} = {get=set; set=get}
  let[@ocaml.inline] iso_map {get; set} f v = get v |> f |> set
  let[@ocaml.inline] down_map {get; set} f v = set v |> f |> get

  let compose
    {get=get1; set=set1}
    {get=get2; set=set2}
    =
    let get v = v |> get1 |> get2 in
    let set v = v |> set2 |> set1 in
    { get; set }
end

module Lens = struct
  type ('s, 'a, 'b) t = { get : 's -> 'b * 'a ; set : 'b * 'a -> 's }

  let[@ocaml.inline] make ~get ~set : ('s, 'a, 'b) t = {get; set}
  let[@ocaml.inline] view ({get; _} : ('s, 'a, 'b) t) v = v |> get |> snd
  let[@ocaml.inline] update {get; set} f s = let b, a = get s in set (b, f a)
  let[@ocaml.inline] set lens v = update lens (Fun.const v)

  let compose
    ({get=get1; set=set1} : ('s1, 's2, 'b1) t)
    ({get=get2; set=set2} : ('s2, 'a2, 'b2) t)
    : ('s1, 'a2, 'b1 * 'b2) t
    =
    let get s1 =
        let b1, s2 = get1 s1 in
        let b2, a2 = get2 s2 in
        ((b1, b2), a2)
    in let set ((b1, b2), a2) = set1 (b1, set2 (b2, a2))
    in {get; set}
end

module Prism = struct
  type ('s, 'a, 'c) t = {
    get : 's -> ('c, 'a) Either.t ;
    set : ('c, 'a) Either.t -> 's
  }

  let[@ocaml.inline] make ~get ~set : ('s, 'a, 'c) t = {get; set}
  let[@ocaml.inline] preview {get; _} v = get v |> Either.fold ~left:(Fun.const Option.none) ~right:Option.some
  let[@ocaml.inline] review {set; _} v = Either.Right v |> set
  let[@ocaml.inline] exists {get; _} v = get v |> Either.is_right
  let[@ocaml.inline] isn't {get; _} v = get v |> Either.is_left

  let compose
    ({get=get1; set=set1} : ('s1, 's2, 'b1) t)
    ({get=get2; set=set2} : ('s2, 'a2, 'b2) t)
    : ('s1, 'a2, ('b1, 'a2) Either.t) t =
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
    in
    {get; set}
end

module Affine = struct
  type ('s, 'a, 'b, 'c) t = { get : 's -> ('c, 'b * 'a) Either.t ; set : ('c, 'b * 'a) Either.t -> 's }

  let[@ocaml.inline] make ~get ~set : ('s, 'a, 'b, 'c) t = {get; set}
  let[@ocaml.inline] preview {get; _} v = get v |> Either.map_right snd
  let[@ocaml.inline] update {get; set} f v = get v |> Either.map_right (fun (b, a) -> (b, f a)) |> set
  let[@ocaml.inline] set affine a v = update affine Fun.(const a) v
  let[@ocaml.inline] exists {get; _} v = get v |> Either.is_right
  let[@ocaml.inline] isn't {get; _} v = get v |> Either.is_left

  let compose
    ({get; set} : ('s1, 's2, 'b1, 'c1) t)
    ({get=get'; set=set'} : ('s2, 'a2, 'b2, 'c2) t)
    : ('s1, 'a2, 'b1 * 'b2, ('c1, 'b1 * 'c2) Either.t) t
    =
    let open Either in
    let get s1 = match get s1 with
      | Right (b1, s2) ->
          begin match get' s2 with
          | Left c2 -> left (right (b1, c2))
          | Right (b2, a2) -> right ((b1, b2), a2)
          end
      | Left c1 ->
          c1 |> left |> left
    in
    let set = function
      | Right ((b1, b2), a2) ->
          let s2 = right (b2, a2) |> set'
          in (b1, s2) |> right |> set
      | Left (Right (b1, c2)) ->
          let s2 = left c2 |> set' in
          (b1, s2) |> right |> set
      | Left (Left c1) ->
          c1 |> left |> set
    in
    {get; set}
end

type ('s, 'a) iso = ('s, 'a) Iso.t
type ('s, 'a, 'c) lens = ('s, 'a, 'c) Lens.t
type ('s, 'a, 'c) prism = ('s, 'a, 'c) Prism.t
type ('s, 'a, 'b, 'c) affine = ('s, 'a, 'b, 'c) Affine.t

module Compose = struct
  (** Iso composition *)

  let iso_and_lens
    ({get=get1;set=set1} : ('a, 'b) iso)
    ({get=get2;set=set2} : ('b, 'c, 'd) lens)
    : ('a, 'c, 'd) lens
    =
    let get v = get1 v |> get2 in
    let set v = set2 v |> set1 in
    { get; set }

  let lens_and_iso
    ({get=get1;set=set1} : ('s, 'a, 'b) lens)
    ({get=get2;set=set2} : ('a, 'd) iso)
    : ('a, 'c, 'd) lens
    =
    let get v = let (b, a) = get1 v in (b, get2 a) in
    let set (b, a') = let a = set2 a' in set1 (b, a) in
    { get; set }

  let iso_and_prism
    ({get=get1;set=set1} : ('a, 'b) iso)
    ({get=get2;set=set2} : ('b, 'c, 'd) prism)
    : ('a, 'c, 'd) prism
    =
    let get v = get1 v |> get2 in
    let set v = set2 v |> set1 in
    { get; set }

  let prism_and_iso
    ({get=get1;set=set1} : ('a, 'b, 'c) prism)
    ({get=get2;set=set2} : ('b, 'd) iso)
    : ('a, 'c, 'd) prism
    =
    let get v = get1 v |> Either.map_right get2 in
    let set v = Either.map_right set2 v |> set1 in
    { get; set }

  let iso_and_affine
    ({get=get1;set=set1} : ('a, 'b) iso)
    ({get=get2;set=set2} : ('b, 'c, 'd, 'e) affine)
    : ('a, 'c, 'd, 'e) affine
    =
    let get v = get1 v |> get2 in
    let set v = set2 v |> set1 in
    { get; set }

  let affine_and_iso
    ({get=get1;set=set1} : ('a, 'b, 'c, 'd) affine)
    ({get=get2;set=set2} : ('b, 'e) iso)
    : ('a, 'e, 'c, 'd) affine
    =
    let get v = get1 v |> Either.map_right (fun (b, a) -> (b, get2 a)) in
    let set v = v |> Either.map_right (fun (b, a) -> (b, set2 a)) |> set1 in
    { get; set }

  let lens_and_prism
    ({get=get1; set=set1} : ('a, 'b, 'c) lens)
    ({get=get2; set=set2} : ('b, 'd, 'e) prism)
    : ('a, 'd, 'c, 'c * 'e) affine
    =
    let open Either in
    {
      get = begin fun a ->
        let c, b = get1 a in
        let f x = (c, x) in
        get2 b |> map ~left:f ~right:f
      end ;
      set = fun v -> begin match v with
        | Left (c, e) -> c, (e |> left |> set2)
        | Right (c, d) -> c, (d |> right |> set2)
      end |> set1
    }

  let prism_and_lens
    ({get=get1; set=set1} : ('a, 'b, 'c) prism)
    ({get=get2; set=set2} : ('b, 'd, 'e) lens)
    : ('a, 'd, 'e, 'c) affine
    =
    let open Either in
    let get v = get1 v |> Either.map_right get2 in
    let set v = map_right set2 v |> set1 in
    { get; set }

  let affine_and_lens
    ({get=get1; set=set1} : ('s1, 'a1, 'b1, 'c1) affine)
    ({get=get2; set=set2} : ('a1, 'a2, 'c2) lens)
    : ('s1, 'a2, 'b1 * 'c2, 'c1) affine =
    let open Either in
    let get v = get1 v |> map_right (fun (b1, a1) ->
        let (c2, a2) = get2 a1 in ((b1, c2), a2))
    in
    let set v = match v with
     | Right ((b1, c2), a2) -> let a1 = set2 (c2, a2) in set1 (right (b1, a1))
     | Left v -> v |> left |> set1
    in
    { get; set }

  let affine_and_prism
    ({get=get1; set=set1} : ('s1, 'a1, 'b1, 'c1) affine)
    ({get=get2; set=set2} : ('a1, 'a2, 'c2) prism)
    : ('s1, 'a2, 'b1, ('c1, 'b1 * 'c2) Either.t) affine =
    let open Either in
     let get v = match get1 v with
        | Left c1 -> c1 |> left |> left
        | Right (b1, a1) ->
            (get2 a1 |> function
              | Left c2 -> left (right (b1, c2))
              | Right a2 -> right (b1, a2))
     in
     let set v = begin match v with
        | Right (b1, a2) -> let a1 = right a2 |> set2 in right (b1, a1) |> set1
        | Left (Right (b1, c2)) -> let a1 = left c2 |> set2 in right (b1, a1) |> set1
        | Left (Left c1) -> (c1 |> left |> set1)
      end  in
     { get; set }

  let lens_and_affine
    ({get=get1; set=set1} : ('s1, 'a1, 'c1) lens)
    ({get=get2; set=set2} : ('a1, 'a2, 'b2, 'c2) affine)
    : ('s1, 'a2, 'c1 * 'b2, 'c1 * 'c2) affine =
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
    { get; set }

  let prism_and_affine
    ({get=get1; set=set1} : ('s1, 's2, 'c1) prism)
    ({get=get2; set=set2} : ('s2, 'a2, 'b2, 'c2) affine)
    : ('s1, 'a2, 'b2, ('c1, 'c2) Either.t) affine =
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
    { get; set }
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
