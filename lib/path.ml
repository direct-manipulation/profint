(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Base

module Dir = struct
  type t = L | R
  [@@deriving equal]

  let flip = function L -> R | _ -> L
  let of_bool = function true -> R | _ -> L
  let to_bool = function L -> false | _ -> true
  let to_string = function L -> "l" | _ -> "r"
end

type t = Z.t
[@@deriving equal]

let to_string : t -> _ =
  fun p -> "P" ^ Z.to_string p
let of_string : _ -> t =
  fun str ->
  if String.length str > 1 && Char.equal (String.unsafe_get str 0) 'P' then
    Z.of_substring str ~pos:1 ~len:(String.length str - 1)
  else invalid_arg "Path.of_string"

let size (p : t) = Z.numbits p - 1
let length = size

let init : t = Z.one
let empty = init

let is_empty (p : t) = Z.(equal p init)

let cons dir (p : t) : t =
  let p = Z.(p lsl 1) in
  match dir with
  | Dir.L -> p
  | Dir.R -> Z.(succ p)

let snoc (p : t) dir : t =
  let depth = Z.numbits p - 1 in
  match dir with
  | Dir.L -> Z.(p + one lsl depth)
  | Dir.R -> Z.(p + one lsl Int.(depth + 1))

let flip_cons p d = cons d p
let flip_snoc d p = snoc p d

let append (p1 : t) (p2 : t) : t =
  let p1_depth = Z.numbits p1 - 1 in
  (* flip p2's lsb, since it will be flipped again *)
  let p2 = Z.((p2 lxor one) lsl p1_depth) in
  Z.(p1 lxor p2)

exception Empty

let expose_front_exn (p : t) : Dir.t * t =
  if Z.(equal p one) then raise Empty else
  let dir = Dir.of_bool Z.(testbit p 0) in
  (dir, Z.(p asr 1))

let expose_back_exn (p : t) : t * Dir.t =
  if Z.(equal p one) then raise Empty else
  let depth = Z.numbits p - 1 in
  let dir = Dir.of_bool Z.(testbit p Int.(depth - 1)) in
  let p = Z.(p land (one lsl depth |> pred)) in
  match dir with
  | Dir.R -> (p, dir)
  | Dir.L ->
      let depth = depth - 1 in
      (Z.(p lor (one lsl depth)), dir)

let expose_front p =
  try Some (expose_front_exn p) with Empty -> None

let expose_back p =
  try Some (expose_back_exn p) with Empty -> None

let rec fold_left p ~init ~f =
  match expose_front_exn p with
  | (dir, p) -> fold_left p ~init:(f init dir) ~f
  | exception Empty -> init

let rec fold_right p ~init ~f =
  match expose_back_exn p with
  | (p, dir) -> fold_right p ~init:(f dir init) ~f
  | exception Empty -> init

let to_list p = fold_right p ~init:[] ~f:List.cons

let of_list l = List.fold_left l ~init:init ~f:snoc

let to_dirstring p =
  to_list p |>
  List.map ~f:Dir.to_string |>
  String.concat ~sep:","

module Private = struct
  let random_test ?(n=100) () =
    Random.self_init () ;
    let str = ref [] in
    let p = ref init in
    for _ = 1 to n do
      match Random.int 4 with
      | 0 ->
          str := !str @ [Dir.L] ;
          p := snoc !p Dir.L
      | 1 ->
          str := !str @ [Dir.R] ;
          p := snoc !p Dir.R
      | 2 ->
          str := Dir.L :: !str ;
          p := cons Dir.L !p
      | _ ->
          str := Dir.R :: !str ;
          p := cons Dir.R !p
    done ;
    let str = String.concat ~sep:"," @@ List.map ~f:Dir.to_string !str in
    let p = to_dirstring !p in
    assert (String.equal str p)
end
