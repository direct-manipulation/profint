(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

module IntHashEq = struct
  type t = int
  let equal = Int.equal
  let compare = Int.compare
  let hash (x : t) = Hashtbl.hash x
end

module ISet : Stdlib.Set.S with type elt := int =
  Stdlib.Set.Make(IntHashEq)
module IMap : Stdlib.Map.S with type key := int =
  Stdlib.Map.Make(IntHashEq)
module ITab : Stdlib.Hashtbl.S with type key := int =
  Stdlib.Hashtbl.Make(IntHashEq)

type ident = string

module IdHashEq = struct
  type t = ident
  let equal : t -> t -> bool = String.equal
  let compare : t -> t -> int = String.compare
  let hash (x : t) = Hashtbl.hash x
end

module IdSet : Stdlib.Set.S with type elt := ident =
  Stdlib.Set.Make(IdHashEq)
module IdMap : Stdlib.Map.S with type key := ident =
  Stdlib.Map.Make(IdHashEq)
module IdTab : Stdlib.Hashtbl.S with type key := ident =
  Stdlib.Hashtbl.Make(IdHashEq)

let failwith_s fmt = Printf.ksprintf failwith fmt
let failwith_fmt fmt =
  let buf = Buffer.create 19 in
  let out = Format.formatter_of_buffer buf in
  Format.kfprintf (fun _ -> failwith (Buffer.contents buf)) out fmt

let rec range_up step lo hi : int Seq.t = fun () ->
  if lo >= hi then Seq.Nil else
    Seq.Cons (lo, range_up step (lo + step) hi)

let rec range_down step hi lo : int Seq.t = fun () ->
  if hi <= lo then Seq.Nil else
    Seq.Cons (hi, range_down step (hi + step) lo)

let range ?(step = 1) x y =
  if step >= 0
  then range_up step x y
  else range_down step x y

module Q = CCFQueue
type 'a q = 'a Q.t
