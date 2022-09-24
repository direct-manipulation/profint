(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* module IntHashEq = struct *)
(*   type t = int *)
(*   let equal = Int.equal *)
(*   let compare = Int.compare *)
(*   let hash (x : t) = Hashtbl.hash x *)
(* end *)

module ISet = Stdlib.Set.Make(CCInt)
module IMap = Stdlib.Map.Make(CCInt)
module ITab = Stdlib.Hashtbl.Make(CCInt)

module SSet = Stdlib.Set.Make(CCString)
module SMap = Stdlib.Map.Make(CCString)
module STab = Stdlib.Hashtbl.Make(CCString)

type ident = {
  base : string ;
  salt : int ;
}
let ident base = { base ; salt = 0 }
let repr ident =
  if ident.salt = 0 then ident.base
  else ident.base ^ "_" ^ string_of_int ident.salt

module IdHashEq = struct
  type t = ident
  let equal (x : ident) (y : ident) =
    String.equal x.base y.base && Int.equal x.salt y.salt
  let compare (x : ident) (y : ident) =
    match String.compare x.base y.base with
    | 0 -> Int.compare x.salt y.salt
    | k -> k
  let hash : ident -> int = Hashtbl.hash
end

module IdSet = Stdlib.Set.Make(IdHashEq)
module IdMap = Stdlib.Map.Make(IdHashEq)
module IdTab = Stdlib.Hashtbl.Make(IdHashEq)

let panic =
  (* hiding the exception in a local module to make it impossible to
   * handle except with a catchall handler *)
  let module P = struct
    exception Panic of string
  end in
  fun msg -> raise @@ P.Panic msg

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

let pp_to_string pp thing =
  let buf = Buffer.create 19 in
  let out = Format.formatter_of_buffer buf in
  pp out thing ;
  Format.pp_print_flush out () ;
  Buffer.contents buf
