(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Interned (hash-consed) identifiers *)

module T = struct
  type t = {
    base : string ;
    salt : int ;
  }
  let compare (x : t) y = Stdlib.compare x y
  let equal (x : t) y = x = y
  let hash (x : t) = Hashtbl.hash x
end

include T

module Set = Set.Make (T)
module Map = Map.Make (T)
module Tab = Hashtbl.Make (T)

let of_string base = { base ; salt = 0 }

let to_string ident =
  if ident.salt = 0 then ident.base
  else ident.base ^ "_" ^ Int.to_string ident.salt
