(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Interned (hash-consed) identifiers *)

open Base

module T = struct
  type t = {
    base : string ;
    salt : int ;
  }
  [@@deriving equal, compare, sexp_of, hash]
end

include T

include Comparator.Make(T)

type set = (t, comparator_witness) Set.t
type 'a map = (t, 'a, comparator_witness) Map.t
type 'a tab = (t, 'a) Hashtbl.t

let of_string base = { base ; salt = 0 }

let to_string ident =
  if ident.salt = 0 then ident.base
  else ident.base ^ "_" ^ Int.to_string ident.salt
