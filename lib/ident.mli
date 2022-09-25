(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

type t = {
  base : string ;
  salt : int ;
}
[@@deriving equal, compare, sexp_of, hash]

include Comparator.S with type t := t

type set = (t, comparator_witness) Set.t
type 'a map = (t, 'a, comparator_witness) Map.t
type 'a tab = (t, 'a) Hashtbl.t

val of_string : string -> t
val to_string : t -> string
