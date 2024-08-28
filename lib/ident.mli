(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

type t = {
  base : string ;
  salt : int ;
}

val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int

module Set : Set.S with type elt := t
module Map : Map.S with type key := t
module Tab : Hashtbl.S with type key := t

val of_string : string -> t
val to_string : t -> string
