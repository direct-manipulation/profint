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

let failwith_s fmt   = Printf.ksprintf failwith fmt
let failwith_fmt fmt = Format.ksprintf failwith fmt
