(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

type idt = {
  str : string ;
  idx : int ;
}

module IdtHashed = struct
  type t = idt
  let equal (id1 : idt) id2 =
    id1.str = id2.str
  let hash (id : idt) =
    Stdlib.Hashtbl.hash id.str
end

module IdtTab = Stdlib.Weak.Make(IdtHashed)
module Hash = Stdlib.Hashtbl.Make(IdtHashed)

let intern : string -> idt =
  let idtab = IdtTab.create 109 in
  let last_idx = ref 0 in
  fun id ->
    incr last_idx ;
    let cand = { str = id ; idx = !last_idx } in
    let idt = IdtTab.merge idtab cand in
    if idt.idx != cand.idx then decr last_idx ;
    idt

module IdtOrdered = struct
  type t = idt
  let compare (id1 : idt) id2 =
    if id1.idx < id2.idx then -1
    else if id1.idx > id2.idx then 1
    else 0
end

module IdtSet = struct
  include Stdlib.Set.Make(IdtOrdered)
  let insert set elt = add elt set
end
module Set = IdtSet

module IdtMap = struct
  include Stdlib.Map.Make(IdtOrdered)
  let insert m k v = add k v m
  let digest kvs = List.to_seq kvs |> of_seq
end
module Map = IdtMap

type t = idt
include (IdtHashed : Stdlib.Hashtbl.HashedType with type t := idt)
include (IdtOrdered : Stdlib.Set.OrderedType with type t := idt)
