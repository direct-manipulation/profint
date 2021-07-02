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
    String.equal id1.str id2.str
  let hash (id : idt) =
    Stdlib.Hashtbl.hash id.str
end

module Hash = Stdlib.Hashtbl.Make(IdtHashed)

let intern : string -> idt =
  let module StringH = struct
    type t = string
    let hash (x : t) = Stdlib.Hashtbl.hash x
    let equal (x : t) y = String.equal x y
  end in
  let module Ht = Stdlib.Hashtbl.Make(StringH) in
  let idtab = Ht.create 109 in  (* memory leak *)
  let last_idx = ref 0 in
  fun str ->
    match Ht.find idtab str with
    | idt -> idt
    | exception Not_found ->
        incr last_idx ;
        let idt = { str ; idx = !last_idx } in
        Ht.replace idtab str idt ;
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
