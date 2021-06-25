(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Interned (hash-consed) strings *)

type idt = private {
  str : string ;
  idx : int ;
}

(** [intern s] returns a shared version of [s].

    Invariant: if [s1 = s2], then [intern s1 == intern s2]. *)
val intern : string -> idt

module Set : sig
  include Set.S
  val insert : t -> elt -> t
end with type elt := idt

module Map : sig
  include Map.S
  val insert : 'v t -> key -> 'v -> 'v t
  val digest : (key * 'v) list -> 'v t
end with type key := idt

module Hash : Hashtbl.S with type key := idt

(** Ascribes to both Set.OrderedType and Hashtbl.HashedType *)

type t = idt
val hash : t -> int
val equal : t -> t -> bool
val compare : t -> t -> int
