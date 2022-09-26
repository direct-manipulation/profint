(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

type doc = Caml.Format.formatter -> unit

val string : string -> doc
val string_as : int -> string -> doc
val cut : doc
val (++) : doc -> doc -> doc

val pp : Caml.Format.formatter -> doc -> unit
val pp_linear : Caml.Format.formatter -> doc -> unit

val to_string : doc -> string

type wrapping = Transparent | Opaque

type exp =
  | Atom of doc
  | Wrap of wrapping * doc * exp * doc
  | Appl of int * bappl

and bappl =
  | Prefix of doc * exp
  | Postfix of doc * exp
  | Infix of doc * assoc * exp list

and assoc = Left | Right | Non

val bracket : ?ld:doc -> ?rd:doc -> exp -> doc
