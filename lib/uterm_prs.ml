(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util

exception Parsing of string

let thing_of_string prs str =
  let lb = Lexing.from_string str in
  try
    let t = prs Prolex.token lb in
    t
  with
  | Proprs.Error -> raise (Parsing "")

let term_of_string str = thing_of_string Proprs.one_term str
let ty_of_string str = thing_of_string Proprs.one_ty str
let form_of_string str = thing_of_string Proprs.one_form str
