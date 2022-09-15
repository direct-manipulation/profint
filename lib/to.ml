(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Types

module type TO = sig
  type 'a pp

  val ty_to_exp    : ty -> Doc.exp
  val termx_to_exp : T.term incx -> Doc.exp
  val formx_to_exp : Form4.formx -> Doc.exp

  val pp_ty    : ty pp
  val pp_termx : T.term incx pp
  val pp_formx : Form4.formx pp

  val pp_sigma : sigma pp
  val pp_deriv : (sigma * Form4.Cos.deriv) pp

  val pp_header  : unit pp
  val pp_footer  : unit pp
  val pp_comment : string pp

  val name : string
  val files : string -> dirtree list
  val build : unit -> string
end with type 'a pp := Format.formatter -> 'a -> unit

module Katex       : TO = To_katex
module Pdf         : TO = To_pdf

module Coq         : TO = To_coq
module Coq_reflect : TO = To_coq_reflect
module Lean3       : TO = To_lean3
module Lean4       : TO = To_lean4

exception Unknown of string

let select sel : (module TO) =
  match sel with
  | "katex"       -> (module Katex)
  | "coq"         -> (module Coq)
  | "coq_reflect" -> (module Coq_reflect)
  | "lean3"       -> (module Lean3)
  | "lean4"       -> (module Lean4)
  | "pdf"         -> (module Pdf)
  | mode -> raise @@ Unknown mode
