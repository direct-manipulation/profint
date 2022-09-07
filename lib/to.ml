(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Types

module type INTERFACE = sig
  open Format

  val ty_to_exp    : ty -> Doc.exp
  val termx_to_exp : T.term incx -> Doc.exp
  val formx_to_exp : Form4.form incx -> Doc.exp

  val pp_ty    : formatter -> ty -> unit
  val pp_termx : formatter -> T.term incx -> unit
  val pp_formx : formatter -> Form4.form incx -> unit

  val pp_sigma : formatter -> sigma -> unit
  val pp_deriv : formatter -> sigma * Form4.Cos.deriv -> unit

  val pp_header : formatter -> unit
  val pp_footer : formatter -> unit
  val pp_comment : formatter -> string -> unit
end

module Katex : INTERFACE = To_katex

module Coq : INTERFACE = To_coq
module Coq_reflect : INTERFACE = To_coq_reflect
module Lean3 : INTERFACE = To_lean3
module Lean4 : INTERFACE = To_lean4
