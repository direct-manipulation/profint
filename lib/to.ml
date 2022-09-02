(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Types

module type INTERFACE = sig
  val ty_to_exp    : ty -> Doc.exp
  val termx_to_exp : T.term incx -> Doc.exp
  val formx_to_exp : Form4.form incx -> Doc.exp

  val pp_ty    : Format.formatter -> ty -> unit
  val pp_termx : Format.formatter -> T.term incx -> unit
  val pp_formx : Format.formatter -> Form4.form incx -> unit

  val pp_sigma : Format.formatter -> sigma -> unit
  val pp_deriv : Format.formatter -> sigma * Form4.Cos.deriv -> unit
end

module Tex : INTERFACE = To_katex

module Coq : INTERFACE = To_coq
module Lean3 : INTERFACE = To_lean3
module Lean4 : INTERFACE = To_lean4
