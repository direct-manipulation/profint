(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util
open! Types
open! T

type form = term
type formx = form incx

let form_to_exp = Term.term_to_exp
let formx_to_exp (fx : formx) = Term.term_to_exp ~cx:fx.tycx fx.data

let pp_form = Term.pp_term
let pp_formx out (fx : formx) = Term.pp_term ~cx:fx.tycx out fx.data

let form_to_string = Term.term_to_string
let formx_to_string (fx : formx) = Term.term_to_string ~cx:fx.tycx fx.data

(******************************************************************************)
(* formula views *)

type fskel =
  | Atom   of term
  | Eq     of term * term * ty
  | And    of form * form
  | Top
  | Or     of form * form
  | Bot
  | Imp    of form * form
  | Forall of typed_var * form
  | Exists of typed_var * form
  | Mdata  of term * ty * form

let expose (form : form) =
  match form with
  | App { head = Const (k, ty) ; spine = [md ; f] } when k = K.k_mdata ->
      Mdata (md, ty, f)
  | App { head = Const (k, _) ; spine = [] } when k = K.k_top ->
      Top
  | App { head = Const (k, _) ; spine = [] } when k = K.k_bot ->
      Bot
  | App { head = Const (k, _) ; spine = [fa ; fb] } when k = K.k_and ->
      And (fa, fb)
  | App { head = Const (k, _) ; spine = [fa ; fb] } when k = K.k_or ->
      Or (fa, fb)
  | App { head = Const (k, _) ; spine = [fa ; fb] } when k = K.k_imp ->
      Imp (fa, fb)
  | App { head = Const (k, Arrow (ty, _)) ; spine = [t1 ; t2] } when k = K.k_eq ->
      Eq (t1, t2, ty)
  | App { head = Const (k, Arrow (Arrow (ty, _), _)) ;
          spine = [Abs { var ; body }] } when k = K.k_all ->
      Forall ({ var ; ty }, body)
  | App { head = Const (k, Arrow (Arrow (ty, _), _)) ;
          spine = [Abs { var ; body }] } when k = K.k_ex ->
      Exists ({ var ; ty }, body)
  | _ ->
      Atom form

let ty_ooo = Arrow (K.ty_o, Arrow (K.ty_o, K.ty_o))

let mk_eq t1 t2 ty =
  App { head = Const (K.k_eq, Arrow (ty, Arrow (ty, K.ty_o))) ;
        spine = [t1 ; t2] }
let mk_and fa fb =
  App { head = Const (K.k_and, ty_ooo) ; spine = [fa ; fb] }
let mk_top = App { head = Const (K.k_top, K.ty_o) ; spine = [] }
let mk_or fa fb =
  App { head = Const (K.k_or, ty_ooo) ; spine = [fa ; fb] }
let mk_bot = App { head = Const (K.k_bot, K.ty_o) ; spine = [] }
let mk_imp fa fb =
  App { head = Const (K.k_imp, ty_ooo) ; spine = [fa ; fb] }
let mk_all vty body =
  App { head = Const (K.k_all, Arrow (Arrow (vty.ty, K.ty_o), K.ty_o)) ;
        spine = [Abs { var = vty.var ; body }] }
let mk_ex vty body =
  App { head = Const (K.k_ex, Arrow (Arrow (vty.ty, K.ty_o), K.ty_o)) ;
        spine = [Abs { var = vty.var ; body }] }
let mk_mdata md ty f =
  App { head = Const (K.k_mdata, Arrow (ty, Arrow (K.ty_o, K.ty_o))) ;
        spine = [md ; f] }
