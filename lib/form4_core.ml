(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

open! Util
open! Types
open! T

type form = term
type formx = form incx

(******************************************************************************)
(* formula views *)

type fskel =
  | Atom   of term
  | Eq     of term * term * Ty.t
  | And    of form * form
  | Top
  | Or     of form * form
  | Bot
  | Imp    of form * form
  | Forall of typed_var * form
  | Exists of typed_var * form
  | Mdata  of term * Ty.t * form

let expose (form : form) =
  match form with
  | App { head = Const (k, ty) ; spine = [md ; f] } when Ident.equal k K.k_mdata ->
      Mdata (md, ty, f)
  | App { head = Const (k, _) ; spine = [] } when Ident.equal k K.k_top ->
      Top
  | App { head = Const (k, _) ; spine = [] } when Ident.equal k K.k_bot ->
      Bot
  | App { head = Const (k, _) ; spine = [fa ; fb] } when Ident.equal k K.k_and ->
      And (fa, fb)
  | App { head = Const (k, _) ; spine = [fa ; fb] } when Ident.equal k K.k_or ->
      Or (fa, fb)
  | App { head = Const (k, _) ; spine = [fa ; fb] } when Ident.equal k K.k_imp ->
      Imp (fa, fb)
  | App { head = Const (k, Arrow (ty, _)) ; spine = [t1 ; t2] } when Ident.equal k K.k_eq ->
      Eq (t1, t2, ty)
  | App { head = Const (k, Arrow (Arrow (ty, _), _)) ;
          spine = [Abs { var ; body }] } when Ident.equal k K.k_all ->
      Forall ({ var ; ty }, body)
  | App { head = Const (k, Arrow (Arrow (ty, _), _)) ;
          spine = [Abs { var ; body }] } when Ident.equal k K.k_ex ->
      Exists ({ var ; ty }, body)
  | _ ->
      Atom form

(******************************************************************************)
(* pretty printing *)

open Term

let rec form_to_exp ~cx f =
  match expose f with
  | Atom a -> term_to_exp ~cx a
  | Eq (s, t, _) ->
      let s = term_to_exp ~cx s in
      let t = term_to_exp ~cx t in
      Doc.(Appl (40, Infix (string " = ", Non, [s ; t])))
  | And (a, b) ->
      let a = form_to_exp ~cx a in
      let b = form_to_exp ~cx b in
      Doc.(Appl (30, Infix (string_as 3 " ∧ ", Right, [a ; b])))
  | Top -> Doc.(Atom (string "True"))
  | Or (a, b) ->
      let a = form_to_exp ~cx a in
      let b = form_to_exp ~cx b in
      Doc.(Appl (20, Infix (string_as 3 " ∨ ", Right, [a ; b])))
  | Bot -> Doc.(Atom (string "False"))
  | Imp (a, b) ->
      let a = form_to_exp ~cx a in
      let b = form_to_exp ~cx b in
      Doc.(Appl (10, Infix (string_as 3 " → ", Right, [a ; b])))
  | Forall (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let q = Caml.Format.(fun out ->
            pp_print_as out 3 "∀ (" ;
            pp_print_string out (Ident.to_string vty.var) ;
            pp_print_string out " : " ;
            Ty.pp out vty.ty ;
            pp_print_string out "), ") in
        let b = form_to_exp ~cx b in
        Doc.(Appl (5, Prefix (q, b)))
      end
  | Exists (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let q = Caml.Format.(fun out ->
            pp_print_as out 3 "∃ (" ;
            pp_print_string out (Ident.to_string vty.var) ;
            pp_print_string out " : " ;
            Ty.pp out vty.ty ;
            pp_print_string out "), ") in
        let b = form_to_exp ~cx b in
        Doc.(Appl (5, Prefix (q, b)))
      end
  | Mdata (_, _, f) -> form_to_exp ~cx f

let formx_to_exp (fx : formx) = form_to_exp ~cx:fx.tycx fx.data

let pp_form ~cx out f = form_to_exp ~cx f |> Doc.bracket |> Doc.pp_linear out
let pp_formx out (fx : formx) = pp_form ~cx:fx.tycx out fx.data

let form_to_string ~cx f = pp_to_string (pp_form ~cx) f
let formx_to_string fx = pp_to_string pp_formx fx

(******************************************************************************)
(* convenience functions *)

module Mk = struct

  let ty_ooo = Ty.Arrow (Ty.o, Ty.Arrow (Ty.o, Ty.o))

  let mk_eq t1 t2 ty =
    App { head = Const (K.k_eq, Ty.Arrow (ty, Ty.Arrow (ty, Ty.o))) ;
          spine = [t1 ; t2] }
  let mk_and fa fb =
    App { head = Const (K.k_and, ty_ooo) ; spine = [fa ; fb] }
  let mk_top = App { head = Const (K.k_top, Ty.o) ; spine = [] }
  let mk_or fa fb =
    App { head = Const (K.k_or, ty_ooo) ; spine = [fa ; fb] }
  let mk_bot = App { head = Const (K.k_bot, Ty.o) ; spine = [] }
  let mk_imp fa fb =
    App { head = Const (K.k_imp, ty_ooo) ; spine = [fa ; fb] }
  let mk_all vty body =
    App { head = Const (K.k_all, Ty.Arrow (Ty.Arrow (vty.ty, Ty.o), Ty.o)) ;
          spine = [Abs { var = vty.var ; body }] }
  let mk_ex vty body =
    App { head = Const (K.k_ex, Ty.Arrow (Ty.Arrow (vty.ty, Ty.o), Ty.o)) ;
          spine = [Abs { var = vty.var ; body }] }
  let mk_mdata md ty f =
    App { head = Const (K.k_mdata, Ty.Arrow (ty, Ty.Arrow (Ty.o, Ty.o))) ;
          spine = [md ; f] }

end
