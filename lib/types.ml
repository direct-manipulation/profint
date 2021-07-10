(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util

type ty =
  | Basic of ident
  | Arrow of ty * ty
  | Tyvar of {id : int ; mutable subst : ty option}

type poly_ty = {nvars : int ; ty : ty}

let rec ty_to_exp ty =
  match ty with
  | Basic a -> Doc.(Atom (String a))
  | Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (String " -> ", Right,
                           [ty_to_exp ta ; ty_to_exp tb])))
  | Tyvar _ -> Doc.(Atom (String "_"))

let ty_to_string ty =
  ty_to_exp ty |> Doc.bracket |> Doc.lin_doc

let k_all = "\\A"
let k_ex  = "\\E"
let k_and = "\\and"
let k_top = "\\top"
let k_or  = "\\or"
let k_bot = "\\bot"
let k_imp = "\\imp"

let ty_o  = Basic "\\o"
let ty_i  = Basic "\\i"

let gsig : poly_ty IdMap.t =
  let vnum n = Tyvar {id = n ; subst = None} in
  let binds = [
    k_all, {nvars = 1 ;
            ty = Arrow (Arrow (vnum 0, ty_o), ty_o)} ;
    k_ex, {nvars = 1 ;
           ty = Arrow (Arrow (vnum 0, ty_o), ty_o)} ;
    k_and, {nvars = 0 ; ty = Arrow (ty_o, Arrow (ty_o, ty_o))} ;
    k_top, {nvars = 0 ; ty = ty_o} ;
    k_or,  {nvars = 0 ; ty = Arrow (ty_o, Arrow (ty_o, ty_o))} ;
    k_bot, {nvars = 0 ; ty = ty_o} ;
    k_imp, {nvars = 0 ; ty = Arrow (ty_o, Arrow (ty_o, ty_o))}
  ] |> List.to_seq in
  IdMap.add_seq binds IdMap.empty

type uterm =
  | Idx of int
  | Var of ident
  | Kon of ident * ty option
  | App of uterm * uterm
  | Abs of ident * ty option * uterm

type cx = (ident * ty) list
