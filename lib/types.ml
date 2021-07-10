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

type cx = (ident * ty) list

let rec ty_to_exp ty =
  match ty with
  | Basic a -> Doc.(Atom (String a))
  | Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (String " -> ", Right,
                           [ty_to_exp ta ; ty_to_exp tb])))
  | Tyvar v -> begin
      match v.subst with
      | None ->
          let rep = "'a" ^ string_of_int v.id in
          Doc.(Atom (String rep))
      | Some ty -> ty_to_exp ty
    end

let ty_to_string ty =
  ty_to_exp ty |> Doc.bracket |> Doc.lin_doc

let k_all = "\\A"
let k_ex  = "\\E"
let k_and = "\\and"
let k_top = "\\top"
let k_or  = "\\or"
let k_bot = "\\bot"
let k_imp = "\\imp"

let k_eq  = "\\eq"

let k_pos_int = "\\rhd"
let k_neg_int = "\\circ"

let ty_o  = Basic "\\o"
let ty_i  = Basic "\\i"

let global_sig : poly_ty IdMap.t =
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
    k_imp, {nvars = 0 ; ty = Arrow (ty_o, Arrow (ty_o, ty_o))} ;
    k_eq,  {nvars = 1 ;
            ty = Arrow (vnum 0, Arrow (vnum 0, ty_o))} ;
    k_pos_int, {nvars = 0 ; ty = Arrow (ty_o, Arrow (ty_o, ty_o))} ;
    k_neg_int, {nvars = 0 ; ty = Arrow (ty_o, Arrow (ty_o, ty_o))} ;
  ] |> List.to_seq in
  IdMap.add_seq binds IdMap.empty

let lookup k local_sig =
  match IdMap.find k local_sig with
  | ty -> ty
  | exception Not_found ->
      IdMap.find k global_sig

(** Untyped terms *)
module U = struct
  type term =
    | Idx of int
    | Var of ident
    | Kon of ident * ty option
    | App of term * term
    | Abs of ident * ty option * term
end

(** Typed and normalized terms *)
module T = struct
  type term =
    | Abs of {var : ident ; body : term}
    | App of {head : head ; spine : spine}

  and head =
    | Const of ident * ty
    | Index of int

  and spine = term list

  type sub =
    | Shift of int
    | Dot of sub * term
end
