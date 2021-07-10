(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util

type uty =
  | Basic of ident
  | Arrow of uty * uty
  | Tyvar of {id : int ; mutable subst : uty option}

type poly_uty = {nvars : int ; uty : uty}

let gsig : (ident, poly_uty) Hashtbl.t = Hashtbl.create 19

module Consts = struct

  let k_all = "\\A"
  let k_ex  = "\\E"
  let k_and = "\\and"
  let k_top = "\\top"
  let k_or  = "\\or"
  let k_bot = "\\bot"
  let k_imp = "\\imp"

  let ty_o  = Basic "\\o"
  let ty_i  = Basic "\\i"

  let () =
    let open Hashtbl in
    let vnum n = Tyvar {id = n ; subst = None} in
    replace gsig k_all {nvars = 1 ;
                        uty = Arrow (Arrow (vnum 0, ty_o), ty_o)} ;
    replace gsig k_ex {nvars = 1 ;
                       uty = Arrow (Arrow (vnum 0, ty_o), ty_o)} ;
    replace gsig k_and {nvars = 0 ; uty = Arrow (ty_o, Arrow (ty_o, ty_o))} ;
    replace gsig k_top {nvars = 0 ; uty = ty_o} ;
    replace gsig k_or  {nvars = 0 ; uty = Arrow (ty_o, Arrow (ty_o, ty_o))} ;
    replace gsig k_bot {nvars = 0 ; uty = ty_o} ;
    replace gsig k_imp {nvars = 0 ; uty = Arrow (ty_o, Arrow (ty_o, ty_o))} ;
    ()

end

type uterm =
  | Idx of int
  | Var of ident
  | Kon of ident * uty option
  | App of uterm * uterm
  | Abs of ident * uty option * uterm

type cx = (ident * uty) list
