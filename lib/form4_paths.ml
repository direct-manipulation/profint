(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

open Util
open Types
open Form4_core
open Mk

(******************************************************************************)
(* Formula Paths *)

type dir = [`l | `r | `i of Ident.t | `d]
type path = dir q

type side = [`l | `r]

let flip (p : side) : side =
  match p with `l -> `r | `r -> `l

exception Bad_direction of { tycx : tycx option ; form : form ; dir : dir }

let rec go (fx : formx) (dir : dir) =
  match expose fx.data, dir with
  | ( And (a, b) | Or (a, b) | Imp (a, b) ), (`l | `r) ->
      ({ fx with data = if Poly.(dir = `l) then a else b }, dir)
  | Forall ({ var ; ty }, b), `d
  | Forall ({ ty ; _ }, b), `i var
  | Exists ({ var ; ty }, b), `d
  | Exists ({ ty ; _ }, b), `i var ->
      with_var fx.tycx { var ; ty } begin fun {var ; _} tycx ->
        ({ tycx ; data = b }, `i var)
      end
  | Mdata (_, _, f), _ ->
      go { fx with data = f } dir
  | _ -> raise @@ Bad_direction { tycx = Some fx.tycx ;
                                  form = fx.data ; dir }

let rec get_at ?(side = `r) tycx form (path : path) k =
  match Q.take_front_exn path with
  | exception Q.Empty -> k tycx form side
  | dir, path -> begin
      match expose form, dir with
      | And (form, _), `l
      | Or (form, _), `l ->
          get_at ~side tycx form path k
      | Imp (form, _), `l ->
          get_at ~side:(flip side) tycx form path k
      | And (_, form), `r
      | Or (_, form), `r
      | Imp (_, form), `r ->
          get_at ~side tycx form path k
      | Forall ({ ty ; _ }, form), `i x
      | Forall ({ var = x ; ty }, form), `d
      | Exists ({ ty ; _ }, form), `i x
      | Exists ({ var = x ; ty }, form), `d ->
          with_var tycx {var = x ; ty} begin fun _ tycx ->
            get_at ~side tycx form path k
          end
      | Mdata (_, _, f), _ ->
          get_at ~side tycx f path k
      | _ ->
          raise @@ Bad_direction { tycx = Some tycx ; form ; dir }
    end

let formx_at ?side (formx : formx) path : formx * side =
  get_at ?side formx.tycx formx.data path (fun tycx form side -> ({ tycx ; data = form }, side))

let side_at ?side tycx form path =
  get_at ?side tycx form path (fun _ _ side -> side)

let rec replace_at (src : form) (path : path) (repl : form) : form =
  match Q.take_front_exn path with
  | exception Q.Empty -> repl
  | dir, path -> begin
      match expose src, dir with
      | And (a, b), `l -> mk_and (replace_at a path repl) b
      | And (a, b), `r -> mk_and a (replace_at b path repl)
      | Or (a, b), `l -> mk_or (replace_at a path repl) b
      | Or (a, b), `r -> mk_or a (replace_at b path repl)
      | Imp (a, b), `l -> mk_imp (replace_at a path repl) b
      | Imp (a, b), `r -> mk_imp a (replace_at b path repl)
      | Forall ({ ty ; _ }, a), `i x
      | Forall ({ ty ; var = x }, a), `d ->
          mk_all { var = x ; ty } (replace_at a path repl)
      | Exists ({ ty ; _ }, a), `i x
      | Exists ({ ty ; var = x }, a), `d ->
          mk_ex { var = x ; ty } (replace_at a path repl)
      | Mdata (md, ty, a), _ ->
          mk_mdata md ty @@ replace_at a path repl
      | _ ->
          raise @@ Bad_direction { tycx = None ; form = src ; dir }
    end

let rec transform_at (src : form) (path : path) (fn : form -> form) : form =
  match Q.take_front_exn path with
  | exception Q.Empty -> fn src
  | dir, path -> begin
      match expose src, dir with
      | And (a, b), `l -> mk_and (transform_at a path fn) b
      | And (a, b), `r -> mk_and a (transform_at b path fn)
      | Or (a, b), `l -> mk_or (transform_at a path fn) b
      | Or (a, b), `r -> mk_or a (transform_at b path fn)
      | Imp (a, b), `l -> mk_imp (transform_at a path fn) b
      | Imp (a, b), `r -> mk_imp a (transform_at b path fn)
      | Forall ({ ty ; _ }, a), `i x
      | Forall ({ ty ; var = x }, a), `d ->
          mk_all { var = x ; ty } (transform_at a path fn)
      | Exists ({ ty ; _ }, a), `i x
      | Exists ({ ty ; var = x }, a), `d ->
          mk_ex { var = x ; ty } (transform_at a path fn)
      | Mdata (md, ty, a), _ ->
          mk_mdata md ty @@ transform_at a path fn
      | _ ->
          raise @@ Bad_direction { tycx = None ; form = src ; dir }
    end
