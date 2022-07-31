(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Util
open Types
open Form4_core

(******************************************************************************)
(* Formula Paths *)

type dir = [`l | `r | `i of ident | `d]
type path = dir q

type side = [`l | `r]

let flip (p : side) : side =
  match p with `l -> `r | `r -> `l

exception Bad_direction of { tycx : tycx option ; form : form ; dir : dir }

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
          with_var tycx {var = x ; ty} begin fun tycx ->
            get_at ~side tycx form path k
          end
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
      | _ ->
          raise @@ Bad_direction { tycx = None ; form = src ; dir }
    end
