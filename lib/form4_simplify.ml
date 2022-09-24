(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Util
open Types
open Form4_core
open Form4_paths
open Form4_cos

(******************************************************************************)
(* Formula Simplification *)

let prin (cp : cos_premise) = cp.prin

type simply_result = TOP | BOT | OTHER

let rec recursive_simplify ~(emit : rule -> cos_premise) (fx : formx) (path : path) (side : side) =
  match expose fx.data with
  | Mdata (_, _, f) ->
      recursive_simplify ~emit (f |@ fx) path side
  | Eq (s, t, _) when side = `r -> begin
      match s, t with
      | T.App { head = f ; _ }, T.App { head = g ; _ }
          when f = g ->
            let res = emit { name = Congr ; path } |> prin in
            recursive_simplify ~emit res path side
      | _ -> OTHER
    end
  | And (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path `l) side in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path `r) side in
      match a, b with
      | _, TOP ->
          emit { name = Simp_and_top { cxkind = side ; minor = `l } ; path }
          |> ignore ; a
      | _, BOT ->
          emit { name = Simp_and_bot { cxkind = side ; minor = `l } ; path }
          |> ignore ; BOT
      | TOP, _ ->
          emit { name = Simp_and_top { cxkind = side ; minor = `r } ; path }
          |> ignore ; b
      | BOT, _ ->
          emit { name = Simp_and_bot { cxkind = side ; minor = `r } ; path }
          |> ignore ; BOT
      | OTHER, OTHER -> OTHER
    end
  | Or (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path `l) side in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path `r) side in
      match a, b with
      | _, TOP ->
          emit { name = Simp_or_top { cxkind = side ; minor = `l } ; path }
          |> ignore ; TOP
      | _, BOT ->
          emit { name = Simp_or_bot { cxkind = side ; minor = `l } ; path }
          |> ignore ; a
      | TOP, _ ->
          emit { name = Simp_or_top { cxkind = side ; minor = `r } ; path }
          |> ignore ; TOP
      | BOT, _ ->
          emit { name = Simp_or_top { cxkind = side ; minor = `r } ; path }
          |> ignore ; b
      | OTHER, OTHER -> OTHER
    end
  | Imp (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path `l) (flip side) in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path `r) side in
      match a, b with
      | TOP, _ ->
          emit { name = Simp_imp_top { cxkind = side ; minor = `r } ; path }
          |> ignore ; b
      | _, TOP ->
          emit { name = Simp_imp_top { cxkind = side ; minor = `l } ; path }
          |> ignore ; TOP
      | BOT, _ ->
          emit { name = Simp_bot_imp { cxkind = side } ; path }
          |> ignore ; TOP
      | ( _, BOT | OTHER, OTHER ) ->
          OTHER
    end
  | Forall (vty, b) ->
      with_var fx.tycx vty begin fun vty tycx ->
        let b = { tycx ; data = b } in
        let b = recursive_simplify ~emit b (Q.snoc path (`i vty.var)) side in
        match b with
        | TOP ->
            emit { name = Simp_all_top { cxkind = side } ; path }
            |> ignore ; TOP
        | _ -> OTHER
      end
  | Exists (vty, b) ->
      with_var fx.tycx vty begin fun vty tycx ->
        let b = { tycx ; data = b } in
        let b = recursive_simplify ~emit b (Q.snoc path (`i vty.var)) side in
        match b with
        | BOT ->
            emit { name = Simp_ex_bot { cxkind = side } ; path }
            |> ignore ; BOT
        | _ -> OTHER
      end
  | Top -> TOP
  | Bot -> BOT
  | Atom _ | Eq _ -> OTHER

let recursive_simplify ~emit fx path side =
  ignore @@ recursive_simplify ~emit fx path side
