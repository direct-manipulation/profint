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
      match side with
      | `l -> OTHER
      | `r -> begin
          match a, b with
          | _, TOP ->
              ignore @@ emit { name = Simp_and_true `l ; path } ; a
          | TOP, _ ->
              ignore @@ emit { name = Simp_and_true `r ; path } ; b
          | _ ->
              OTHER
        end
    end
  | Or (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path `l) side in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path `r) side in
      match side with
      | `l -> OTHER
      | `r -> begin
          match a, b with
          | _, TOP ->
              ignore @@ emit { name = Simp_or_true `l ; path } ; TOP
          | TOP, _ ->
              ignore @@ emit { name = Simp_or_true `r ; path } ; TOP
          | _ ->
              OTHER
        end
    end
  | Imp (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path `l) (flip side) in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path `r) side in
      match side, a, b with
      | side, TOP, _ ->
          ignore @@ emit { name = Simp_true_imp side ; path } ; b
      | `r, _, TOP ->
          ignore @@ emit { name = Simp_imp_true ; path } ; TOP
      | `r, BOT, _ ->
          ignore @@ emit { name = Simp_false_imp ; path } ; TOP
      | _ ->
          OTHER
    end
  | Forall (vty, b) ->
      with_var ~fresh:true fx.tycx vty begin fun vty tycx ->
        let b = { tycx ; data = b } in
        let b = recursive_simplify ~emit b (Q.snoc path (`i vty.var)) side in
        match side with
        | `l -> OTHER
        | `r -> begin
            match b with
            | TOP ->
                ignore @@ emit { name = Simp_all_true ; path } ; TOP
            | _ ->
                OTHER
          end
      end
  | Exists (vty, b) ->
      with_var ~fresh:true fx.tycx vty begin fun vty tycx ->
        let b = { tycx ; data = b } in
        recursive_simplify ~emit b (Q.snoc path (`i vty.var)) side
      end
  | Top -> TOP
  | Bot -> BOT
  | Atom _ | Eq _ -> OTHER

let recursive_simplify ~emit fx path side =
  ignore @@ recursive_simplify ~emit fx path side
