(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Util
open Types
open T
open Form4_core
open Form4_paths
open Form4_cos

(******************************************************************************)
(* Formula Simplification *)

let rec recursive_simplify ~emit (fx : formx) (path : path) (side : side) =
  match expose fx.data with
  | Mdata (md, ty, f) ->
      let f = recursive_simplify ~emit (f |@ fx) path side in
      mk_mdata md ty f.data |@ fx
  | Eq (s, t, _) when side = `r -> begin
      match s, t with
      | App { head = f ; spine = ss },
        App { head = g ; spine = ts } when Term.eq_head f g ->
          emit { name = Congr ; path } ;
          let res = compute_spine_congruence (Term.ty_infer fx.tycx f) ss ts in
          recursive_simplify ~emit (res |@ fx) path side
      | _ -> fx
    end
  | And (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path `l) side in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path `r) side in
      match side with
      | `l -> mk_and a.data b.data |@ fx
      | `r -> begin
          match expose a.data, expose b.data with
          | _, Top ->
              emit { name = Simp_and_true `l ; path } ; a
          | Top, _ ->
              emit { name = Simp_and_true `r ; path } ; b
          | _ ->
              mk_and a.data b.data |@ fx
        end
    end
  | Or (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path `l) side in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path `r) side in
      match side with
      | `l -> mk_or a.data b.data |@ fx
      | `r -> begin
          match expose a.data, expose b.data with
          | _, Top ->
              emit { name = Simp_or_true `l ; path } ; b
          | Top, _ ->
              emit { name = Simp_or_true `r ; path } ; a
          | _ ->
              mk_or a.data b.data |@ fx
        end
    end
  | Imp (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path `l) (flip side) in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path `r) side in
      match side, expose a.data, expose b.data with
      | _, Top, _ ->
          emit { name = Simp_true_imp ; path } ; b
      | `r, _, Top ->
          emit { name = Simp_imp_true ; path } ; b
      | `r, Bot, _ ->
          emit { name = Simp_false_imp ; path } ;
          mk_top |@ fx
      | _ ->
          mk_imp a.data b.data |@ fx
    end
  | Forall (vty, b) ->
      with_var ~fresh:true fx.tycx vty begin fun vty tycx ->
        let b = { tycx ; data = b } in
        let b = recursive_simplify ~emit b (Q.snoc path `d) side in
        match side with
        | `l -> mk_all vty b.data |@ fx
        | `r -> begin
            match expose b.data with
            | Top ->
                emit { name = Simp_all_true ; path } ; b
            | _ ->
                mk_all vty b.data |@ fx
          end
      end
  | Exists (vty, b) ->
      with_var ~fresh:true fx.tycx vty begin fun vty tycx ->
        let b = { tycx ; data = b } in
        let b = recursive_simplify ~emit b (Q.snoc path `d) side in
        mk_ex vty b.data |@ fx
      end
  | Atom _ | Eq _ | Top | Bot -> fx
