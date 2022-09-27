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
open Form4_paths
open Form4_cos

(******************************************************************************)
(* Formula Simplification *)

let prin (cp : cos_premise) = cp.prin

type simply_result = TOP | BOT | OTHER of form

let rec recursive_simplify ~(emit : rule -> cos_premise) (fx : formx) (path : path) (side : Side.t) =
  match expose fx.data with
  | Mdata (_, _, f) ->
      recursive_simplify ~emit (f |@ fx) path side
  | Eq (s, t, _) when Side.equal side R -> begin
      match s, t with
      | T.App { head = f ; _ }, T.App { head = g ; _ }
          when T.equal_head f g ->
            let res = emit { name = Congr ; path } |> prin in
            recursive_simplify ~emit res path side
      | _ -> OTHER fx.data
    end
  | And (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path L) side in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path R) side in
      match a, b with
      | _, TOP ->
          emit { name = Simp_and_top { cxkind = side ; minor = L } ; path }
          |> ignore ; a
      | _, BOT ->
          emit { name = Simp_and_bot { cxkind = side ; minor = L } ; path }
          |> ignore ; BOT
      | TOP, _ ->
          emit { name = Simp_and_top { cxkind = side ; minor = R } ; path }
          |> ignore ; b
      | BOT, _ ->
          emit { name = Simp_and_bot { cxkind = side ; minor = R } ; path }
          |> ignore ; BOT
      | OTHER a, OTHER b ->
          OTHER (Mk.mk_and a b)
    end
  | Or (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path L) side in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path R) side in
      match a, b with
      | _, TOP ->
          emit { name = Simp_or_top { cxkind = side ; minor = L } ; path }
          |> ignore ; TOP
      | _, BOT ->
          emit { name = Simp_or_bot { cxkind = side ; minor = L } ; path }
          |> ignore ; a
      | TOP, _ ->
          emit { name = Simp_or_top { cxkind = side ; minor = R } ; path }
          |> ignore ; TOP
      | BOT, _ ->
          emit { name = Simp_or_top { cxkind = side ; minor = R } ; path }
          |> ignore ; b
      | OTHER a, OTHER b ->
          OTHER (Mk.mk_or a b)
    end
  | Imp (a, b) -> begin
      let a = recursive_simplify ~emit (a |@ fx) (Q.snoc path L) (flip side) in
      let b = recursive_simplify ~emit (b |@ fx) (Q.snoc path R) side in
      match a, b with
      | TOP, _ ->
          emit { name = Simp_imp_top { cxkind = side ; minor = R } ; path }
          |> ignore ; b
      | _, TOP ->
          emit { name = Simp_imp_top { cxkind = side ; minor = L } ; path }
          |> ignore ; TOP
      | BOT, _ ->
          emit { name = Simp_bot_imp { cxkind = side } ; path }
          |> ignore ; TOP
      | OTHER a, BOT ->
          OTHER (Mk.mk_imp a Mk.mk_bot)
      | OTHER a, OTHER b ->
          OTHER (Mk.mk_imp a b)
    end
  | Forall (vty, b) ->
      with_var fx.tycx vty begin fun vty tycx ->
        let b = { tycx ; data = b } in
        let b = recursive_simplify ~emit b (Q.snoc path (I vty.var)) side in
        match b with
        | TOP ->
            emit { name = Simp_all_top { cxkind = side } ; path }
            |> ignore ; TOP
        | BOT ->
            OTHER (Mk.mk_all vty Mk.mk_bot)
        | OTHER b -> begin
            if not @@ Side.equal side L then OTHER (Mk.mk_all vty b) else
            match Option.(ubind 0 b >>= Term.lower ~above:0 ~by:1) with
            | Some t -> begin
                (* Caml.Format.printf "Found u-subst: %s := %a@.For: %a@." *)
                (*   (Ident.to_string vty.var) *)
                (*   (Term.pp_term ~cx:fx.tycx) t *)
                (*   (pp_form ~cx:tycx) b ; *)
                let cpr = emit { name = Inst { side ; term = t |@ fx } ; path } in
                let b = cpr.prin in
                (* Caml.Format.printf "Result of u-subst: %a@.prin = %a@." *)
                (*   pp_formx cpr.goal *)
                (*   pp_formx b ; *)
                recursive_simplify ~emit b path side
              end
            | None ->
                OTHER (Mk.mk_all vty b)
          end
      end
  | Exists (vty, b) ->
      with_var fx.tycx vty begin fun vty tycx ->
        let b = { tycx ; data = b } in
        let b = recursive_simplify ~emit b (Q.snoc path (I vty.var)) side in
        match b with
        | BOT ->
            emit { name = Simp_ex_bot { cxkind = side } ; path }
            |> ignore ; BOT
        | TOP ->
            OTHER (Mk.mk_ex vty Mk.mk_top)
        | OTHER b -> begin
            if not @@ Side.equal side R then OTHER (Mk.mk_ex vty b) else
            match Option.(ebind 0 b >>= Term.lower ~above:0 ~by:1) with
            | Some t -> begin
                (* Caml.Format.printf "Found e-subst: %s := %a@.For: %a@." *)
                (*   (Ident.to_string vty.var) *)
                (*   (Term.pp_term ~cx:fx.tycx) t *)
                (*   (pp_form ~cx:tycx) b ; *)
                let cpr = emit { name = Inst { side ; term = t |@ fx } ; path } in
                let b = cpr.prin in
                (* Caml.Format.printf "Result of e-subst: %a@.prin = %a@." *)
                (*   pp_formx cpr.goal *)
                (*   pp_formx b ; *)
                recursive_simplify ~emit b path side
              end
            | None ->
                OTHER (Mk.mk_ex vty b)
          end
      end
  | Top -> TOP
  | Bot -> BOT
  | Atom _ | Eq _ -> OTHER fx.data

and ebind n f =
  match expose f with
  | Eq (s, t, _) -> begin
      let u = T.App { head = Index n ; spine = [] } in
      if Term.eq_term u s && suitable n t then Some t else
      if Term.eq_term u t && suitable n s then Some s else None
    end
  | And (f, g) -> begin
      match ebind n f with
      | Some _ as ret -> ret
      | None -> ebind n g
    end
  | Or (f, g) ->
      Option.(
        ebind n f >>= fun s ->
        ebind n g >>= fun t ->
        if Term.eq_term s t then Some s else None)
  | Imp (_, g) ->
      ebind n g
  | Forall (_, f) | Exists (_, f) ->
      Option.(
        ebind (n + 1) f >>= fun t ->
        Term.lower ~above:0 ~by:1 t)
  | Top | Bot | Atom _ -> None
  | Mdata (_, _, f) -> ebind n f

and ubind n f =
  match expose f with
  | And (f, g) ->
      Option.(
        ubind n f >>= fun s ->
        ubind n g >>= fun t ->
        if Term.eq_term s t then Some s else None)
  | Imp (f, g) -> begin
      match ebind n f with
      | Some _ as ret -> ret
      | None -> ubind n g
    end
  | Forall (_, f) | Exists (_, f) ->
      Option.(
        ubind (n + 1) f >>= fun t ->
        Term.lower ~above:0 ~by:1 t)
  | Top | Or _ | Bot | Eq _ | Atom _ -> None
  | Mdata (_, _, f) -> ubind n f

and suitable n t =
  match t with
  | T.App { head ; spine } ->
      suitable_head n head && List.for_all spine ~f:(suitable n)
  | T.Abs { body ; _ } ->
      suitable (n + 1) body

and suitable_head n head =
  match head with
  | T.Const _ -> true
  | T.Index k -> k > n

let recursive_simplify ~emit fx path side =
  ignore @@ recursive_simplify ~emit fx path side
