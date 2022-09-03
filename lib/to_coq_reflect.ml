(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Output suitable for Coq *)

open! Util
open! Types
open! Term
open! Form4

include To_coq

let pp_rule out goal rule =
  let pp_rule cx f name =
    match name with
    | Cos.Init -> begin
        let fail () =
          unprintable @@ "init: got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = f } in
        match expose f with
        | Imp (a, b) when Term.eq_term a b ->
            Format.fprintf out "RN_init"
        | _ -> fail ()
      end
    | Cos.Congr -> begin
        let fail () =
          unprintable @@ "congr: got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = f } in
        match expose f with
        | Eq (s, t, _) when Term.eq_term s t ->
            Format.fprintf out "RN_congr"
        | _ -> fail ()
      end
    | Cos.Inst tx -> begin
        Format.fprintf out "RN_inst (" ;
        List.rev tx.tycx.linear |>
        List.iter begin fun vty ->
          Format.fprintf out "fun (%s : %a) => " vty.var pp_ty vty.ty
        end ;
        Format.fprintf out "%a)" pp_termx tx
      end
    | _ ->
        Format.pp_print_string out "RN_" ;
        Cos.pp_rule_name out name
  in
  let rec pp_path n cx f0 dirs path =
    match Q.take_front path with
    | None -> (List.rev dirs, cx, f0)
    | Some (dir, path) -> begin
        match expose f0, dir with
        | And (f, _), `l ->
            pp_path (n + 1) cx f (0 :: dirs) path
        | And (_, f), `r ->
            pp_path (n + 1) cx f (1 :: dirs) path
        | Or (f, _), `l ->
            pp_path (n + 1) cx f (0 :: dirs) path
        | Or (_, f), `r ->
            pp_path (n + 1) cx f (1 :: dirs) path
        | Imp (f, _), `l ->
            pp_path (n + 1) cx f (0 :: dirs) path
        | Imp (_, f), `r ->
            pp_path (n + 1) cx f (1 :: dirs) path
        | Forall ({ var ; ty }, f), `d
        | Forall ({ ty ; _ }, f), `i var ->
            with_var ~fresh:true cx { var ; ty } begin fun _ cx ->
              pp_path (n + 1) cx f (0 :: dirs) path
            end
        | Exists ({ var ; ty }, f), `d
        | Exists ({ ty ; _ }, f), `i var ->
            with_var ~fresh:true cx { var ; ty } begin fun _ cx ->
              pp_path (n + 1) cx f (0 :: dirs) path
            end
        | _ ->
            String.concat " " [ "pp_rule:" ;
                                pp_to_string Cos.pp_rule rule ;
                                "::" ;
                                pp_to_string pp_formx goal ]
            |> unprintable
      end
  in
  let trail, cx, f = pp_path 1 goal.tycx goal.data [] rule.path in
  let trail = "[" ^ ( trail |> List.map string_of_int |> String.concat ";" ) ^ "]" in
  Format.pp_print_string out "(" ;
  pp_rule cx f rule.Cos.name ;
  Format.pp_print_string out ", " ;
  Format.pp_print_string out trail ;
  Format.pp_print_string out ")"

let pp_step out (prem, rule, concl) =
  pp_rule out concl rule ;
  Format.fprintf out "@,(* %a *)" pp_formx prem

let pp_deriv out (sg, deriv) =
  Format.fprintf out "Section Example.@." ;
  pp_sigma out sg ;
  Format.fprintf out "Goal (%a) -> %a.@."
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  Format.fprintf out {|  let h := fresh "H" in@.|} ;
  Format.fprintf out {|  intro h ;@.|} ;
  Format.fprintf out {|  let deriv := fresh "deriv" in@.|} ;
  Format.fprintf out {|  pose (deriv := @[<v2>[ %a ] : Profint.deriv@]) ;@.|}
    (Format.pp_print_list pp_step
       ~pp_sep:(fun out () -> Format.fprintf out " ;@,"))
    (List.rev deriv.Cos.middle) ;
  Format.fprintf out {|  apply (Profint.correctness deriv) ;@.|} ;
  Format.fprintf out {|  unfold deriv ; Profint.check_solve.@.|} ;
  Format.fprintf out {|Qed.@.End Example.@.|}