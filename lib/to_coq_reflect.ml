(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Output suitable for Coq *)

open Base

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
            Stdlib.Format.fprintf out "RN_init"
        | _ -> fail ()
      end
    | Cos.Congr -> begin
        let fail () =
          unprintable @@ "congr: got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = f } in
        match expose f with
        | Eq (s, t, _) when Term.eq_term s t ->
            Stdlib.Format.fprintf out "RN_congr"
        | _ -> fail ()
      end
    | Cos.Inst { side ; term = tx ; ty } -> begin
        Stdlib.Format.fprintf out "RN_inst_%s ("
          (match side with L -> "l" | _ -> "r") ;
        List.rev tx.tycx.linear |>
        List.iter ~f:begin fun vty ->
          Stdlib.Format.fprintf out "fun (%s : %a) => " (Ident.to_string vty.var) pp_ty vty.ty
        end ;
        Stdlib.Format.fprintf out "%a)" (pp_termx ty) tx
      end
    | Cos.Rename _ ->
        Stdlib.Format.pp_print_string out "RN_repeat"
    | _ ->
        Stdlib.Format.pp_print_string out "RN_" ;
        Cos.pp_rule_name out name
  in
  let rec pp_path n cx f0 dirs path =
    match Path.expose_front path with
    | None -> (List.rev dirs, cx, f0)
    | Some (dir, path) -> begin
        match expose f0, dir with
        | And (f, _), Path.Dir.L ->
            pp_path (n + 1) cx f (0 :: dirs) path
        | And (_, f), R ->
            pp_path (n + 1) cx f (1 :: dirs) path
        | Or (f, _), L ->
            pp_path (n + 1) cx f (0 :: dirs) path
        | Or (_, f), R ->
            pp_path (n + 1) cx f (1 :: dirs) path
        | Imp (f, _), L ->
            pp_path (n + 1) cx f (0 :: dirs) path
        | Imp (_, f), R ->
            pp_path (n + 1) cx f (1 :: dirs) path
        | Forall ({ var ; ty }, f), L ->
            with_var cx { var ; ty } begin fun _ cx ->
              pp_path (n + 1) cx f (0 :: dirs) path
            end
        | Exists ({ var ; ty }, f), L ->
            with_var cx { var ; ty } begin fun _ cx ->
              pp_path (n + 1) cx f (0 :: dirs) path
            end
        | _ ->
            String.concat ~sep:" "
              [ "pp_rule:" ;
                pp_to_string Cos.pp_rule rule ;
                "::" ;
                pp_to_string pp_formx goal ]
            |> unprintable
      end
  in
  let trail, cx, f = pp_path 1 goal.tycx goal.data [] rule.path in
  let trail = "[" ^ ( trail |> List.map ~f:Int.to_string |> String.concat ~sep:";" ) ^ "]" in
  Stdlib.Format.pp_print_string out "(" ;
  pp_rule cx f rule.Cos.name ;
  Stdlib.Format.pp_print_string out ", " ;
  Stdlib.Format.pp_print_string out trail ;
  Stdlib.Format.pp_print_string out ")"

let pp_step out (prem, rule, concl) =
  pp_rule out concl rule ;
  Stdlib.Format.fprintf out "@,(* %a *)" pp_formx prem

let pp_deriv out (sg, deriv) =
  Stdlib.Format.fprintf out "Section Example.@." ;
  pp_sigma out sg ;
  Stdlib.Format.fprintf out "Goal (%a) -> %a.@."
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  Stdlib.Format.fprintf out {|  let h := fresh "H" in@.|} ;
  Stdlib.Format.fprintf out {|  intro h ;@.|} ;
  Stdlib.Format.fprintf out {|  let deriv := fresh "deriv" in@.|} ;
  Stdlib.Format.fprintf out {|  pose (deriv := @[<v2>[ %a ] : Profint.deriv@]) ;@.|}
    (Stdlib.Format.pp_print_list pp_step
       ~pp_sep:(fun out () -> Stdlib.Format.fprintf out " ;@,"))
    (List.rev deriv.Cos.middle) ;
  Stdlib.Format.fprintf out {|  apply (Profint.correctness deriv) ;@.|} ;
  Stdlib.Format.fprintf out {|  unfold deriv ; Profint.check_solve.@.|} ;
  Stdlib.Format.fprintf out {|Qed.@.End Example.@.|}

let name = "coq_reflect"
let files pf =
  let replace contents =
    String.substr_replace_first contents
      ~pattern:"(*PROOF*)\n" ~with_:pf
  in [
    File { fname = "Proof.v" ;
           contents = replace [%blob "lib/systems/coq_reflect/Proof.v"] } ;
    File { fname = "Profint.v" ;
           contents = [%blob "lib/systems/coq_reflect/Profint.v"] } ;
    File { fname = "_CoqProject" ;
           contents = [%blob "lib/systems/coq_reflect/_CoqProject"] } ;
    File { fname = "Makefile" ;
           contents = [%blob "lib/systems/coq_reflect/Makefile"] } ;
  ]
let build () = "make"
