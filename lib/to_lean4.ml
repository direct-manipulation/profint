(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Output suitable for Lean 4 *)

open! Util
open! Types
open! Term
open! Form4

let rec ty_to_exp ty =
  match ty with
  | Basic a ->
      let rep = if a = K.k_o then "Prop" else a in
      Doc.(Atom (String rep))
  | Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (StringAs (3, " → "), Right,
                           [ty_to_exp ta ; ty_to_exp tb])))
  | Tyvar v -> begin
      match v.subst with
      | None -> Doc.(Atom (String "_"))
      | Some ty -> ty_to_exp ty
    end

let pp_ty out ty = ty_to_exp ty |> Doc.bracket |> Doc.pp_lin_doc out
let ty_to_string ty = pp_to_string pp_ty ty

let rec termx_to_exp_ ~cx t =
  match t with
  | T.Abs { var ; body } ->
      with_var ~fresh:true cx { var ; ty = K.ty_any } begin fun vty cx ->
        let rep = Doc.String (Printf.sprintf "fun %s => " vty.var) in
        Doc.(Appl (1, Prefix (rep, termx_to_exp_  ~cx body)))
      end
  | T.App { head ; spine = [] } ->
      Term.head_to_exp ~cx head
  | T.App { head ; spine } ->
      let head = Term.head_to_exp ~cx head in
      let spine = List.map (termx_to_exp_ ~cx) spine in
      Doc.(Appl (100, Infix (String " ", Left, (head :: spine))))

let termx_to_exp tx = termx_to_exp_ ~cx:tx.tycx tx.data
let pp_termx out tx = termx_to_exp tx |> Doc.bracket |> Doc.pp_lin_doc out

let rec formx_to_exp_ ~cx f =
  match expose f with
  | Atom a -> termx_to_exp_ ~cx a
  | Eq (s, t, _) ->
      let s = termx_to_exp_ ~cx s in
      let t = termx_to_exp_ ~cx t in
      Doc.(Appl (40, Infix (String " = ", Non, [s ; t])))
  | And (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (30, Infix (StringAs (3, " ∧ "), Right, [a ; b])))
  | Top -> Doc.(Atom (String "True"))
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (20, Infix (StringAs (3, " ∨ "), Right, [a ; b])))
  | Bot -> Doc.(Atom (String "False"))
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (10, Infix (StringAs (3, " → "), Right, [a ; b])))
  | Forall (vty, b) ->
      with_var ~fresh:true cx vty begin fun vty cx ->
        let q = Doc.Fmt Format.(fun out ->
            pp_print_as out 3 "∀ (" ;
            pp_print_string out vty.var ;
            pp_print_string out " : " ;
            pp_ty out vty.ty ;
            pp_print_string out "), ") in
        let b = formx_to_exp_ ~cx b in
        Doc.(Appl (5, Prefix (q, b)))
      end
  | Exists (vty, b) ->
      with_var ~fresh:true cx vty begin fun vty cx ->
        let q = Doc.Fmt Format.(fun out ->
            pp_print_as out 3 "∃ (" ;
            pp_print_string out vty.var ;
            pp_print_string out " : " ;
            pp_ty out vty.ty ;
            pp_print_string out "), ") in
        let b = formx_to_exp_ ~cx b in
        Doc.(Appl (5, Prefix (q, b)))
      end
  | Mdata (_, _, f) -> formx_to_exp_ ~cx f

let formx_to_exp fx = formx_to_exp_ ~cx:fx.tycx fx.data
let pp_formx out fx = formx_to_exp fx |> Doc.bracket |> Doc.pp_lin_doc out

let pp_sigma out sg =
  Format.fprintf out "universe u@." ;
  IdSet.iter begin fun i ->
    if IdSet.mem i sigma0.basics then () else
      Format.fprintf out "variable {%s : Type u}@." i
  end sg.basics ;
  IdMap.iter begin fun k ty ->
    if IdMap.mem k sigma0.consts then () else
      Format.fprintf out "variable {%s : %s}@." k (ty_to_string @@ thaw_ty ty)
  end sg.consts

let pp_path out path =
  Q.to_seq path |>
  Format.pp_print_seq
    ~pp_sep:(fun out () -> Format.pp_print_string out ",")
    (fun out -> function
       | `l -> Format.pp_print_string out "l"
       | `r -> Format.pp_print_string out "r"
       | `d -> Format.pp_print_string out "d"
       | `i x ->
           Format.pp_print_string out "i " ;
           Format.pp_print_string out x)
    out

let pp_rule_name out rn =
  match rn with
  | Cos.Inst tx -> Format.fprintf out "inst (%a)" pp_termx tx
  | _ -> Cos.pp_rule_name out rn

let pp_deriv out (sg, deriv) =
  Format.fprintf out "section Example@." ;
  pp_sigma out sg ;
  Format.fprintf out "example (_ : %a) : %a := by@."
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  List.iter begin fun (prem, rule, _) ->
    Format.fprintf out "  within %a use %a@."
      pp_path rule.Cos.path
      pp_rule_name rule.Cos.name ;
    Format.fprintf out "  /- @[%a@] -/@." pp_formx prem ;
  end @@ List.rev deriv.middle ;
  Format.fprintf out "  rename_i u ; exact u@." ;
  Format.fprintf out "end Example@."

let pp_header out () =
  Format.fprintf out "import Profint@." ;
  Format.fprintf out "open Profint@."

let pp_footer _out () = ()

let pp_comment out str =
  Format.fprintf out "/- %s -/@\n" str

let name = "lean4"
let files pf =
  let replace contents =
    CCString.replace ~which:`Left contents
      ~sub:"/-PROOF-/\n" ~by:pf
  in [
    File { fname = "lakefile.lean" ;
           contents = [%blob "../demo/lean4/lakefile.lean"] } ;
    File { fname = "lean-toolchain" ;
           contents = [%blob "../demo/lean4/lean-toolchain"] } ;
    Dir {
      dname = "Profint" ;
      contents = [
        File { fname = "Basic.lean" ;
               contents = [%blob "../demo/lean4/Profint/Basic.lean"] } ;
      ] } ;
    File { fname = "Profint.lean" ;
           contents = [%blob "../demo/lean4/Profint.lean"] } ;
    File { fname = "Proof.lean" ;
           contents = replace [%blob "../demo/lean4/Proof.lean"] } ;
  ]
let build () = "lake build"
