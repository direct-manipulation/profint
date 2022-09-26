(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Output suitable for Lean 4 *)

open Base

open Util
open Types
open Form4

let rec ty_to_exp ty =
  match ty with
  | Ty.Basic a ->
      let rep = if Ident.equal a Ty.k_o then "Prop" else Ident.to_string a in
      Doc.(Atom (string rep))
  | Ty.Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (string_as 3 " → ", Right,
                           [ty_to_exp ta ; ty_to_exp tb])))
  | Ty.Var v -> begin
      match v.subst with
      | None -> Doc.(Atom (string "_"))
      | Some ty -> ty_to_exp ty
    end

let pp_ty out ty = ty_to_exp ty |> Doc.bracket |> Doc.pp_linear out
let ty_to_string ty = pp_to_string pp_ty ty

let rec termx_to_exp_ ~cx t =
  match t with
  | T.Abs { var ; body } ->
      with_var cx { var ; ty = K.ty_any } begin fun vty cx ->
        let rep = Doc.string (Printf.sprintf "fun %s => " (Ident.to_string vty.var)) in
        Doc.(Appl (1, Prefix (rep, termx_to_exp_  ~cx body)))
      end
  | T.App { head ; spine = [] } ->
      Term.head_to_exp ~cx head
  | T.App { head ; spine } ->
      let head = Term.head_to_exp ~cx head in
      let spine = List.map ~f:(termx_to_exp_ ~cx) spine in
      Doc.(Appl (100, Infix (string " ", Left, (head :: spine))))

let termx_to_exp tx = termx_to_exp_ ~cx:tx.tycx tx.data
let pp_termx out tx = termx_to_exp tx |> Doc.bracket |> Doc.pp_linear out

let rec formx_to_exp_ ~cx f =
  match expose f with
  | Atom a -> termx_to_exp_ ~cx a
  | Eq (s, t, _) ->
      let s = termx_to_exp_ ~cx s in
      let t = termx_to_exp_ ~cx t in
      Doc.(Appl (40, Infix (string " = ", Non, [s ; t])))
  | And (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (30, Infix (string_as 3 " ∧ ", Right, [a ; b])))
  | Top -> Doc.(Atom (string "True"))
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (20, Infix (string_as 3 " ∨ ", Right, [a ; b])))
  | Bot -> Doc.(Atom (string "False"))
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (10, Infix (string_as 3 " → ", Right, [a ; b])))
  | Forall (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let q = Caml.Format.(fun out ->
            pp_print_as out 3 "∀ (" ;
            pp_print_string out (Ident.to_string vty.var) ;
            pp_print_string out " : " ;
            pp_ty out vty.ty ;
            pp_print_string out "), ") in
        let b = formx_to_exp_ ~cx b in
        Doc.(Appl (5, Prefix (q, b)))
      end
  | Exists (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let q = Caml.Format.(fun out ->
            pp_print_as out 3 "∃ (" ;
            pp_print_string out (Ident.to_string vty.var) ;
            pp_print_string out " : " ;
            pp_ty out vty.ty ;
            pp_print_string out "), ") in
        let b = formx_to_exp_ ~cx b in
        Doc.(Appl (5, Prefix (q, b)))
      end
  | Mdata (_, _, f) -> formx_to_exp_ ~cx f

let formx_to_exp fx = formx_to_exp_ ~cx:fx.tycx fx.data
let pp_formx out fx = formx_to_exp fx |> Doc.bracket |> Doc.pp_linear out

let pp_sigma out sg =
  Caml.Format.fprintf out "universe u@." ;
  Set.iter ~f:begin fun i ->
    if Set.mem sigma0.basics i then () else
      Caml.Format.fprintf out "variable {%s : Type u}@." (Ident.to_string i)
  end sg.basics ;
  Map.iteri ~f:begin fun ~key:k ~data:ty ->
    if Map.mem sigma0.consts k then () else
      Caml.Format.fprintf out "variable {%s : %s}@." (Ident.to_string k) (ty_to_string @@ thaw_ty ty)
  end sg.consts

let pp_path out path =
  Q.to_seq path |>
  Caml.Format.pp_print_seq
    ~pp_sep:(fun out () -> Caml.Format.pp_print_string out ",")
    (fun out -> function
       | `l -> Caml.Format.pp_print_string out "l"
       | `r -> Caml.Format.pp_print_string out "r"
       | `d -> Caml.Format.pp_print_string out "d"
       | `i x ->
           Caml.Format.pp_print_string out "i " ;
           Caml.Format.pp_print_string out (Ident.to_string x))
    out

let pp_rule_name out rn =
  match rn with
  | Cos.Inst { side ; term = tx } ->
      Caml.Format.fprintf out "inst_%s (%a)"
        (match side with `r -> "r" | _ -> "l")
        pp_termx tx
  | _ -> Cos.pp_rule_name out rn

let pp_deriv out (sg, deriv) =
  Caml.Format.fprintf out "section Example@." ;
  pp_sigma out sg ;
  Caml.Format.fprintf out "example (_ : %a) : %a := by@."
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  List.iter ~f:begin fun (prem, rule, _) ->
    Caml.Format.fprintf out "  within %a use %a@."
      pp_path rule.Cos.path
      pp_rule_name rule.Cos.name ;
    Caml.Format.fprintf out "  /- @[%a@] -/@." pp_formx prem ;
  end @@ List.rev deriv.middle ;
  Caml.Format.fprintf out "  rename_i u ; exact u@." ;
  Caml.Format.fprintf out "end Example@."

let pp_header out () =
  Caml.Format.fprintf out "import Profint@." ;
  Caml.Format.fprintf out "open Profint@."

let pp_footer _out () = ()

let pp_comment out str =
  Caml.Format.fprintf out "/- %s -/@\n" str

let name = "lean4"
let files pf =
  let replace contents =
    CCString.replace ~which:`Left contents
      ~sub:"/-PROOF-/\n" ~by:pf
  in [
    File { fname = "lakefile.lean" ;
           contents = [%blob "lib/systems/lean4/lakefile.lean"] } ;
    File { fname = "lean-toolchain" ;
           contents = [%blob "lib/systems/lean4/lean-toolchain"] } ;
    Dir {
      dname = "Profint" ;
      contents = [
        File { fname = "Theorems.lean" ;
               contents = [%blob "lib/systems/lean4/Profint/Theorems.lean"] } ;
        File { fname = "Paths.lean" ;
               contents = [%blob "lib/systems/lean4/Profint/Paths.lean"] } ;
        File { fname = "Within.lean" ;
               contents = [%blob "lib/systems/lean4/Profint/Within.lean"] } ;
      ] } ;
    File { fname = "Profint.lean" ;
           contents = [%blob "lib/systems/lean4/Profint.lean"] } ;
    File { fname = "Proof.lean" ;
           contents = replace [%blob "lib/systems/lean4/Proof.lean"] } ;
  ]
let build () = "lake build"
