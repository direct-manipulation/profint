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
  Caml.Format.fprintf out "@[<v0>universe u@," ;
  Set.iter ~f:begin fun i ->
    if Set.mem sigma0.basics i then () else
      Caml.Format.fprintf out "variable {%s : Type u}@," (Ident.to_string i)
  end sg.basics ;
  Map.iteri ~f:begin fun ~key:k ~data:ty ->
    if Map.mem sigma0.consts k then () else
      Caml.Format.fprintf out "variable {%s : %s}@," (Ident.to_string k) (ty_to_string @@ thaw_ty ty)
  end sg.consts ;
  Caml.Format.fprintf out "@,@]"

exception Unprintable

type lean_dir = L of int | R of int | I of Ident.t list
[@@deriving equal]

let compatible d1 d2 =
  match d1, d2 with
  | L _, L _
  | R _, R _
  | I _, I _ -> true
  | _ -> false

let join d1 d2 =
  match d1, d2 with
  | L m, L n -> L (m + n)
  | R m, R n -> R (m + n)
  | I xs, I ys -> I (xs @ ys)
  | _ -> assert false

let ldir_to_string = function
  | L 1 -> "l"
  | L n -> "l " ^ Int.to_string n
  | R 1 -> "r"
  | R n -> "r " ^ Int.to_string n
  | I xs ->
      "i " ^ (List.map ~f:Ident.to_string xs |>
              String.concat ~sep:" ")

let pp_path rule concl out =
  let trail = ref [] in
  let push ldir =
    match !trail with
    | old_ldir :: rest when compatible old_ldir ldir ->
        trail := join old_ldir ldir :: rest
    | _ ->
        trail := ldir :: !trail
  in
  let rec get_trail cx goal path =
    match Path.expose_front path with
    | None -> ()
    | Some (dir, path) -> begin
        match dir, expose goal with
        | L, (And (goal, _) | Or (goal, _) | Imp (goal, _)) ->
            push (L 1) ;
            get_trail cx goal path
        | R, (And (_, goal) | Or (_, goal) | Imp (_, goal)) ->
            push (R 1) ;
            get_trail cx goal path
        | L, (Forall (vty, goal) | Exists (vty, goal)) ->
            with_var cx vty begin fun { var ; _ } cx ->
              push (I [var]) ;
              get_trail cx goal path
            end
        | _, Mdata (_, _, goal) ->
            get_trail cx goal path
        | _ ->
            raise Unprintable
      end
  in
  get_trail concl.tycx concl.data rule.Cos.path ;
  List.rev !trail |>
  List.map ~f:ldir_to_string |>
  String.concat ~sep:", " |>
  Caml.Format.pp_print_string out

let pp_rule_name out rn =
  match rn with
  | Cos.Inst { side ; term = tx } ->
      Caml.Format.fprintf out "inst_%s (%a)"
        (match side with R -> "r" | _ -> "l")
        pp_termx tx
  | _ -> Cos.pp_rule_name out rn

let pp_deriv out (sg, deriv) =
  Caml.Format.fprintf out "@[<v0>section Example@," ;
  pp_sigma out sg ;
  Caml.Format.fprintf out "example (__profint_prem : %a) : %a := by@,"
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  List.iter ~f:begin fun (prem, rule, concl) ->
    Caml.Format.fprintf out "  within %t use %a@,"
      (pp_path rule concl)
      pp_rule_name rule.Cos.name ;
    Caml.Format.fprintf out "  /- @[%a@] -/@," pp_formx prem ;
  end @@ List.rev deriv.middle ;
  Caml.Format.fprintf out "  exact __profint_prem@," ;
  Caml.Format.fprintf out "end Example@,@]"

let pp_header out () =
  Caml.Format.fprintf out "@[<v0>import Profint@,open Profint@,@]"

let pp_footer _out () = ()

let pp_comment out str =
  Caml.Format.fprintf out "/- %s -/@," str

let name = "lean4"
let files pf =
  let replace contents =
    String.substr_replace_first contents
      ~pattern:"/-PROOF-/\n" ~with_:pf
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
