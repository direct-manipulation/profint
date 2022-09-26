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

let rec ty_to_exp ty =
  match ty with
  | Ty.Basic a ->
      let rep = if Ident.equal a Ty.k_o then "Prop" else Ident.to_string a in
      Doc.(Atom (string rep))
  | Ty.Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (string " -> ", Right,
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
        let rep = Caml.Format.dprintf "fun %s => "
            (Ident.to_string vty.var) in
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
      Doc.(Appl (30, Infix (string " /\\ ", Right, [a ; b])))
  | Top -> Doc.(Atom (string "True"))
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (20, Infix (string " \\/ ", Right, [a ; b])))
  | Bot -> Doc.(Atom (string "False"))
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (10, Infix (string " -> ", Right, [a ; b])))
  | Forall (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let q = Caml.Format.(fun out ->
            pp_print_as out 3 "forall (" ;
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
            pp_print_as out 3 "exists (" ;
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
  Set.iter sg.basics ~f:begin fun i ->
    if Set.mem sigma0.basics i then () else
      Caml.Format.fprintf out "Context {%s : Type}.@." (Ident.to_string i)
  end ;
  Map.iteri sg.consts ~f:begin fun ~key:k ~data:ty ->
    if Map.mem sigma0.consts k then () else
      Caml.Format.fprintf out "Context {%s : %s}.@."
        (Ident.to_string k)
        (ty_to_string @@ thaw_ty ty)
  end

exception Unprintable
let unprintable reason =
  Caml.Format.eprintf "to_coq: failure: %s@." reason ;
  raise Unprintable

let rec make_eqns ty ss ts =
  match ty, ss, ts with
  | _, [], [] -> []
  | Ty.Arrow (a, ty), (s :: ss), (t :: tt) ->
      let eqs = make_eqns ty ss tt in
      if Term.eq_term s t then eqs else (s, t, a) :: eqs
  | _ ->
      unprintable "make_eqns"

let make_lemma (target : formx) (eqs : (T.term * T.term * Ty.t) list) : string =
  let tycx = target.tycx in
  let target = formx_to_exp target in
  let eqs = List.filter_map eqs ~f:begin fun (l, r, ty) ->
      if Term.eq_term l r then None else
      let ex = Doc.(Appl (100, Infix (string " ", Left,
                                      [ Atom (string "@eq") ;
                                        ty_to_exp ty ;
                                        termx_to_exp { tycx ; data = l } ;
                                        termx_to_exp { tycx ; data = r } ]))) in
      Some ex
    end in
  let eq = match eqs with
    | [] -> Doc.(Atom (string "True"))
    | [eq] -> eq
    | _ -> Doc.(Appl (30, Infix (string " /\\ ", Right, eqs)))
  in
  Doc.(Appl (1, Infix (string " -> ", Right, [eq ; target]))) |>
  Doc.bracket |> Doc.to_string

let pp_rule out goal rule =
  let has_subproof = ref false in
  let pp_rule cx f name =
    match name with
    | Cos.Init -> begin
        let fail () =
          unprintable @@ "init: got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = f } in
        match expose f with
        | Imp (a, b) -> begin
            match expose a, expose b with
            | Atom T.(App { head = Const (_, ty) ; spine = ss }),
              Atom T.(App { spine = ts ; _ }) ->
                make_eqns (Ty.norm_exn ty) ss ts |>
                make_lemma { tycx = cx ; data = f } |>
                Caml.Format.fprintf out "(_ : %s)" ;
                has_subproof := true
            | _ -> fail ()
          end
        | _ -> fail ()
      end
    | Cos.Congr -> begin
        let fail () =
          unprintable @@ "congr: got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = f } in
        match expose f with
        | Eq (T.(App { spine = ss ; head }), T.(App { spine = ts ; _ }), _) ->
            let ty = Ty.norm_exn @@ ty_infer cx head in
            make_eqns ty ss ts |>
            make_lemma { tycx = cx ; data = f } |>
            Caml.Format.fprintf out "(_ : %s)" ;
            has_subproof := true
        | _ -> fail ()
      end
    | Cos.Inst { side ; term = tx } -> begin
        let fail () =
          unprintable @@ "inst: got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = f } in
        match side, expose f with
        | `l, Forall ({ var ; ty }, b)
        | `r, Exists ({ var ; ty }, b) ->
            with_var cx { var ; ty } begin fun { var ; ty } cx ->
              Caml.Format.fprintf out "inst_%s (p := fun (%s : %a) => %a) (%a)"
                (match side with  `l -> "l" | _ -> "r")
                (Ident.to_string var) pp_ty ty
                pp_formx { tycx = cx ; data = b }
                pp_termx tx
            end
        | _ -> fail ()
      end
    | _ -> Cos.pp_rule_name out name
  in
  let rec pp_path n cx f0 path =
    match Q.take_front path with
    | None ->
        pp_rule cx f0 rule.Cos.name ;
        Caml.Format.fprintf out "%s _%c.@." (String.make (n - 1) ')') ')' ;
        if !has_subproof then begin
          Caml.Format.fprintf out "  profint_discharge_lemma.@." ;
          has_subproof := false
        end
    | Some (dir, path) -> begin
        match expose f0, dir with
        | And (f, _), `l ->
            Caml.Format.pp_print_string out "go_left_and (" ;
            pp_path (n + 1) cx f path
        | And (_, f), `r ->
            Caml.Format.pp_print_string out "go_right_and (" ;
            pp_path (n + 1) cx f path
        | Or (f, _), `l ->
            Caml.Format.pp_print_string out "go_left_or (" ;
            pp_path (n + 1) cx f path
        | Or (_, f), `r ->
            Caml.Format.pp_print_string out "go_right_or (" ;
            pp_path (n + 1) cx f path
        | Imp (f, _), `l ->
            Caml.Format.pp_print_string out "go_left_imp (" ;
            pp_path (n + 1) cx f path
        | Imp (_, f), `r ->
            Caml.Format.pp_print_string out "go_right_imp (" ;
            pp_path (n + 1) cx f path
        | Forall ({ var ; ty }, f), `d
        | Forall ({ ty ; _ }, f), `i var ->
            with_var cx { var ; ty } begin fun { var ; _ } cx ->
              Caml.Format.fprintf out "go_down_all (fun (%s : %a) => "
                (Ident.to_string var) pp_ty ty ;
              pp_path (n + 1) cx f path
            end
        | Exists ({ var ; ty }, f), `d
        | Exists ({ ty ; _ }, f), `i var ->
            with_var cx { var ; ty } begin fun { var ; _ } cx ->
              Caml.Format.fprintf out "go_down_ex (fun (%s : %a) => "
                (Ident.to_string var) pp_ty ty ;
              pp_path (n + 1) cx f path
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
  Caml.Format.fprintf out "refine %c" '(' ;
  pp_path 1 goal.tycx goal.data rule.path

let pp_step out (prem, rule, concl) =
  pp_rule out concl rule ;
  Caml.Format.fprintf out "(* %a *)@." pp_formx prem

let pp_deriv out (sg, deriv) =
  Caml.Format.fprintf out "Section Example.@." ;
  pp_sigma out sg ;
  Caml.Format.fprintf out "Goal (%a) -> %a.@."
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  Caml.Format.fprintf out "intro __Profint_top.@." ;
  List.iter ~f:(pp_step out) (List.rev deriv.Cos.middle) ;
  Caml.Format.fprintf out "exact __Profint_top.@.Qed.@.End Example.@."

let pp_header out () =
  Caml.Format.fprintf out "Require Import List.@." ;
  Caml.Format.fprintf out "Import ListNotations.@." ;
  Caml.Format.fprintf out "Require Import Profint.@."

let pp_footer _out () = ()

let pp_comment out str =
  Caml.Format.fprintf out "(* %s *)@\n" str

let name = "coq"
let files pf =
  let replace contents =
    CCString.replace ~which:`Left contents
      ~sub:"(*PROOF*)\n" ~by:pf
  in [
    File { fname = "Proof.v" ;
           contents = replace [%blob "lib/systems/coq/Proof.v"] } ;
    File { fname = "Profint.v" ;
           contents = [%blob "lib/systems/coq/Profint.v"] } ;
    File { fname = "_CoqProject" ;
           contents = [%blob "lib/systems/coq/_CoqProject"] } ;
    File { fname = "Makefile" ;
           contents = [%blob "lib/systems/coq/Makefile"] } ;
  ]
let build () = "make"
