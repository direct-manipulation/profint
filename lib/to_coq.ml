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

let rec ty_to_exp ty =
  match ty with
  | Basic a ->
      let rep = if a = K.k_o then "Prop" else a in
      Doc.(Atom (String rep))
  | Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (String (" -> "), Right,
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
      Doc.(Appl (30, Infix (String " /\\ ", Right, [a ; b])))
  | Top -> Doc.(Atom (String "True"))
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (20, Infix (String " \\/ ", Right, [a ; b])))
  | Bot -> Doc.(Atom (String "False"))
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (10, Infix (String " -> ", Right, [a ; b])))
  | Forall (vty, b) ->
      with_var ~fresh:true cx vty begin fun vty cx ->
        let q = Doc.Fmt Format.(fun out ->
            pp_print_as out 3 "forall (" ;
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
            pp_print_as out 3 "exists (" ;
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
  IdSet.iter begin fun i ->
    if IdSet.mem i sigma0.basics then () else
      Format.fprintf out "Context {%s : Type}.@." i
  end sg.basics ;
  IdMap.iter begin fun k ty ->
    if IdMap.mem k sigma0.consts then () else
      Format.fprintf out "Context {%s : %s}.@." k (ty_to_string @@ thaw_ty ty)
  end sg.consts

exception Unprintable
let unprintable reason =
  Format.eprintf "to_coq: failure: %s@." reason ;
  raise Unprintable

let rec make_eqns ty ss ts =
  match ty, ss, ts with
  | _, [], [] -> []
  | Arrow (a, ty), (s :: ss), (t :: tt) ->
      let eqs = make_eqns ty ss tt in
      if Term.eq_term s t then eqs else (s, t, a) :: eqs
  | _ ->
      unprintable "make_eqns"

let make_lemma (target : formx) (eqs : (T.term * T.term * ty) list) : string =
  let tycx = target.tycx in
  let target = formx_to_exp target in
  let eqs = List.filter_map begin fun (l, r, ty) ->
      if Term.eq_term l r then None else
      let ex = Doc.(Appl (100, Infix (String " ", Left,
                                      [ Atom (String "@eq") ;
                                        ty_to_exp ty ;
                                        termx_to_exp { tycx ; data = l } ;
                                        termx_to_exp { tycx ; data = r } ]))) in
      Some ex
    end eqs in
  let eq = match eqs with
    | [] -> Doc.(Atom (String "True"))
    | [eq] -> eq
    | _ -> Doc.(Appl (30, Infix (String " /\\ ", Right, eqs)))
  in
  Doc.(Appl (1, Infix (String " -> ", Right, [eq ; target]))) |>
  Doc.bracket |> Doc.lin_doc

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
                make_eqns (ty_norm ty) ss ts |>
                make_lemma { tycx = cx ; data = f } |>
                Format.fprintf out "(_ : %s)" ;
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
            let ty = ty_norm @@ ty_infer cx head in
            make_eqns (ty_norm ty) ss ts |>
            make_lemma { tycx = cx ; data = f } |>
            Format.fprintf out "(_ : %s)" ;
            has_subproof := true
        | _ -> fail ()
      end
    | Cos.Inst tx -> begin
        let fail () =
          unprintable @@ "inst: got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = f } in
        match expose f with
        | Exists ({ var ; ty }, b) ->
            with_var ~fresh:true cx { var ; ty } begin fun { var ; ty } cx ->
              Format.fprintf out "inst (p := fun (%s : %a) => %a) (%a)"
                var pp_ty ty
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
        Format.fprintf out "%s.@." @@ String.make n (Char.chr 41) ;
        if !has_subproof then begin
          Format.fprintf out "  profint_discharge_lemma.@." ;
          has_subproof := false
        end
    | Some (dir, path) -> begin
        match expose f0, dir with
        | And (f, _), `l ->
            Format.pp_print_string out "go_left_and (" ;
            pp_path (n + 1) cx f path
        | And (_, f), `r ->
            Format.pp_print_string out "go_right_and (" ;
            pp_path (n + 1) cx f path
        | Or (f, _), `l ->
            Format.pp_print_string out "go_left_or (" ;
            pp_path (n + 1) cx f path
        | Or (_, f), `r ->
            Format.pp_print_string out "go_right_or (" ;
            pp_path (n + 1) cx f path
        | Imp (f, _), `l ->
            Format.pp_print_string out "go_left_imp (" ;
            pp_path (n + 1) cx f path
        | Imp (_, f), `r ->
            Format.pp_print_string out "go_right_imp (" ;
            pp_path (n + 1) cx f path
        | Forall ({ var ; ty }, f), `d
        | Forall ({ ty ; _ }, f), `i var ->
            with_var ~fresh:true cx { var ; ty } begin fun { var ; _ } cx ->
              Format.fprintf out "go_down_all (fun (%s : %a) => "
                var pp_ty ty ;
              pp_path (n + 1) cx f path
            end
        | Exists ({ var ; ty }, f), `d
        | Exists ({ ty ; _ }, f), `i var ->
            with_var ~fresh:true cx { var ; ty } begin fun { var ; _ } cx ->
              Format.fprintf out "go_down_ex (fun (%s : %a) => "
                var pp_ty ty ;
              pp_path (n + 1) cx f path
            end
        | _ ->
            String.concat " " [ "pp_rule:" ;
                                pp_to_string Cos.pp_rule rule ;
                                "::" ;
                                pp_to_string pp_formx goal ]
            |> unprintable
      end
  in
  Format.fprintf out "unshelve eapply (" ;
  pp_path 1 goal.tycx goal.data rule.path

let pp_step out (prem, rule, concl) =
  pp_rule out concl rule ;
  Format.fprintf out "(* %a *)@." pp_formx prem

let pp_deriv out (sg, deriv) =
  Format.fprintf out "Section Example.@." ;
  pp_sigma out sg ;
  Format.fprintf out "Goal (%a) -> %a.@."
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  Format.fprintf out "intro __Profint_top.@." ;
  List.iter (pp_step out) (List.rev deriv.Cos.middle) ;
  Format.fprintf out "exact __Profint_top.@.Qed.@.End Example.@."
