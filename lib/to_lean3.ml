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
        let rep = Doc.String (Printf.sprintf "fun %s, " vty.var) in
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
  | Top -> Doc.(Atom (String "true"))
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (20, Infix (StringAs (3, " ∨ "), Right, [a ; b])))
  | Bot -> Doc.(Atom (String "false"))
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

exception Unprintable
let unprintable reason =
  Format.eprintf "to_lean3: failure: %s@." reason ;
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
    | [] -> Doc.(Atom (String "true"))
    | [eq] -> eq
    | _ -> Doc.(Appl (30, Infix (StringAs (3, " ∧ "), Right, eqs)))
  in
  Doc.(Appl (1, Infix (StringAs (3, " → "), Right, [eq ; target]))) |>
  Doc.bracket |> Doc.lin_doc

let pp_rule out (prem, rule, goal) =
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
        | Eq (T.(App { spine = ss ; _ }), T.(App { spine = ts ; _ }), ty) ->
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
              Format.fprintf out "@inst %a (fun (%s : %a), %a) (%a)"
                pp_ty ty
                var pp_ty ty
                pp_formx { tycx = cx ; data = b }
                pp_termx tx
            end
        | _ -> fail ()
      end
    | _ -> Cos.pp_rule_name out name
  in
  let rec pp_path n cx goal prem path =
    match Q.take_front path with
    | None ->
        pp_rule cx goal rule.Cos.name ;
        Format.fprintf out "%s _,@." @@ String.make n (Char.chr 41) ;
        if !has_subproof then begin
          Format.fprintf out "  { profint_discharge },@." ;
          has_subproof := false
        end
    | Some (dir, path) -> begin
        match expose goal, expose prem, dir with
        | And (b, c), And (a, _), `l ->
            Format.fprintf out "@@go_left_and (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | And (c, b), And (_, a), `r ->
            Format.fprintf out "@@go_right_and (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | Or (b, c), Or (a, _), `l ->
            Format.fprintf out "@@go_left_or (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | Or (c, b), Or (_, a), `r ->
            Format.fprintf out "@@go_right_or (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | Imp (b, c), Imp (a, _), `l ->
            Format.fprintf out "@@go_left_imp (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx a b path
        | Imp (c, b), Imp (_, a), `r ->
            Format.fprintf out "@@go_right_imp (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | Forall ({ var ; ty }, q), Forall (_, p), `d
        | Forall ({ ty ; _ }, q), Forall (_, p), `i var ->
            with_var ~fresh:true cx { var ; ty } begin fun { var ; _ } cx ->
              Format.fprintf out "@@go_down_all (%a) (fun (%s : %a), %a) (fun (%s : %a), %a) (fun (%s : %a), "
                pp_ty ty
                var pp_ty ty pp_formx { tycx = cx ; data = p }
                var pp_ty ty pp_formx { tycx = cx ; data = q }
                var pp_ty ty ;
              pp_path (n + 1) cx q p path
            end
        | Exists ({ var ; ty }, q), Exists (_, p), `d
        | Exists ({ ty ; _ }, q), Exists (_, p), `i var ->
            with_var ~fresh:true cx { var ; ty } begin fun { var ; _ } cx ->
              Format.fprintf out "@@go_down_ex (%a) (fun (%s : %a), %a) (fun (%s : %a), %a) (fun (%s : %a), "
                pp_ty ty
                var pp_ty ty pp_formx { tycx = cx ; data = p }
                var pp_ty ty pp_formx { tycx = cx ; data = q }
                var pp_ty ty ;
              pp_path (n + 1) cx q p path
            end
        | _ ->
            String.concat " " [ "pp_rule:" ;
                                pp_to_string Cos.pp_rule rule ;
                                "::" ;
                                pp_to_string pp_formx { tycx = cx ; data = goal } ]
            |> unprintable
      end
  in
  Format.fprintf out "refine (" ;
  pp_path 1 goal.tycx goal.data prem.data rule.path

let pp_step out (prem, rule, concl as prc) =
  pp_rule out prc ;
  Format.fprintf out "show %a,@." pp_formx prem

let pp_deriv out (sg, deriv) =
  Format.fprintf out "section Example@." ;
  pp_sigma out sg ;
  Format.fprintf out "example (__profint : %a) : %a :=@."
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  Format.fprintf out "begin@." ;
  List.iter (pp_step out) (List.rev deriv.Cos.middle) ;
  Format.fprintf out "exact __profint@." ;
  Format.fprintf out "end@." ;
  Format.fprintf out "end Example.@."