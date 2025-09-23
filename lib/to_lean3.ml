(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Output suitable for Lean3 *)

open Util
open Types
open Term
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
        let rep = Doc.string (Printf.sprintf "fun %s, " (Ident.to_string vty.var)) in
        Doc.(Appl (1, Prefix (rep, termx_to_exp_  ~cx body)))
      end
  | T.App { head ; spine = [] } ->
      Term.head_to_exp ~cx head
  | T.App { head ; spine } ->
      let head = Term.head_to_exp ~cx head in
      let spine = List.map (termx_to_exp_ ~cx) spine in
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
  | Top -> Doc.(Atom (string "true"))
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (20, Infix (string_as 3 " ∨ ", Right, [a ; b])))
  | Bot -> Doc.(Atom (string "false"))
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (10, Infix (string_as 3 " → ", Right, [a ; b])))
  | Forall (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let q = Stdlib.Format.(fun out ->
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
        let q = Stdlib.Format.(fun out ->
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
  Stdlib.Format.fprintf out "universe u@." ;
  Ident.Set.iter begin fun i ->
    if Ident.Set.mem i sigma0.basics then () else
    let i = Ident.to_string i in
    Stdlib.Format.fprintf out "variable {%s : Type u}@.include %s@." i i
  end sg.basics ;
  Ident.Map.iter begin fun k ty ->
    if Ident.Map.mem k sigma0.consts then () else
    let k = Ident.to_string k in
    Stdlib.Format.fprintf out "variable {%s : %s}@.include %s@."
      k (ty_to_string @@ thaw_ty ty) k
  end sg.consts

exception Unprintable
let unprintable reason =
  Stdlib.Format.eprintf "to_lean3: failure: %s@." reason ;
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
  let eqs = List.filter_map begin fun (l, r, ty) ->
      if Term.eq_term l r then None else
      let ex = Doc.(Appl (100, Infix (string " ", Left,
                                      [ Atom (string "@eq") ;
                                        ty_to_exp ty ;
                                        termx_to_exp { tycx ; data = l } ;
                                        termx_to_exp { tycx ; data = r } ]))) in
      Some ex
    end eqs in
  let eq = match eqs with
    | [] -> Doc.(Atom (string "true"))
    | [eq] -> eq
    | _ -> Doc.(Appl (30, Infix (string_as 3 " ∧ ", Right, eqs)))
  in
  Doc.(Appl (1, Infix (string_as 3 " → ", Right, [eq ; target]))) |>
  Doc.bracket |> Doc.to_string

let pp_rule out (prem, rule, goal) =
  let has_subproof = ref false in
  let pp_rule cx fc fp name =
    match name with
    | Cos.Init -> begin
        let fail () =
          unprintable @@ "init: got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = fc } in
        match expose fc with
        | Imp (a, b) -> begin
            match expose a, expose b with
            | Atom T.(App { head = Const (_, ty) ; spine = ss }),
              Atom T.(App { spine = ts ; _ }) ->
                make_eqns (Ty.norm_exn ty) ss ts |>
                make_lemma { tycx = cx ; data = fc } |>
                Stdlib.Format.fprintf out "(_ : %s)" ;
                has_subproof := true
            | _ -> fail ()
          end
        | _ -> fail ()
      end
    | Cos.Congr -> begin
        let fail () =
          unprintable @@ "congr: got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = fc } in
        match expose fc with
        | Eq (T.(App { spine = ss ; head }), T.(App { spine = ts ; _ }), _) ->
            let ty = Ty.norm_exn @@ ty_infer cx head in
            make_eqns ty ss ts |>
            make_lemma { tycx = cx ; data = fc } |>
            Stdlib.Format.fprintf out "(_ : %s)" ;
            has_subproof := true
        | _ -> fail ()
      end
    | Cos.Inst { side ; term = tx } -> begin
        let f = if Path.Dir.equal side L then fp else fc in
        let fail () =
          Stdlib.Format.kasprintf unprintable
            "inst_%s: got %a"
            (match side with L -> "l" | _ -> "r")
            Form4.pp_formx { tycx = cx ; data = f } in
        match expose f with
        | Forall ({ var ; ty }, b)
        | Exists ({ var ; ty }, b) ->
            with_var cx { var ; ty } begin fun { var ; ty } cx ->
              Stdlib.Format.fprintf out "%@inst_%s %a (fun (%s : %a), %a) (%a)"
                (match side with L -> "l" | _ -> "r")
                pp_ty ty
                (Ident.to_string var) pp_ty ty
                pp_formx { tycx = cx ; data = b }
                pp_termx tx
            end
        | _ -> fail ()
      end
    | Cos.Rewrite { from } -> begin
        let dstr = match from with L -> "ltr" | _ -> "rtl" in
        let fail () =
          unprintable @@ "rewrite_" ^ dstr ^ ": got " ^
                         pp_to_string Form4.pp_formx { tycx = cx ; data = fc } in
        match expose fc with
        | Imp (a, b) -> begin
            match expose a with
            | Eq (s, t, ty) -> begin
                let tfrom, tto = match from with
                  | L -> s, t
                  | _ -> t, s
                in
                let var = Ident.of_string "__profint_var" in
                let const = T.App { head = Const (var, ty) ; spine = [] } in
                let pbody = Term.rewrite ~tfrom ~tto:const b in
                Stdlib.Format.fprintf out "%@rewrite_%s (%a) (fun (%s : %a), %a) (%a) (%a)"
                  dstr
                  pp_ty ty
                  (Ident.to_string var) pp_ty ty
                  pp_formx { tycx = cx ; data = pbody }
                  pp_termx { tycx = cx ; data = tfrom }
                  pp_termx { tycx = cx ; data = tto }
              end
            | _ -> fail ()
          end
        | _ -> fail ()
      end
    | Cos.Rename _ -> Stdlib.Format.pp_print_string out "id"
    | _ -> Cos.pp_rule_name out name
  in
  let rec pp_path n cx goal prem path =
    match Path.expose_front path with
    | None ->
        pp_rule cx goal prem rule.Cos.name ;
        Stdlib.Format.fprintf out "%s _,@." @@ String.make n ')' ;
        if !has_subproof then begin
          Stdlib.Format.fprintf out "  { profint_discharge },@." ;
          has_subproof := false
        end
    | Some (dir, path) -> begin
        match expose goal, expose prem, dir with
        | And (b, c), And (a, _), Path.Dir.L ->
            Stdlib.Format.fprintf out "%@go_left_and (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | And (c, b), And (_, a), R ->
            Stdlib.Format.fprintf out "%@go_right_and (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | Or (b, c), Or (a, _), L ->
            Stdlib.Format.fprintf out "%@go_left_or (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | Or (c, b), Or (_, a), R ->
            Stdlib.Format.fprintf out "%@go_right_or (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | Imp (b, c), Imp (a, _), L ->
            Stdlib.Format.fprintf out "%@go_left_imp (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx a b path
        | Imp (c, b), Imp (_, a), R ->
            Stdlib.Format.fprintf out "%@go_right_imp (%a) (%a) (%a) ("
              pp_formx { tycx = cx ; data = a }
              pp_formx { tycx = cx ; data = b }
              pp_formx { tycx = cx ; data = c } ;
            pp_path (n + 1) cx b a path
        | Forall ({ var ; ty }, q), Forall (_, p), L ->
            with_var cx { var ; ty } begin fun { var ; _ } cx ->
              let var = Ident.to_string var in
              Stdlib.Format.fprintf out "%@go_down_all (%a) (fun (%s : %a), %a) (fun (%s : %a), %a) (fun (%s : %a), "
                pp_ty ty
                var pp_ty ty pp_formx { tycx = cx ; data = p }
                var pp_ty ty pp_formx { tycx = cx ; data = q }
                var pp_ty ty ;
              pp_path (n + 1) cx q p path
            end
        | Exists ({ var ; ty }, q), Exists (_, p), L ->
            with_var cx { var ; ty } begin fun { var ; _ } cx ->
              let var = Ident.to_string var in
              Stdlib.Format.fprintf out "%@go_down_ex (%a) (fun (%s : %a), %a) (fun (%s : %a), %a) (fun (%s : %a), "
                pp_ty ty
                var pp_ty ty pp_formx { tycx = cx ; data = p }
                var pp_ty ty pp_formx { tycx = cx ; data = q }
                var pp_ty ty ;
              pp_path (n + 1) cx q p path
            end
        | _ ->
            String.concat " "
              [ "pp_rule:" ;
                pp_to_string Cos.pp_rule rule ;
                "::" ;
                pp_to_string pp_formx { tycx = cx ; data = goal } ]
            |> unprintable
      end
  in
  Stdlib.Format.fprintf out "refine (" ;
  pp_path 1 goal.tycx goal.data prem.data rule.path

let pp_step out (prem, _, _ as prc) =
  pp_rule out prc ;
  Stdlib.Format.fprintf out "show %a,@." pp_formx prem

let pp_deriv out (sg, deriv) =
  Stdlib.Format.fprintf out "section Example@." ;
  pp_sigma out sg ;
  Stdlib.Format.fprintf out "example (__profint : %a) : %a :=@."
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  Stdlib.Format.fprintf out "begin@." ;
  List.iter (pp_step out) (List.rev deriv.Cos.middle) ;
  Stdlib.Format.fprintf out "exact __profint@." ;
  Stdlib.Format.fprintf out "end@." ;
  Stdlib.Format.fprintf out "end Example.@."

let pp_header out () =
  Stdlib.Format.fprintf out "import Profint@." ;
  Stdlib.Format.fprintf out "open Profint@."

let pp_footer _out () = ()

let pp_comment out str =
  Stdlib.Format.fprintf out "/- %s -/@\n" str

let name = "lean3"
let cookie_re = Re.Pcre.regexp ~flags:[`MULTILINE] {|\/-PROOF-\/|}
let files pf =
  let replace contents =
    Re.Pcre.substitute ~rex:cookie_re ~subst:(fun _ -> pf) contents
  in [
    File { fname = "lean-toolchain" ;
           contents = blob "lean3/lean-toolchain" } ;
    File { fname = "leanpkg.toml" ;
           contents = blob "lean3/leanpkg.toml" } ;
    Dir {
      dname = "src" ;
      contents = [
        File { fname = "Proof.lean" ;
               contents = replace @@ blob "lean3/src/Proof.lean" } ;
        File { fname = "Profint.lean" ;
               contents = blob "lean3/src/Profint.lean" } ;
      ] } ;
  ]
let build () = "leanpkg build"
