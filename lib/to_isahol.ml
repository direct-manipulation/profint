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
      let rep = if a = K.k_o then "bool" else "'" ^ a in
      Doc.(Atom (String rep))
  | Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (StringAs (3, " \\<Rightarrow> "), Right,
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
        let rep = Doc.String (Printf.sprintf "\\<lambda> %s. " vty.var) in
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
      Doc.(Appl (30, Infix (StringAs (3, " \\<and> "), Right, [a ; b])))
  | Top -> Doc.(Atom (String "True"))
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (20, Infix (StringAs (3, " \\<or> "), Right, [a ; b])))
  | Bot -> Doc.(Atom (String "False"))
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx a in
      let b = formx_to_exp_ ~cx b in
      Doc.(Appl (10, Infix (StringAs (3, " \\<longrightarrow> "), Right, [a ; b])))
  | Forall (vty, b) ->
      with_var ~fresh:true cx vty begin fun vty cx ->
        let q = Doc.Fmt Format.(fun out ->
            pp_print_as out 3 "\\<forall> " ;
            pp_print_string out vty.var ;
            pp_print_string out " :: " ;
            pp_ty out vty.ty ;
            pp_print_string out ". ") in
        let b = formx_to_exp_ ~cx b in
        Doc.(Appl (5, Prefix (q, b)))
      end
  | Exists (vty, b) ->
      with_var ~fresh:true cx vty begin fun vty cx ->
        let q = Doc.Fmt Format.(fun out ->
            pp_print_as out 3 "\\<exists> " ;
            pp_print_string out vty.var ;
            pp_print_string out " :: " ;
            pp_ty out vty.ty ;
            pp_print_string out ". ") in
        let b = formx_to_exp_ ~cx b in
        Doc.(Appl (5, Prefix (q, b)))
      end
  | Mdata (_, _, f) -> formx_to_exp_ ~cx f

let formx_to_exp fx = formx_to_exp_ ~cx:fx.tycx fx.data
let pp_formx out fx = formx_to_exp fx |> Doc.bracket |> Doc.pp_lin_doc out

let pp_sigma out sg =
  IdMap.iter begin fun k ty ->
    if IdMap.mem k sigma0.consts then () else
      Format.fprintf out "  fixes %s :: \"%s\"@."
        k (ty_to_string @@ thaw_ty ty)
  end sg.consts

exception Unprintable
let unprintable reason =
  Format.eprintf "to_isahol: failure: %s@." reason ;
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
    | _ -> Doc.(Appl (30, Infix (StringAs (3, " \\<and> "), Right, eqs)))
  in
  Doc.(Appl (1, Infix (StringAs (3, " \\<longrightarrow> "), Right, [eq ; target]))) |>
  Doc.bracket |> Doc.lin_doc

type step_surgery_rule =
  | Inner_reference of string
  | Cos_rule_name of Cos.rule_name

type step_surgery_state = {
  out : Format.formatter ;
  close : char list ;
  to_here : path ;
  from_here : path ;
  rule : step_surgery_rule ;
  tycx : tycx ;
  premise : form ;
  conclusion : form ;
}

let fresh_inner_counter =
  let ctr = ref 0 in
  fun () ->
    incr ctr ;
    "i" ^ string_of_int !ctr

let init_like_lemma ~emit sss ty ss ts target =
  let eqns =
    make_eqns (ty_norm ty) ss ts |>
    List.filter_map begin fun (l, r, _) ->
      if Term.eq_term l r then None else
      let l = termx_to_exp { tycx = sss.tycx ; data = l } in
      let r = termx_to_exp { tycx = sss.tycx ; data = r } in
      Some Doc.(Appl (40, Infix (String " = ", Non, [l ; r])))
    end
  in
  let eqn = match eqns with
    | [] -> Doc.(Atom (String "True"))
    | [eq] -> eq
    | _ -> Doc.(Appl (30, Infix (StringAs (3, " \\<and> "), Right, eqns)))
  in
  let target = formx_to_exp { tycx = sss.tycx ; data = target } in
  let lem = Doc.(Appl (1, Infix (StringAs (3, " \\<longrightarrow> "),
                                 Right, [eqn ; target]))) |>
            Doc.bracket |> Doc.lin_doc in
  let lem = List.fold_left begin fun lem vty ->
      Format.asprintf "\\<And> %s :: %a. %s"
        vty.var pp_ty vty.ty lem
    end lem sss.tycx.linear in
  let buf = Buffer.create 19 in
  emit buf ;
  let out = Format.formatter_of_buffer buf in
  let lemid = "i" ^ fresh_inner_counter () in
  Format.fprintf out "have %s: \"%s\"@,  by blast@?" lemid lem ;
  Format.fprintf sss.out "%s%s"
    lemid (CCString.of_list sss.close)

let rec step_surgery ~emit sss =
  match Q.take_front sss.from_here with
  | None -> begin
      match sss.rule with
      | Inner_reference lemid ->
          Format.fprintf sss.out "%s%s"
            lemid (CCString.of_list sss.close)
      | Cos_rule_name Cos.Init -> begin
          let fail () =
            "init: got " ^
            pp_to_string Form4.pp_formx
              { tycx = sss.tycx ; data = sss.conclusion } |> unprintable in
          match expose sss.conclusion with
          | Imp (a, b) -> begin
              match expose a, expose b with
              | Atom T.(App { head = Const (_, ty) ; spine = ss }),
                Atom T.(App { spine = ts ; _ }) ->
                  init_like_lemma ~emit sss ty ss ts sss.conclusion
              | _ -> fail ()
            end
          | _ -> fail ()
        end
      | Cos_rule_name Cos.Congr -> begin
          let fail () =
            "congr: got " ^
            pp_to_string Form4.pp_formx
              { tycx = sss.tycx ; data = sss.conclusion } |> unprintable in
          match expose sss.conclusion with
          | Eq (T.(App { head ; spine = ss }),
                T.(App { spine = ts ; _ }), _) -> begin
              let ty = ty_norm @@ ty_infer sss.tycx head in
              init_like_lemma ~emit sss ty ss ts sss.conclusion
            end
          | _ -> fail ()
        end
      | Cos_rule_name (Cos.Inst { side ; term = tx }) -> begin
          let f = if side = `l then sss.premise else sss.conclusion in
          let fail () =
            Format.kasprintf unprintable
              "inst_%s: got %a"
              (match side with `l -> "l" | _ -> "r")
              Form4.pp_formx { tycx = sss.tycx ; data = f } in
          match expose f with
          | Forall ({ var ; ty }, b)
          | Exists ({ var ; ty }, b) ->
              with_var ~fresh:true sss.tycx { var ; ty } begin fun { var ; ty } cx ->
                Format.fprintf sss.out "inst_%s[of \"\\<lambda> %s :: %a. %a\" \"%a\"]%s"
                  (match side with `l -> "l" | _ -> "r")
                  var pp_ty ty
                  pp_formx { tycx = cx ; data = b }
                  pp_termx tx
                  (CCString.of_list sss.close)
              end
          | _ -> fail ()
        end
      | Cos_rule_name name ->
          Format.fprintf sss.out "%a%s"
            Cos.pp_rule_name name
            (CCString.of_list sss.close)
    end
  | Some (dir, path) -> begin
      match dir, expose sss.conclusion, expose sss.premise with
      | `l, And (b, _), And (a, _)
      | `r, And (_, b), And (_, a) ->
          Format.fprintf sss.out "impE[OF go_%s_and "
            (match dir with `l -> "left" | _ -> "right") ;
          step_surgery ~emit
            { sss with
              to_here = Q.snoc sss.to_here dir ;
              from_here = path ;
              premise = a ; conclusion = b ;
              close = ']' :: sss.close }
      | `l, Or (b, _), Or (a, _)
      | `r, Or (_, b), Or (_, a) ->
          Format.fprintf sss.out "impE[OF go_%s_or "
            (match dir with `l -> "left" | _ -> "right") ;
          step_surgery ~emit
            { sss with
              to_here = Q.snoc sss.to_here dir ;
              from_here = path ;
              premise = a ; conclusion = b ;
              close = ']' :: sss.close }
      | `l, Imp (b, _), Imp (a, _)
      | `r, Imp (_, b), Imp (_, a) ->
          Format.fprintf sss.out "impE[OF go_%s_imp "
            (match dir with `l -> "left" | _ -> "right") ;
          step_surgery ~emit
            { sss with
              to_here = Q.snoc sss.to_here dir ;
              from_here = path ;
              premise = if dir = `l then b else a ;
              conclusion = if dir = `l then a else b ;
              close = ']' :: sss.close }
      | `d, Forall ({ var ; ty }, q), Forall (_, p)
      | `d, Exists ({ var ; ty }, q), Exists (_, p)
      | `i var, Forall ({ ty ; _ }, q), Forall (_, p)
      | `i var, Exists ({ ty ; _ }, q), Exists (_, p) ->
          with_var ~fresh:true sss.tycx { var ; ty } begin fun vty tycx ->
            let lemid = "d" ^ fresh_inner_counter () in
            let transport_rule = match expose sss.conclusion with
              | Forall _ -> "go_down_all"
              | _ -> "go_down_ex"
            in
            Format.fprintf sss.out "impE[OF %s " transport_rule ;
            step_surgery ~emit
              { sss with
                from_here = Q.empty ;
                rule = Inner_reference lemid ;
                close = ']' :: sss.close } ;
            let buf = Buffer.create 19 in
            emit buf ;
            let out = Format.formatter_of_buffer buf in
            let prefix = List.fold_left begin fun lem vty ->
                Format.asprintf "\\<And> %s :: %a. %s"
                  vty.var pp_ty vty.ty lem
              end "" sss.tycx.linear in
            Format.fprintf out "@[<v0>have %s: \"%s%a\"@," lemid
              prefix
              pp_formx { tycx = sss.tycx ; data = Mk.mk_all vty (Mk.mk_imp p q) } ;
            Format.fprintf out "proof@," ;
            List.iter begin fun vty ->
              Format.fprintf out "  fix %s :: \"%a\"@," vty.var pp_ty vty.ty
            end (List.rev sss.tycx.linear) ;
            Format.fprintf out "  fix %s :: \"%a\"@," vty.var pp_ty vty.ty ;
            Format.fprintf out "  show \"%a\"@,"
              pp_formx { tycx ; data = Mk.mk_imp p q } ;
            Format.fprintf out "  by (rule " ;
            let sss = { sss with
                        out ; tycx ; premise = p ; conclusion = q ;
                        to_here = Q.empty ; from_here = path ;
                        close = [] } in
            step_surgery ~emit sss ;
            Format.fprintf out ")@,qed@]@?"
          end
      | _ -> raise Unprintable
    end

let pp_rule stepno out (prem, rule, goal) =
  let bufs = ref [] in
  let emit buf = bufs := buf :: !bufs in
  let mainbuf = Buffer.create 19 in
  emit mainbuf ;
  let mainout = Format.formatter_of_buffer mainbuf in
  Format.fprintf mainout "have l%d: \"%a\"@,  by (rule impE[OF "
    (stepno + 1) pp_formx goal ;
  step_surgery ~emit {
    out = mainout ;
    close = [] ;
    to_here = Q.empty ;
    from_here = rule.Cos.path ;
    tycx = empty ;
    premise = prem.data ;
    conclusion = goal.data ;
    rule = Cos_rule_name rule.Cos.name ;
  } ;
  Format.fprintf mainout " l%d])@?" stepno ;
  List.iter begin fun buf ->
    Buffer.contents buf
    |> String.split_on_char '\n'
    |> List.iter (Format.fprintf out "%s@,")
  end !bufs

let pp_rule_old stepno out (prem, rule, goal) =
  let has_subproof = ref false in
  let lbuf = Buffer.create 19 in
  let lout = Format.formatter_of_buffer lbuf in
  let lem_count = ref 0 in
  let emit_lemma cx f =
    let lemid = "i" ^ string_of_int !lem_count in
    incr lem_count ;
    let prefix = match cx.linear with
      | [] -> ""
      | vars ->
          "\\<And> "
          ^ String.concat " " (List.rev_map (fun v -> v.var) vars)
          ^ ". "
    in
    Format.fprintf lout "  @[<v0>have %s: \"%s%a\"@,sorry@]@,"
      lemid prefix pp_formx { data = f ; tycx = cx } ;
    lemid
  in
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
                make_eqns (ty_norm ty) ss ts |>
                make_lemma { tycx = cx ; data = fc } |>
                Format.fprintf out "(_ : %s)" ;
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
            let ty = ty_norm @@ ty_infer cx head in
            make_eqns ty ss ts |>
            make_lemma { tycx = cx ; data = fc } |>
            Format.fprintf out "(_ : %s)" ;
            has_subproof := true
        | _ -> fail ()
      end
    | Cos.Inst { side ; term = tx } -> begin
        let f = if side = `l then fp else fc in
        let fail () =
          Format.kasprintf unprintable
            "inst_%s: got %a"
            (match side with `l -> "l" | _ -> "r")
            Form4.pp_formx { tycx = cx ; data = f } in
        match expose f with
        | Forall ({ var ; ty }, b)
        | Exists ({ var ; ty }, b) ->
            with_var ~fresh:true cx { var ; ty } begin fun { var ; ty } cx ->
              Format.fprintf out "@@inst_%s %a (fun (%s : %a), %a) (%a)"
                (match side with `l -> "l" | _ -> "r")
                pp_ty ty
                var pp_ty ty
                pp_formx { tycx = cx ; data = b }
                pp_termx tx
            end
        | _ -> fail ()
      end
    | _ -> Cos.pp_rule_name out name
  in
  let rec pp_path close cx goal prem path =
    match Q.take_front path with
    | None ->
        pp_rule cx goal prem rule.Cos.name ;
        (* if Q.is_empty rule.Cos.path then *)
        (*   Format.fprintf out " l%d])@." stepno *)
        (* else *)
          Format.fprintf out "%s l%d])@,"
            (CCString.of_list close) stepno ;
        if !has_subproof then begin
          Format.fprintf out "  { profint_discharge },@." ;
          has_subproof := false
        end
    | Some (dir, path) -> begin
        match expose goal, expose prem, dir with
        | And (b, c), And (a, _), `l ->
            Format.fprintf out "impE[OF go_left_and " ;
            pp_path (']' :: close) cx b a path
        | And (c, b), And (_, a), `r ->
            Format.fprintf out "impE[OF go_right_and " ;
            pp_path (']' :: close) cx b a path
        | Or (b, c), Or (a, _), `l ->
            Format.fprintf out "impE[OF go_left_or " ;
            pp_path (']' :: close) cx b a path
        | Or (c, b), Or (_, a), `r ->
            Format.fprintf out "impE[OF go_right_or " ;
            pp_path (']' :: close) cx b a path
        | Imp (b, c), Imp (a, _), `l ->
            Format.fprintf out "impE[OF go_left_imp " ;
            pp_path (']' :: close) cx a b path
        | Imp (c, b), Imp (_, a), `r ->
            Format.fprintf out "impE[OF go_right_imp " ;
            pp_path (']' :: close) cx b a path
        | Forall ({ var ; ty }, q), Forall (_, p), `d
        | Forall ({ ty ; _ }, q), Forall (_, p), `i var ->
            let old_cx = cx in
            with_var ~fresh:true cx { var ; ty } begin fun vty cx ->
              let lemid = emit_lemma old_cx (Mk.mk_all vty (Mk.mk_imp p q)) in
              Format.fprintf out "impE[OF go_down_all %s]" lemid ;
              pp_path (')' :: ']' :: close) cx q p path
            end
        | Exists ({ var ; ty }, q), Exists (_, p), `d
        | Exists ({ ty ; _ }, q), Exists (_, p), `i var ->
            let old_cx = cx in
            with_var ~fresh:true cx { var ; ty } begin fun vty cx ->
              let lemid = emit_lemma old_cx (Mk.mk_all vty (Mk.mk_imp p q)) in
              Format.fprintf out "impE[OF go_down_ex %s]" lemid ;
              pp_path (')' :: ']' :: close) cx q p path
            end
        | _ ->
            String.concat " " [ "pp_rule:" ;
                                pp_to_string Cos.pp_rule rule ;
                                "::" ;
                                pp_to_string pp_formx { tycx = cx ; data = goal } ]
            |> unprintable
      end
  in
  Format.fprintf out "have l%d: \"%a\"@,  by (rule impE[OF "
    (stepno + 1) pp_formx goal ;
  pp_path [] goal.tycx goal.data prem.data rule.path ;
  Format.pp_print_flush lout () ;
  Format.fprintf out "(* %s *)@," (Buffer.contents lbuf)

let pp_step out stepno (prem, _, _ as prc) =
  pp_rule stepno out prc

let pp_deriv out (sg, deriv) =
  Format.fprintf out "lemma profint__export:@.%a  assumes prem: \"%a\"@.  shows \"%a\"@."
    pp_sigma sg
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  Format.fprintf out "proof -@.  @[<v0>" ;
  Format.fprintf out "have l0: \"%a\" by (rule prem)@,"
    pp_formx deriv.Cos.top ;
  List.iteri (pp_step out) deriv.Cos.middle ;
  Format.fprintf out "show \"%a\" by (rule l%d)@]@."
    pp_formx deriv.Cos.bottom
    (List.length deriv.Cos.middle) ;
  Format.fprintf out "qed@.@.print_statement profint__export@."

let pp_header out () =
  Format.fprintf out "import Profint@." ;
  Format.fprintf out "open Profint@."

let pp_footer _out () = ()

let pp_comment out str =
  Format.fprintf out "/- %s -/@\n" str

let name = "isahol"
let files pf =
  let replace contents =
    CCString.replace ~which:`Left contents
      ~sub:"(*PROOF*)\n" ~by:pf
  in [
    File { fname = "Profint.thy" ;
           contents = [%blob "lib/systems/isabelle_hol/Profint.thy"] } ;
    File { fname = "Proof.thy" ;
           contents = replace [%blob "lib/systems/isabelle_hol/Proof.thy"] } ;
    File { fname = "ROOT" ;
           contents = replace [%blob "lib/systems/isabelle_hol/ROOT"] } ;
  ]
let build () = "leanpkg build"
