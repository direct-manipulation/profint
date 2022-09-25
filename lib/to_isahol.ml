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
      let rep = if Ident.equal a Ty.k_o then "bool" else "'" ^ (Ident.to_string a) in
      Doc.(Atom (String rep))
  | Ty.Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (StringAs (3, " \\<Rightarrow> "), Right,
                           [ty_to_exp ta ; ty_to_exp tb])))
  | Ty.Var v -> begin
      match v.subst with
      | None -> Doc.(Atom (String "_"))
      | Some ty -> ty_to_exp ty
    end

let pp_ty out ty = ty_to_exp ty |> Doc.bracket |> Doc.pp_lin_doc out
let ty_to_string ty = pp_to_string pp_ty ty

let rec termx_to_exp_ ~cx t =
  match t with
  | T.Abs { var ; body } ->
      with_var cx { var ; ty = K.ty_any } begin fun vty cx ->
        let rep = Doc.String (Printf.sprintf "\\<lambda> %s. " (Ident.to_string vty.var)) in
        Doc.(Appl (1, Prefix (rep, termx_to_exp_  ~cx body)))
      end
  | T.App { head ; spine = [] } ->
      Term.head_to_exp ~cx head
  | T.App { head ; spine } ->
      let head = Term.head_to_exp ~cx head in
      let spine = List.map ~f:(termx_to_exp_ ~cx) spine in
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
      with_var cx vty begin fun vty cx ->
        let q = Doc.Fmt Caml.Format.(fun out ->
            pp_print_as out 3 "\\<forall> " ;
            pp_print_string out (Ident.to_string vty.var) ;
            pp_print_string out " :: " ;
            pp_ty out vty.ty ;
            pp_print_string out ". ") in
        let b = formx_to_exp_ ~cx b in
        Doc.(Appl (5, Prefix (q, b)))
      end
  | Exists (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let q = Doc.Fmt Caml.Format.(fun out ->
            pp_print_as out 3 "\\<exists> " ;
            pp_print_string out (Ident.to_string vty.var) ;
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
  Map.iteri sg.consts ~f:begin fun ~key:k ~data:ty ->
    if Map.mem sigma0.consts k then () else
      Caml.Format.fprintf out "  fixes %s :: \"%s\"@."
        (Ident.to_string k) (ty_to_string @@ thaw_ty ty)
  end

exception Unprintable
let unprintable reason =
  Caml.Format.eprintf "to_isahol: failure: %s@." reason ;
  raise Unprintable

let rec make_eqns ty ss ts =
  match ty, ss, ts with
  | _, [], [] -> []
  | Ty.Arrow (a, ty), (s :: ss), (t :: tt) ->
      let eqs = make_eqns ty ss tt in
      if Term.eq_term s t then eqs else (s, t, a) :: eqs
  | _ ->
      unprintable "make_eqns"

type step_surgery_rule =
  | Inner_reference of string
  | Cos_rule_name of Cos.rule_name

type step_surgery_state = {
  out : Caml.Format.formatter ;
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
    Int.incr ctr ;
    "i" ^ Int.to_string !ctr

let init_like_lemma ~emit sss ty ss ts target =
  let eqns =
    make_eqns (Ty.norm ty) ss ts |>
    List.filter_map ~f:begin fun (l, r, _) ->
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
  let lem = List.fold_left sss.tycx.linear ~init:lem
      ~f:begin fun lem vty ->
        Caml.Format.asprintf "\\<And> %s :: %a. %s"
          (Ident.to_string vty.var) pp_ty vty.ty lem
      end in
  let buf = Buffer.create 19 in
  emit buf ;
  let out = Caml.Format.formatter_of_buffer buf in
  let lemid = "i" ^ fresh_inner_counter () in
  Caml.Format.fprintf out "have %s: \"%s\"@,  by blast@?" lemid lem ;
  Caml.Format.fprintf sss.out "%s%s"
    lemid (CCString.of_list sss.close)

let rec step_surgery ~emit sss =
  match Q.take_front sss.from_here with
  | None -> begin
      match sss.rule with
      | Inner_reference lemid ->
          Caml.Format.fprintf sss.out "%s%s"
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
              let ty = Ty.norm @@ ty_infer sss.tycx head in
              init_like_lemma ~emit sss ty ss ts sss.conclusion
            end
          | _ -> fail ()
        end
      | Cos_rule_name (Cos.Inst { side ; term = tx }) -> begin
          let f = if Poly.(side = `l) then sss.premise else sss.conclusion in
          let fail () =
            Caml.Format.kasprintf unprintable
              "inst_%s: got %a"
              (match side with `l -> "l" | _ -> "r")
              Form4.pp_formx { tycx = sss.tycx ; data = f } in
          match expose f with
          | Forall ({ var ; ty }, b)
          | Exists ({ var ; ty }, b) ->
              with_var sss.tycx { var ; ty } begin fun { var ; ty } cx ->
                Caml.Format.fprintf sss.out "inst_%s[of \"\\<lambda> %s :: %a. %a\" \"%a\"]%s"
                  (match side with `l -> "l" | _ -> "r")
                  (Ident.to_string var) pp_ty ty
                  pp_formx { tycx = cx ; data = b }
                  pp_termx tx
                  (CCString.of_list sss.close)
              end
          | _ -> fail ()
        end
      | Cos_rule_name name ->
          Caml.Format.fprintf sss.out "%a%s"
            Cos.pp_rule_name name
            (CCString.of_list sss.close)
    end
  | Some (dir, path) -> begin
      match dir, expose sss.conclusion, expose sss.premise with
      | `l, And (b, _), And (a, _)
      | `r, And (_, b), And (_, a) ->
          Caml.Format.fprintf sss.out "impE[OF go_%s_and "
            (match dir with `l -> "left" | _ -> "right") ;
          step_surgery ~emit
            { sss with
              to_here = Q.snoc sss.to_here dir ;
              from_here = path ;
              premise = a ; conclusion = b ;
              close = ']' :: sss.close }
      | `l, Or (b, _), Or (a, _)
      | `r, Or (_, b), Or (_, a) ->
          Caml.Format.fprintf sss.out "impE[OF go_%s_or "
            (match dir with `l -> "left" | _ -> "right") ;
          step_surgery ~emit
            { sss with
              to_here = Q.snoc sss.to_here dir ;
              from_here = path ;
              premise = a ; conclusion = b ;
              close = ']' :: sss.close }
      | `l, Imp (b, _), Imp (a, _)
      | `r, Imp (_, b), Imp (_, a) ->
          Caml.Format.fprintf sss.out "impE[OF go_%s_imp "
            (match dir with `l -> "left" | _ -> "right") ;
          step_surgery ~emit
            { sss with
              to_here = Q.snoc sss.to_here dir ;
              from_here = path ;
              premise = if Caml.(dir = `l) then b else a ;
              conclusion = if Caml.(dir = `l) then a else b ;
              close = ']' :: sss.close }
      | `d, Forall ({ var ; ty }, q), Forall (_, p)
      | `d, Exists ({ var ; ty }, q), Exists (_, p)
      | `i var, Forall ({ ty ; _ }, q), Forall (_, p)
      | `i var, Exists ({ ty ; _ }, q), Exists (_, p) ->
          with_var sss.tycx { var ; ty } begin fun vty tycx ->
            let lemid = "d" ^ fresh_inner_counter () in
            let transport_rule = match expose sss.conclusion with
              | Forall _ -> "go_down_all"
              | _ -> "go_down_ex"
            in
            Caml.Format.fprintf sss.out "impE[OF %s " transport_rule ;
            step_surgery ~emit
              { sss with
                from_here = Q.empty ;
                rule = Inner_reference lemid ;
                close = ']' :: sss.close } ;
            let buf = Buffer.create 19 in
            emit buf ;
            let out = Caml.Format.formatter_of_buffer buf in
            let prefix = List.fold_left ~f:begin fun lem vty ->
                Caml.Format.asprintf "\\<And> %s :: %a. %s"
                  (Ident.to_string vty.var) pp_ty vty.ty lem
              end ~init:"" sss.tycx.linear in
            Caml.Format.fprintf out "@[<v0>have %s: \"%s%a\"@," lemid
              prefix
              pp_formx { tycx = sss.tycx ; data = Mk.mk_all vty (Mk.mk_imp p q) } ;
            Caml.Format.fprintf out "proof@," ;
            List.iter ~f:begin fun vty ->
              Caml.Format.fprintf out "  fix %s :: \"%a\"@," (Ident.to_string vty.var) pp_ty vty.ty
            end (List.rev sss.tycx.linear) ;
            Caml.Format.fprintf out "  fix %s :: \"%a\"@," (Ident.to_string vty.var) pp_ty vty.ty ;
            Caml.Format.fprintf out "  show \"%a\"@,"
              pp_formx { tycx ; data = Mk.mk_imp p q } ;
            Caml.Format.fprintf out "  by (rule " ;
            let sss = { sss with
                        out ; tycx ; premise = p ; conclusion = q ;
                        to_here = Q.empty ; from_here = path ;
                        close = [] } in
            step_surgery ~emit sss ;
            Caml.Format.fprintf out ")@,qed@]@?"
          end
      | _ -> raise Unprintable
    end

let pp_rule stepno out (prem, rule, goal) =
  let bufs = ref [] in
  let emit buf = bufs := buf :: !bufs in
  let mainbuf = Buffer.create 19 in
  emit mainbuf ;
  let mainout = Caml.Format.formatter_of_buffer mainbuf in
  Caml.Format.fprintf mainout "have l%d: \"%a\"@,  by (rule impE[OF "
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
  Caml.Format.fprintf mainout " l%d])@?" stepno ;
  List.iter ~f:begin fun buf ->
    Buffer.contents buf
    |> String.split ~on:'\n'
    |> List.iter ~f:(Caml.Format.fprintf out "%s@,")
  end !bufs

let pp_step out stepno prc = pp_rule stepno out prc

let pp_deriv out (sg, deriv) =
  Caml.Format.fprintf out "lemma profint__export:@.%a  assumes prem: \"%a\"@.  shows \"%a\"@."
    pp_sigma sg
    pp_formx deriv.Cos.top
    pp_formx deriv.Cos.bottom ;
  Caml.Format.fprintf out "proof -@.  @[<v0>" ;
  Caml.Format.fprintf out "have l0: \"%a\" by (rule prem)@,"
    pp_formx deriv.Cos.top ;
  List.iteri ~f:(pp_step out) deriv.Cos.middle ;
  Caml.Format.fprintf out "show \"%a\" by (rule l%d)@]@."
    pp_formx deriv.Cos.bottom
    (List.length deriv.Cos.middle) ;
  Caml.Format.fprintf out "qed@.@.print_statement profint__export@."

let pp_header out () =
  Caml.Format.fprintf out "import Profint@." ;
  Caml.Format.fprintf out "open Profint@."

let pp_footer _out () = ()

let pp_comment out str =
  Caml.Format.fprintf out "/- %s -/@\n" str

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
