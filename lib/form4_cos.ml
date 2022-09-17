(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Util
open Types
open T
open Form4_core
open Form4_paths
open Mk

(******************************************************************************)
(* CoS rules *)

type rule_name =
  | Goal_ts_imp of { pick : side }
  | Goal_imp_ts
  | Goal_ts_and of { pick : side }
  | Goal_and_ts of { pick : side }
  | Goal_ts_or  of { pick : side }
  | Goal_or_ts
  | Goal_ts_all
  | Goal_all_ts
  | Goal_ts_ex
  | Goal_ex_ts

  | Init
  | Rewrite of { from : side }

  | Asms_and of { minor : side ; pick : side }
  | Asms_or  of { minor : side ; pick : side }
  | Asms_imp of { minor : side ; pick : side }
  | Asms_all of { minor : side }
  | Asms_ex  of { minor : side }

  | Simp_and_top of { cxkind : side ; minor : side }
  | Simp_or_top  of { cxkind : side ; minor : side }
  | Simp_imp_top of { cxkind : side ; minor : side }
  | Simp_all_top of { cxkind : side }

  | Simp_and_bot of { cxkind : side ; minor : side }
  | Simp_or_bot  of { cxkind : side ; minor : side }
  | Simp_bot_imp of { cxkind : side }
  | Simp_ex_bot  of { cxkind : side }

  | Congr
  | Contract
  | Weaken
  | Inst of { side : side ; term : term incx }

and rule = {
  name : rule_name ;
  path : path ;
}

let side_to_string (side : side) =
  match side with
  | `l -> "l"
  | `r -> "r"

let pp_rule_name out rn =
  match rn with
  | Goal_ts_imp { pick} ->
      Format.fprintf out "goal_ts_imp_%s" (side_to_string pick)
  | Goal_imp_ts ->
      Format.fprintf out "goal_imp_ts"
  | Goal_ts_and { pick } ->
      Format.fprintf out "goal_ts_and_%s" (side_to_string pick)
  | Goal_and_ts { pick } ->
      Format.fprintf out "goal_and_ts_%s" (side_to_string pick)
  | Goal_ts_or  { pick } ->
      Format.fprintf out "goal_ts_or_%s" (side_to_string pick)
  | Goal_or_ts ->
      Format.fprintf out "goal_or_ts"
  | Goal_ts_all ->
      Format.fprintf out "goal_ts_all"
  | Goal_all_ts ->
      Format.fprintf out "goal_all_ts"
  | Goal_ts_ex ->
      Format.fprintf out "goal_ts_ex"
  | Goal_ex_ts ->
      Format.fprintf out "goal_ex_ts"
  | Asms_and { minor ; pick } ->
      Format.fprintf out "asms_and_%s_%s"
        (side_to_string minor) (side_to_string pick)
  | Asms_or  { minor ; pick } ->
      Format.fprintf out "asms_or_%s_%s"
        (side_to_string minor) (side_to_string pick)
  | Asms_imp { minor ; pick } ->
      Format.fprintf out "asms_imp_%s_%s"
        (side_to_string minor) (side_to_string pick)
  | Asms_all { minor } ->
      Format.fprintf out "asms_all_%s"
        (side_to_string minor)
  | Asms_ex  { minor } ->
      Format.fprintf out "asms_ex_%s"
        (side_to_string minor)
  | Simp_and_top { cxkind ; minor } ->
      Format.fprintf out "simp_%s_%s_%s"
        (match cxkind with `r -> "goal" | _ -> "asms")
        (match minor with `l -> "and" | _ -> "top")
        (match minor with `l -> "top" | _ -> "and")
  | Simp_or_top { cxkind ; minor } ->
      Format.fprintf out "simp_%s_%s_%s"
        (match cxkind with `r -> "goal" | _ -> "asms")
        (match minor with `l -> "or" | _ -> "top")
        (match minor with `l -> "top" | _ -> "or")
  | Simp_imp_top { cxkind ; minor } ->
      Format.fprintf out "simp_%s_%s_%s"
        (match cxkind with `r -> "goal" | _ -> "asms")
        (match minor with `l -> "imp" | _ -> "top")
        (match minor with `l -> "top" | _ -> "imp")
  | Simp_all_top { cxkind } ->
      Format.fprintf out "simp_%s_all_top"
        (match cxkind with `r -> "goal" | _ -> "asms")
  | Simp_and_bot { cxkind ; minor } ->
      Format.fprintf out "simp_%s_%s_%s"
        (match cxkind with `r -> "goal" | _ -> "asms")
        (match minor with `l -> "and" | _ -> "bot")
        (match minor with `l -> "bot" | _ -> "and")
  | Simp_or_bot { cxkind ; minor } ->
      Format.fprintf out "simp_%s_%s_%s"
        (match cxkind with `r -> "goal" | _ -> "asms")
        (match minor with `l -> "or" | _ -> "bot")
        (match minor with `l -> "bot" | _ -> "or")
  | Simp_bot_imp { cxkind } ->
      Format.fprintf out "simp_%s_bot_imp"
        (match cxkind with `r -> "goal" | _ -> "asms")
  | Simp_ex_bot { cxkind } ->
      Format.fprintf out "simp_%s_ex_bot"
        (match cxkind with `r -> "goal" | _ -> "asms")
  | Init ->
      Format.fprintf out "init"
  | Rewrite { from } ->
      Format.fprintf out "rewrite_%s"
        (match from with `l -> "ltr" | _ -> "rtl")
  | Congr ->
      Format.fprintf out "congr"
  | Contract ->
      Format.fprintf out "contract"
  | Weaken ->
      Format.fprintf out "weaken"
  | Inst { side ; term = tx } ->
      Format.fprintf out "inst_%s[@[%a@]]"
        (side_to_string side)
        (Term.pp_term ~cx:tx.tycx) tx.data

let rec pp_path_list out path =
  match path with
  | [] -> ()
  | [`l] -> Format.fprintf out "l"
  | [`r] -> Format.fprintf out "r"
  | [`i x] -> Format.fprintf out "i %s" x
  | [`d] -> Format.fprintf out "d"
  | dir :: (_ :: _ as path) ->
      Format.fprintf out "%a, %a" pp_path_list [dir] pp_path_list path

let pp_path out (path : path) =
  pp_path_list out (Q.to_list path)

let pp_rule out rule =
  Format.fprintf out "@[%a%s:: %a@]"
    pp_path rule.path
    (if Q.size rule.path = 0 then "" else " ")
    pp_rule_name rule.name

let rule_to_string rule = pp_to_string pp_rule rule

exception Bad_spines of {ty : ty ; ss : spine ; ts : spine}

let rec spine_equations (ty : ty) (ss : spine) (ts : spine) : form list =
  let ty = ty_norm ty in
  match ty, ss, ts with
  | Arrow (tya, ty), (s :: ss), (t :: ts) ->
      (if Term.eq_term s t then [] else [mk_eq s t tya]) @
      spine_equations ty ss ts
  | _, [], [] -> []
  | _ -> raise @@ Bad_spines { ty ; ss ; ts }

let rec mk_big_and fs =
  match fs with
  | [] -> mk_top
  | [f] -> f
  | f :: fs -> mk_and f (mk_big_and fs)

let compute_spine_congruence (ty : ty) (ss : spine) (ts : spine) : form =
  mk_big_and @@ spine_equations ty ss ts

exception Bad_match of {goal : formx ; rule : rule}

let shift n t = Term.(sub_term (Shift n) t) [@@inline]

type cos_premise = {
  goal : formx ;
  prin : formx ;
}

let compute_premise (goal : formx) (rule : rule) : cos_premise =
  let bad_match msg =
    (* Format.printf "@.Bad_match[%s]:@. rule = %a@.goal = %a@." *)
    (*   msg pp_rule rule pp_formx goal ; *)
    Format.eprintf "compute_premise: bad_match: %s@." msg ;
    raise @@ Bad_match {goal ; rule} in
  let (prin, side) = formx_at goal rule.path in
  let prin = {
    prin with data = match side, expose prin.data, rule.name with
      (* goal *)
      | `r, Imp (a, f), Goal_ts_imp { pick } -> begin
          match expose f, pick with
          | Imp (b, f), `l ->
              mk_imp (mk_and a b) f
          | Imp (f, b), `r ->
              mk_imp f (mk_imp a b)
          | _ -> bad_match "0"
        end
      | `r, Imp (f, b), Goal_imp_ts -> begin
          match expose f with
          | Imp (f, a) ->
              mk_and f (mk_imp a b)
          | _ -> bad_match "1"
        end
      | `r, Imp (a, f), Goal_ts_and { pick } -> begin
          match expose f, pick with
          | And (b, f), `l ->
              mk_and (mk_imp a b) f
          | And (f, b), `r ->
              mk_and f (mk_imp a b)
          | _ -> bad_match "2"
        end
      | `r, Imp (f, b), Goal_and_ts { pick } -> begin
          match expose f, pick with
          | And (a, _), `l
          | And (_, a), `r ->
              mk_imp a b
          | _ -> bad_match "3"
        end
      | `r, Imp (a, f), Goal_ts_or { pick } -> begin
          match expose f, pick  with
          | Or (b, _), `l
          | Or (_, b), `r ->
              mk_imp a b
          | _ -> bad_match "4"
        end
      | `r, Imp (f, b), Goal_or_ts -> begin
          match expose f with
          | Or (a1, a2) ->
              mk_and (mk_imp a1 b) (mk_imp a2 b)
          | _ -> bad_match "5"
        end
      | `r, Imp (a, f), Goal_ts_all -> begin
          match expose f with
          | Forall (vty, b) ->
              mk_all vty (mk_imp (shift 1 a) b)
          | _ -> bad_match "6"
        end
      | `r, Imp (f, b), Goal_all_ts -> begin
          match expose f with
          | Forall (vty, a) ->
              mk_ex vty (mk_imp a (shift 1 b))
          | _ -> bad_match "7"
        end
      | `r, Imp (a, f), Goal_ts_ex -> begin
          match expose f with
          | Exists (vty, b) ->
              mk_ex vty (mk_imp (shift 1 a) b)
          | _ -> bad_match "8"
        end
      | `r, Imp (f, b), Goal_ex_ts -> begin
          match expose f with
          | Exists (vty, a) ->
              mk_all vty (mk_imp a (shift 1 b))
          | _ -> bad_match "9"
        end
      (* assumptions *)
      | `l, And (a, f), Asms_and { minor = `l ; pick = sel } -> begin
          match expose f, sel with
          | And (b, _), `l
          | And (_, b), `r ->
              mk_and a b
          | _ -> bad_match "10"
        end
      | `l, And (f, b), Asms_and { minor = `r ; pick = sel } -> begin
          match expose f, sel with
          | And (a, _), `l
          | And (_, a), `r ->
              mk_and a b
          | _ -> bad_match "11"
        end
      | `l, And (a, f), Asms_or { minor = `l ; pick = sel } -> begin
          match expose f, sel with
          | Or (b, f), `l ->
              mk_or (mk_and a b) f
          | Or (f, b), `r ->
              mk_or f (mk_and a b)
          | _ -> bad_match "12"
        end
      | `l, And (f, b), Asms_or { minor = `r ; pick = sel } -> begin
          match expose f, sel with
          | Or (a, f), `l ->
              mk_or (mk_and a b) f
          | Or (f, a), `r ->
              mk_or f (mk_and a b)
          | _ -> bad_match "13"
        end
      | `l, And (a, f), Asms_imp { minor = `l ; pick = sel } -> begin
          match expose f, sel with
          | Imp (b, f), `l ->
              mk_imp (mk_imp a b) f
          | Imp (f, b), `r ->
              mk_imp f (mk_and a b)
          | _ -> bad_match "14"
        end
      | `l, And (f, b), Asms_imp { minor = `r ; pick = sel } -> begin
          match expose f, sel with
          | Imp (a, f), `l ->
              mk_imp (mk_imp b a) f
          | Imp (f, a), `r ->
              mk_imp f (mk_and a b)
          | _ -> bad_match "15"
        end
      | `l, And (a, f), Asms_all { minor = `l } -> begin
          match expose f with
          | Forall (vty, b) ->
              mk_all vty (mk_and (shift 1 a) b)
          | _ -> bad_match "16"
        end
      | `l, And (f, b), Asms_all { minor = `r } -> begin
          match expose f with
          | Forall (vty, a) ->
              mk_all vty (mk_and a (shift 1 b))
          | _ -> bad_match "17"
        end
      | `l, And (a, f), Asms_ex { minor = `l } -> begin
          match expose f with
          | Exists (vty, b) ->
              mk_ex vty (mk_and (shift 1 a) b)
          | _ -> bad_match "18"
        end
      | `l, And (f, b), Asms_ex { minor = `r } -> begin
          match expose f with
          | Exists (vty, a) ->
              mk_ex vty (mk_and a (shift 1 b))
          | _ -> bad_match "19"
        end
      (* simplification: top *)
      | ( _, And (a, f), Simp_and_top { cxkind ; minor = `l }
        | _, And (f, a), Simp_and_top { cxkind ; minor = `r } )
        when cxkind = side -> begin
          match expose f with
          | Top -> a
          | _ -> bad_match "20"
        end
      | ( _, Or (_, f), Simp_or_top { cxkind ; minor = `l }
        | _, Or (f, _), Simp_or_top { cxkind ; minor = `r } )
        when cxkind = side -> begin
          match expose f with
          | Top -> f
          | _ -> bad_match "21"
        end
      | _, Imp (_, f), Simp_imp_top { cxkind ; minor = `l }
        when cxkind = side -> begin
          match expose f with
          | Top -> f
          | _ -> bad_match "22"
        end
      | _, Imp (f, a), Simp_imp_top { cxkind ; minor = `r }
        when cxkind = side -> begin
          match expose f with
          | Top -> a
          | _ -> bad_match "23"
        end
      | _, Forall (_, f), Simp_all_top { cxkind }
        when cxkind = side -> begin
          match expose f with
          | Top -> f
          | _ -> bad_match "24"
        end
      (* simplification: bot *)
      | ( _, And (_, f), Simp_and_bot { cxkind ; minor = `l }
        | _, And (f, _), Simp_and_bot { cxkind ; minor = `r } )
        when cxkind = side -> begin
          match expose f with
          | Bot -> f
          | _ -> bad_match "25"
        end
      | ( _, Or (a, f), Simp_or_bot { cxkind ; minor = `l }
        | _, Or (f, a), Simp_or_bot { cxkind ; minor = `r } )
        when cxkind = side -> begin
          match expose f with
          | Bot -> a
          | _ -> bad_match "26"
        end
      | _, Imp (f, _), Simp_bot_imp { cxkind }
        when cxkind = side -> begin
          match expose f with
          | Bot -> mk_top
          | _ -> bad_match "27"
        end
      | _, Exists (_, f), Simp_ex_bot { cxkind }
        when cxkind = side -> begin
          match expose f with
          | Bot -> f
          | _ -> bad_match "28"
        end
      (* structural *)
      | `r, Imp (a, b), Init -> begin
          match expose a, expose b with
          | Atom (App { head = f ; spine = ss }),
            Atom (App { head = g ; spine = ts }) when Term.eq_head f g ->
              compute_spine_congruence (Term.ty_infer prin.tycx f) ss ts
          | _ -> bad_match "29"
        end
      | `r, Imp (a, b), Rewrite { from } -> begin
          match expose a with
          | Eq (s, t, _) -> begin
              let (tfrom, tto) = match from with
                | `l -> s, t
                | _ -> t, s
              in
              Term.rewrite ~tfrom ~tto b
            end
          | _ -> bad_match "30"
        end
      | `r, Eq (s, t, _), Congr -> begin
          match s, t with
          | App { head = f ; spine = ss },
            App { head = g ; spine = ts } when Term.eq_head f g ->
              compute_spine_congruence (Term.ty_infer prin.tycx f) ss ts
          | _ -> bad_match "31"
        end
      | `r, Imp (a, b), Contract ->
          mk_imp a (mk_imp a b)
      | `r, Imp (_, b), Weaken ->
          b
      | `l, Forall (vty, b), Inst { side = `l ; term = wtx }
      | `r, Exists (vty, b), Inst { side = `r ; term = wtx } ->
          Term.ty_check prin.tycx wtx.data vty.ty ;
          Term.do_app (Abs {var = vty.var ; body = b}) [wtx.data]
      | _ -> bad_match "32"
  } in
  let goal = { goal with data = replace_at goal.data rule.path prin.data } in
  { goal ; prin }

(* quick access to top and bottom *)
type deriv = {
  top    : formx ;
  middle : (formx * rule * formx) list ;
  bottom : formx ;
}

exception Cannot_concat of deriv * deriv

let concat d1 d2 =
  (* [HACK] physical equality is probably overkill but whatevs *)
  (* if d1.bottom != d2.top then *)
  (*   raise @@ Cannot_concat (d1, d2) ; *)
  { top = d1.top ;
    middle = d1.middle @ d2.middle ;
    bottom = d2.bottom }
