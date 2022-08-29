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

(******************************************************************************)
(* CoS rules *)

type rule_name =
  | Goal_ts_imp of side
  | Goal_imp_ts
  | Goal_ts_and of side
  | Goal_and_ts of side
  | Goal_ts_or  of side
  | Goal_or_ts
  | Goal_ts_all
  | Goal_all_ts
  | Goal_ts_ex
  | Goal_ex_ts
  | Asms_and of { minor : side ; pick : side }
  | Asms_or  of { minor : side ; pick : side }
  | Asms_imp of { minor : side ; pick : side }
  | Asms_all of { minor : side }
  | Asms_ex  of { minor : side }
  | Simp_imp_true
  | Simp_true_imp of side
  | Simp_false_imp
  | Simp_and_true of side
  | Simp_or_true  of side
  | Simp_all_true
  | Init
  | Congr
  | Contract
  | Weaken
  | Inst of term incx

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
  | Goal_ts_imp side ->
      Format.fprintf out "goal_ts_imp_%s" (side_to_string side)
  | Goal_imp_ts ->
      Format.fprintf out "goal_imp_ts"
  | Goal_ts_and side ->
      Format.fprintf out "goal_ts_and_%s" (side_to_string side)
  | Goal_and_ts side ->
      Format.fprintf out "goal_and_ts_%s" (side_to_string side)
  | Goal_ts_or  side ->
      Format.fprintf out "goal_ts_or_%s" (side_to_string side)
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
  | Simp_imp_true ->
      Format.fprintf out "simp_imp_true"
  | Simp_true_imp side ->
      Format.fprintf out "simp_true_imp_%s"
        (side_to_string side)
  | Simp_false_imp ->
      Format.fprintf out "simp_false_imp"
  | Simp_and_true side ->
      Format.fprintf out "simp_and_true_%s"
        (side_to_string side)
  | Simp_or_true side ->
      Format.fprintf out "simp_or_true_%s"
        (side_to_string side)
  | Simp_all_true ->
      Format.fprintf out "simp_all_true"
  | Init ->
      Format.fprintf out "init"
  | Congr ->
      Format.fprintf out "congr"
  | Contract ->
      Format.fprintf out "contract"
  | Weaken ->
      Format.fprintf out "weaken"
  | Inst tx ->
      Format.fprintf out "inst[@[%a@]]" (Term.pp_term ~cx:tx.tycx) tx.data

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

let rec compute_spine_congruence (ty : ty) (ss : spine) (ts : spine) : form =
  let ty = ty_norm ty in
  match ty, ss, ts with
  | Arrow (tya, ty), (s :: ss), (t :: tt) -> begin
      match ss, tt with
      | [], [] ->
          mk_eq s t tya
      | _ ->
          mk_and (mk_eq s t tya) (compute_spine_congruence ty ss tt)
    end
  | _, [], [] ->
      mk_top
  | _ ->
      raise @@ Bad_spines {ty ; ss ; ts}

exception Bad_match of {goal : formx ; rule : rule}

let shift n t = Term.(sub_term (Shift n) t) [@@inline]

let compute_premise (goal : formx) (rule : rule) : formx =
  let bad_match () =
    Format.eprintf "Bad_match: %a :: %a@."
      pp_rule rule
      Form4_pp.LeanPP.pp goal ;
    raise @@ Bad_match {goal ; rule} in
  let (fx, side) = formx_at goal rule.path in
  let c = match side, expose fx.data, rule.name with
    (* goal *)
    | `r, Imp (a, f), Goal_ts_imp sel -> begin
        match expose f, sel with
        | Imp (b, f), `l ->
            mk_imp (mk_and a b) f
        | Imp (f, b), `r ->
            mk_imp f (mk_imp a b)
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_imp_ts -> begin
        match expose f with
        | Imp (f, a) ->
            mk_and f (mk_imp a b)
        | _ -> bad_match ()
      end
    | `r, Imp (a, f), Goal_ts_and sel -> begin
        match expose f, sel with
        | And (b, f), `l ->
            mk_and (mk_imp a b) f
        | And (f, b), `r ->
            mk_and f (mk_imp a b)
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_and_ts sel -> begin
        match expose f, sel with
        | And (a, _), `l
        | And (_, a), `r ->
            mk_imp a b
        | _ -> bad_match ()
      end
    | `r, Imp (a, f), Goal_ts_or sel -> begin
        match expose f, sel with
        | Or (b, _), `l
        | Or (_, b), `r ->
            mk_imp a b
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_or_ts -> begin
        match expose f with
        | Or (a1, a2) ->
            mk_and (mk_imp a1 b) (mk_imp a2 b)
        | _ -> bad_match ()
      end
    | `r, Imp (a, f), Goal_ts_all -> begin
        match expose f with
        | Forall (vty, b) ->
            mk_all vty (mk_imp (shift 1 a) b)
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_all_ts -> begin
        match expose f with
        | Forall (vty, a) ->
            mk_ex vty (mk_imp a (shift 1 b))
        | _ -> bad_match ()
      end
    | `r, Imp (a, f), Goal_ts_ex -> begin
        match expose f with
        | Exists (vty, b) ->
            mk_ex vty (mk_imp (shift 1 a) b)
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_ex_ts -> begin
        match expose f with
        | Exists (vty, a) ->
            mk_all vty (mk_imp a (shift 1 b))
        | _ -> bad_match ()
      end
    (* assumptions *)
    | `l, And (a, f), Asms_and { minor = `l ; pick = sel } -> begin
        match expose f, sel with
        | And (b, _), `l
        | And (_, b), `r ->
            mk_and a b
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_and { minor = `r ; pick = sel } -> begin
        match expose f, sel with
        | And (a, _), `l
        | And (_, a), `r ->
            mk_and a b
        | _ -> bad_match ()
      end
    | `l, And (a, f), Asms_or { minor = `l ; pick = sel } -> begin
        match expose f, sel with
        | Or (b, f), `l ->
            mk_or (mk_and a b) f
        | Or (f, b), `r ->
            mk_or f (mk_and a b)
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_or { minor = `r ; pick = sel } -> begin
        match expose f, sel with
        | Or (a, f), `l ->
            mk_or (mk_and a b) f
        | Or (f, a), `r ->
            mk_or f (mk_and a b)
        | _ -> bad_match ()
      end
    | `l, And (a, f), Asms_imp { minor = `l ; pick = sel } -> begin
        match expose f, sel with
        | Imp (b, f), `l ->
            mk_imp (mk_imp a b) f
        | Imp (f, b), `r ->
            mk_imp f (mk_and a b)
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_imp { minor = `r ; pick = sel } -> begin
        match expose f, sel with
        | Imp (a, f), `l ->
            mk_imp (mk_imp b a) f
        | Imp (f, a), `r ->
            mk_imp f (mk_and a b)
        | _ -> bad_match ()
      end
    | `l, And (a, f), Asms_all { minor = `l } -> begin
        match expose f with
        | Forall (vty, b) ->
            mk_all vty (mk_and (shift 1 a) b)
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_all { minor = `r } -> begin
        match expose f with
        | Forall (vty, a) ->
            mk_all vty (mk_and a (shift 1 b))
        | _ -> bad_match ()
      end
    | `l, And (a, f), Asms_ex { minor = `l } -> begin
        match expose f with
        | Exists (vty, b) ->
            mk_ex vty (mk_and (shift 1 a) b)
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_ex { minor = `r } -> begin
        match expose f with
        | Exists (vty, a) ->
            mk_ex vty (mk_and a (shift 1 b))
        | _ -> bad_match ()
      end
    (* simplification *)
    | `r, Imp (_, f), Simp_imp_true -> begin
        match expose f with
        | Top -> f
        | _ -> bad_match ()
      end
    | _, Imp (f, a), Simp_true_imp side_ when side = side_ -> begin
        match expose f with
        | Top -> a
        | _ -> bad_match ()
      end
    | `r, Imp (f, _), Simp_false_imp -> begin
        match expose f with
        | Bot -> mk_top
        | _ -> bad_match ()
      end
    | `r, And (a, f), Simp_and_true `l
    | `r, And (f, a), Simp_and_true `r -> begin
        match expose f with
        | Top -> a
        | _ -> bad_match ()
      end
    | `r, Or (_, f), Simp_or_true `l
    | `r, Or (f, _), Simp_or_true `r -> begin
        match expose f with
        | Top -> f
        | _ -> bad_match ()
      end
    | `r, Forall (_, f), Simp_all_true -> begin
        match expose f with
        | Top -> f
        | _ -> bad_match ()
      end
    (* structural *)
    | `r, Imp (a, b), Init -> begin
        match expose a, expose b with
        | Atom (App { head = f ; spine = ss }),
          Atom (App { head = g ; spine = ts }) when Term.eq_head f g ->
            compute_spine_congruence (Term.ty_infer fx.tycx f) ss ts
        | _ -> bad_match ()
      end
    | `r, Eq (s, t, _), Congr -> begin
        match s, t with
        | App { head = f ; spine = ss },
          App { head = g ; spine = ts } when Term.eq_head f g ->
            compute_spine_congruence (Term.ty_infer fx.tycx f) ss ts
        | _ -> bad_match ()
      end
    | `r, Imp (a, b), Contract ->
        mk_imp a (mk_imp a b)
    | `l, _, Contract ->
        mk_and fx.data fx.data
    | `r, Imp (_, b), Weaken ->
        b
    | `r, Exists (vty, b), Inst wtx ->
        Term.ty_check fx.tycx wtx.data vty.ty ;
        Term.do_app (Abs {var = vty.var ; body = b}) [wtx.data]
    | _ -> bad_match ()
  in
  { goal with data = replace_at goal.data rule.path c }

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

let pp_path_as_lean4 out path =
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

let pp_rule_name_as_lean4 out rn =
  match rn with
  | Inst tx ->
      Format.fprintf out "inst (%a)"
        Form4_pp.LeanPP.pp_termx tx
  | _ ->
      pp_rule_name out rn

let pp_deriv_as_lean4 out deriv =
  Format.fprintf out "section Example@." ;
  Form4_pp.LeanPP.pp_sigma out ;
  Format.fprintf out "example (_ : %a) : %a := by@."
    Form4_pp.LeanPP.pp deriv.top
    Form4_pp.LeanPP.pp deriv.bottom ;
  List.iter begin fun (prem, rule, _) ->
    Format.fprintf out "  within %a use %a@."
      pp_path_as_lean4 rule.path
      pp_rule_name_as_lean4 rule.name ;
    Format.fprintf out "  /- @[%a@] -/@." Form4_pp.LeanPP.pp prem ;
  end @@ List.rev deriv.middle ;
  Format.fprintf out "  rename_i u ; exact u@." ;
  Format.fprintf out "end Example@."
