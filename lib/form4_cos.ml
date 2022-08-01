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

type cos_rule_name =
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
  | Simp_false_imp
  | Simp_and_true of side
  | Simp_or_true  of side
  | Simp_all_true
  | Init
  | Congr
  | Contract
  | Weaken
  | Inst of term

and cos_rule = {
  name : cos_rule_name ;
  path : path ;
}

let side_to_string (side : side) =
  match side with
  | `l -> "l"
  | `r -> "r"

let pp_rule_name ?(cx = empty) out rn =
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
  | Inst term ->
      Format.fprintf out "inst[@[%a@]]" (Term.pp_term ~cx) term

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

let pp_rule out goalx rule =
  let (fx, _) = formx_at goalx rule.path in
  Format.fprintf out "@[%a%s:: %a@]"
    pp_path rule.path
    (if Q.size rule.path = 0 then "" else " ")
    (pp_rule_name ~cx:fx.tycx) rule.name

let rule_to_string goalx rule =
  let buf = Buffer.create 19 in
  let out = Format.formatter_of_buffer buf in
  pp_rule out goalx rule ;
  Format.pp_print_flush out () ;
  Buffer.contents buf

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

exception Bad_match of {goal : formx ; rule : cos_rule}

let shift n t = Term.(sub_term (Shift n) t) [@@inline]

let compute_premise (goal : formx) (rule : cos_rule) : formx =
  let bad_match () = raise @@ Bad_match {goal ; rule} in
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
    | `r, Exists (vty, b), Inst wt ->
        Term.ty_check fx.tycx wt vty.ty ;
        Term.do_app (Abs {var = vty.var ; body = b}) [wt]
    | _ -> bad_match ()
  in
  { goal with data = replace_at goal.data rule.path c }