(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util
open! Types
open! T

type 'a incx = {
  tycx : tycx ;
  data : 'a ;
 }

let (@>) th cx = { cx with data = th }

type form = term
type formx = form incx

(******************************************************************************)
(* formula views *)

type fskel =
  | Atom of term
  | Eq of term * term * ty
  | And of form * form
  | Top
  | Or of form * form
  | Bot
  | Imp of form * form
  | Forall of ident * ty * form
  | Exists of ident * ty * form
  | Pos_int of form * form
  | Neg_int of form * form

let expose (form : form) =
  match form with
  | App { head = Const (k, _) ; spine = [] } when k = k_top ->
      Top
  | App { head = Const (k, _) ; spine = [] } when k = k_bot ->
      Bot
  | App { head = Const (k, _) ; spine = [fa ; fb] } when k = k_and ->
      And (fa, fb)
  | App { head = Const (k, _) ; spine = [fa ; fb] } when k = k_or ->
      Or (fa, fb)
  | App { head = Const (k, _) ; spine = [fa ; fb] } when k = k_imp ->
      Imp (fa, fb)
  | App { head = Const (k, Arrow (ty, _)) ; spine = [t1 ; t2] } when k = k_eq ->
      Eq (t1, t2, ty)
  | App { head = Const (k, _) ; spine = [fa ; fb] } when k = k_neg_int ->
      Neg_int (fa, fb)
  | App { head = Const (k, _) ; spine = [fa ; fb] } when k = k_pos_int ->
      Pos_int (fa, fb)
  | App { head = Const (k, Arrow (Arrow (ty, _), _)) ;
         spine = [Abs { var ; body }] } when k = k_all ->
      Forall (var, ty, body)
  | App { head = Const (k, Arrow (Arrow (ty, _), _)) ;
         spine = [Abs { var ; body }] } when k = k_ex ->
      Exists (var, ty, body)
  | _ ->
      Atom form

let ty_ooo = Arrow (ty_o, Arrow (ty_o, ty_o))

let hide fsk =
  match fsk with
  | Atom f -> f
  | Eq (t1, t2, ty) ->
      App { head = Const (k_eq, Arrow (ty, Arrow (ty, ty_o))) ;
           spine = [t1 ; t2] }
  | And (fa, fb) ->
      App { head = Const (k_and, ty_ooo) ; spine = [fa ; fb] }
  | Top -> App { head = Const (k_top, ty_o) ; spine = [] }
  | Neg_int (fa, fb) ->
      App { head = Const (k_neg_int, ty_ooo) ; spine = [fa ; fb] }
  | Or (fa, fb) ->
      App { head = Const (k_or, ty_ooo) ; spine = [fa ; fb] }
  | Bot -> App { head = Const (k_bot, ty_o) ; spine = [] }
  | Imp (fa, fb) ->
      App { head = Const (k_imp, ty_ooo) ; spine = [fa ; fb] }
  | Pos_int (fa, fb) ->
      App { head = Const (k_pos_int, ty_ooo) ; spine = [fa ; fb] }
  | Forall (var, ty, body) ->
      App { head = Const (k_all, Arrow (Arrow (ty, ty_o), ty_o)) ;
           spine = [Abs { var ; body }] }
  | Exists (var, ty, body) ->
      App { head = Const (k_ex, Arrow (Arrow (ty, ty_o), ty_o)) ;
           spine = [Abs { var ; body }] }

(******************************************************************************)
(* paths *)

type dir = [`l | `r | `i of ident]
type path = dir list

type side = [`l | `r]

let flip (p : side) =
  match p with `l -> `r | `r -> `l

exception Bad_direction of { tycx : tycx option ; form : form ; dir : dir }

let rec get_at ?(side = `r) tycx form (path : path) k =
  match path with
  | [] -> k tycx form side
  | dir :: path -> begin
      match expose form, dir with
      | And (form, _), `l
      | Or (form, _), `l ->
          get_at ~side tycx form path k
      | Imp (form, _), `l ->
          get_at ~side:(flip side) tycx form path k
      | And (_, form), `r
      | Or (_, form), `r
      | Imp (_, form), `r ->
          get_at ~side tycx form path k
      | Forall (_, ty, form), `i x
      | Exists (_, ty, form), `i x ->
          get_at ~side ({ var = x ; ty : ty } :: tycx) form path k
      | _ ->
          raise @@ Bad_direction { tycx = Some tycx ; form ; dir }
    end

let formx_at ?side (formx : formx) path : formx * side =
  get_at ?side formx.tycx formx.data path (fun tycx form side -> ({ tycx ; data = form }, side))

let side_at ?side tycx form path =
  get_at ?side tycx form path (fun _ _ side -> side)

let rec replace_at (src : form) (path : path) (repl : form) : form =
  match path with
  | [] -> repl
  | dir :: path -> begin
      match expose src, dir with
      | And (a, b), `l -> And (replace_at a path repl, b)
      | And (a, b), `r -> And (a, replace_at b path repl)
      | Or (a, b), `l -> Or (replace_at a path repl, b)
      | Or (a, b), `r -> Or (a, replace_at b path repl)
      | Imp (a, b), `l -> Imp (replace_at a path repl, b)
      | Imp (a, b), `r -> Imp (a, replace_at b path repl)
      | Forall (_, ty, a), `i x ->
          Forall (x, ty, replace_at a path repl)
      | Exists (_, ty, a), `i x ->
          Exists (x, ty, replace_at a path repl)
      | _ ->
          raise @@ Bad_direction { tycx = None ; form = src ; dir }
    end |> hide

(******************************************************************************)
(* Direct Manipulation Rules *)

type dmanip_rule =
  | Pristine
  | Point_form of path
  | Point_term of path
  | Link_form of { parent : path ;
                   src    : path ;
                   dest   : path ;
                   side   : side }
  | Link_eq   of { parent : path ;
                   src : path ;
                   dest : path ;
                   side : side }
  | Contract  of { where : path }
  | Weaken    of { where : path }

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

exception Bad_spines of {ty : ty ; ss : spine ; ts : spine}

let rec compute_spine_congruence (ty : ty) (ss : spine) (ts : spine) : form =
  let ty = ty_norm ty in
  match ty, ss, ts with
  | Arrow (tya, ty), (s :: ss), (t :: tt) -> begin
      match ss, tt with
      | [], [] ->
          Eq (s, t, tya) |> hide
      | _ ->
          And (Eq (s, t, tya) |> hide,
               compute_spine_congruence ty ss tt) |> hide
    end
  | _, [], [] ->
      hide Top
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
            Imp (And (a, b) |> hide, f) |> hide
        | Imp (f, b), `r ->
            Imp (f, Imp (a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_imp_ts -> begin
        match expose f with
        | Imp (f, a) ->
            And (f, Imp (a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `r, Imp (a, f), Goal_ts_and sel -> begin
        match expose f, sel with
        | And (b, f), `l ->
            And (Imp (a, b) |> hide, f) |> hide
        | And (f, b), `r ->
            And (f, Imp (a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_and_ts sel -> begin
        match expose f, sel with
        | And (a, _), `l
        | And (_, a), `r ->
            Imp (a, b) |> hide
        | _ -> bad_match ()
      end
    | `r, Imp (a, f), Goal_ts_or sel -> begin
        match expose f, sel with
        | Or (b, _), `l
        | Or (_, b), `r ->
            Imp (a, b) |> hide
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_or_ts -> begin
        match expose f with
        | Or (a1, a2) ->
            And (Imp (a1, b) |> hide,
                 Imp (a2, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `r, Imp (a, f), Goal_ts_all -> begin
        match expose f with
        | Forall (x, ty, b) ->
            Forall (x, ty, Imp (shift 1 a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_all_ts -> begin
        match expose f with
        | Forall (x, ty, a) ->
            Exists (x, ty, Imp (a, shift 1 b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `r, Imp (a, f), Goal_ts_ex -> begin
        match expose f with
        | Exists (x, ty, b) ->
            Exists (x, ty, Imp (shift 1 a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_ex_ts -> begin
        match expose f with
        | Exists (x, ty, a) ->
            Forall (x, ty, Imp (a, shift 1 b) |> hide) |> hide
        | _ -> bad_match ()
      end
    (* assumptions *)
    | `l, And (a, f), Asms_and { minor = `l ; pick = sel } -> begin
        match expose f, sel with
        | And (b, _), `l
        | And (_, b), `r ->
            And (a, b) |> hide
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_and { minor = `r ; pick = sel } -> begin
        match expose f, sel with
        | And (a, _), `l
        | And (_, a), `r ->
            And (a, b) |> hide
        | _ -> bad_match ()
      end
    | `l, And (a, f), Asms_or { minor = `l ; pick = sel } -> begin
        match expose f, sel with
        | Or (b, f), `l ->
            Or (And (a, b) |> hide, f) |> hide
        | Or (f, b), `r ->
            Or (f, And (a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_or { minor = `r ; pick = sel } -> begin
        match expose f, sel with
        | Or (a, f), `l ->
            Or (And (a, b) |> hide, f) |> hide
        | Or (f, a), `r ->
            Or (f, And (a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `l, And (a, f), Asms_imp { minor = `l ; pick = sel } -> begin
        match expose f, sel with
        | Imp (b, f), `l ->
            Imp (Imp (a, b) |> hide, f) |> hide
        | Imp (f, b), `r ->
            Imp (f, And (a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_imp { minor = `r ; pick = sel } -> begin
        match expose f, sel with
        | Imp (a, f), `l ->
            Imp (Imp (b, a) |> hide, f) |> hide
        | Imp (f, a), `r ->
            Imp (f, And (a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `l, And (a, f), Asms_all { minor = `l } -> begin
        match expose f with
        | Forall (x, ty, b) ->
            Forall (x, ty, And (shift 1 a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_all { minor = `r } -> begin
        match expose f with
        | Forall (x, ty, a) ->
            Forall (x, ty, And (a, shift 1 b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `l, And (a, f), Asms_ex { minor = `l } -> begin
        match expose f with
        | Exists (x, ty, b) ->
            Exists (x, ty, And (shift 1 a, b) |> hide) |> hide
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_ex { minor = `r } -> begin
        match expose f with
        | Exists (x, ty, a) ->
            Exists (x, ty, And (a, shift 1 b) |> hide) |> hide
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
        | Bot -> hide Top
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
    | `r, Forall (_, _, f), Simp_all_true -> begin
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
        Imp (a, Imp (a, b) |> hide) |> hide
    | `l, _, Contract ->
        And (fx.data, fx.data) |> hide
    | `r, Imp (_, b), Weaken ->
        b
    | `r, Exists (x, ty, b), Inst wt ->
        Term.ty_check fx.tycx wt ty ;
        Term.do_app (Abs {var = x ; body = b}) [wt]
    | _ -> bad_match ()
  in
  { goal with data = replace_at goal.data rule.path c }
