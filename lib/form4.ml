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
  | App { head = Const (k, Arrow (Arrow (ty, _), _)) ;
         spine = [Abs { var ; body }] } when k = k_all ->
      Forall (var, ty, body)
  | App { head = Const (k, Arrow (Arrow (ty, _), _)) ;
         spine = [Abs { var ; body }] } when k = k_ex ->
      Exists (var, ty, body)
  | _ ->
      Atom form

let ty_ooo = Arrow (ty_o, Arrow (ty_o, ty_o))

let mk_eq t1 t2 ty =
  App { head = Const (k_eq, Arrow (ty, Arrow (ty, ty_o))) ;
        spine = [t1 ; t2] }
let mk_and fa fb =
  App { head = Const (k_and, ty_ooo) ; spine = [fa ; fb] }
let mk_top = App { head = Const (k_top, ty_o) ; spine = [] }
let mk_or fa fb =
  App { head = Const (k_or, ty_ooo) ; spine = [fa ; fb] }
let mk_bot = App { head = Const (k_bot, ty_o) ; spine = [] }
let mk_imp fa fb =
  App { head = Const (k_imp, ty_ooo) ; spine = [fa ; fb] }
let mk_all var ty body =
  App { head = Const (k_all, Arrow (Arrow (ty, ty_o), ty_o)) ;
        spine = [Abs { var ; body }] }
let mk_ex var ty body =
  App { head = Const (k_ex, Arrow (Arrow (ty, ty_o), ty_o)) ;
        spine = [Abs { var ; body }] }

(* let hide__ fsk = *)
(*   match fsk with *)
(*   | Atom f -> f *)
(*   | Eq (t1, t2, ty) -> mk_eq t1 t2 ty *)
(*   | And (fa, fb) -> mk_and fa fb *)
(*   | Top -> mk_top *)
(*   | Or (fa, fb) -> mk_or fa fb *)
(*   | Bot -> mk_bot *)
(*   | Imp (fa, fb) -> mk_imp fa fb *)
(*   | Forall (var, ty, body) -> mk_all var ty body *)
(*   | Exists (var, ty, body) -> mk_ex var ty body *)

(******************************************************************************)
(* paths *)

type dir = [`l | `r | `i of ident | `d]
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
      | Forall (x, ty, form), `d
      | Exists (_, ty, form), `i x
      | Exists (x, ty, form), `d ->
          with_var tycx {var = x ; ty} begin fun tycx ->
            get_at ~side tycx form path k
          end
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
      | And (a, b), `l -> mk_and (replace_at a path repl) b
      | And (a, b), `r -> mk_and a (replace_at b path repl)
      | Or (a, b), `l -> mk_or (replace_at a path repl) b
      | Or (a, b), `r -> mk_or a (replace_at b path repl)
      | Imp (a, b), `l -> mk_imp (replace_at a path repl) b
      | Imp (a, b), `r -> mk_imp a (replace_at b path repl)
      | Forall (_, ty, a), `i x
      | Forall (x, ty, a), `d ->
          mk_all x ty (replace_at a path repl)
      | Exists (_, ty, a), `i x
      | Exists (x, ty, a), `d ->
          mk_ex x ty (replace_at a path repl)
      | _ ->
          raise @@ Bad_direction { tycx = None ; form = src ; dir }
    end

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

let rec pp_path out (path : path) =
  match path with
  | [] -> ()
  | [`l] -> Format.fprintf out "l"
  | [`r] -> Format.fprintf out "r"
  | [`i x] -> Format.fprintf out "i %s" x
  | [`d] -> Format.fprintf out "d"
  | dir :: (_ :: _ as path) ->
      Format.fprintf out "%a, %a" pp_path [dir] pp_path path

let pp_rule out goalx rule =
  let (fx, _) = formx_at goalx rule.path in
  Format.fprintf out "@[%a :: %a@]"
    pp_path rule.path
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
        | Forall (x, ty, b) ->
            mk_all x ty (mk_imp (shift 1 a) b)
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_all_ts -> begin
        match expose f with
        | Forall (x, ty, a) ->
            mk_ex x ty (mk_imp a (shift 1 b))
        | _ -> bad_match ()
      end
    | `r, Imp (a, f), Goal_ts_ex -> begin
        match expose f with
        | Exists (x, ty, b) ->
            mk_ex x ty (mk_imp (shift 1 a) b)
        | _ -> bad_match ()
      end
    | `r, Imp (f, b), Goal_ex_ts -> begin
        match expose f with
        | Exists (x, ty, a) ->
            mk_all x ty (mk_imp a (shift 1 b))
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
        | Forall (x, ty, b) ->
            mk_all x ty (mk_and (shift 1 a) b)
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_all { minor = `r } -> begin
        match expose f with
        | Forall (x, ty, a) ->
            mk_all x ty (mk_and a (shift 1 b))
        | _ -> bad_match ()
      end
    | `l, And (a, f), Asms_ex { minor = `l } -> begin
        match expose f with
        | Exists (x, ty, b) ->
            mk_ex x ty (mk_and (shift 1 a) b)
        | _ -> bad_match ()
      end
    | `l, And (f, b), Asms_ex { minor = `r } -> begin
        match expose f with
        | Exists (x, ty, a) ->
            mk_ex x ty (mk_and a (shift 1 b))
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
        mk_imp a (mk_imp a b)
    | `l, _, Contract ->
        mk_and fx.data fx.data
    | `r, Imp (_, b), Weaken ->
        b
    | `r, Exists (x, ty, b), Inst wt ->
        Term.ty_check fx.tycx wt ty ;
        Term.do_app (Abs {var = x ; body = b}) [wt]
    | _ -> bad_match ()
  in
  { goal with data = replace_at goal.data rule.path c }

(******************************************************************************)
(* Formula Simplification *)

let ( |@ ) f th = { th with data = f }

let rec recursive_simplify (fx : formx) (rpath : path) (side : side) emit =
  match expose fx.data with
  | Eq (s, t, _) when side = `r -> begin
      match s, t with
      | App { head = f ; spine = ss },
        App { head = g ; spine = ts } when Term.eq_head f g ->
          emit { name = Congr ; path = List.rev rpath } ;
          let res = compute_spine_congruence (Term.ty_infer fx.tycx f) ss ts in
          recursive_simplify (res |@ fx) rpath side emit
      | _ -> fx
    end
  | And (a, b) -> begin
      let a = recursive_simplify (a |@ fx) (`l :: rpath) side emit in
      let b = recursive_simplify (b |@ fx) (`r :: rpath) side emit in
      match side with
      | `l -> mk_and a.data b.data |@ fx
      | `r -> begin
          match expose a.data, expose b.data with
          | _, Top ->
              emit { name = Simp_and_true `l ; path = List.rev rpath } ; a
          | Top, _ ->
              emit { name = Simp_and_true `r ; path = List.rev rpath } ; b
          | _ ->
              mk_and a.data b.data |@ fx
        end
    end
  | Or (a, b) -> begin
      let a = recursive_simplify (a |@ fx) (`l :: rpath) side emit in
      let b = recursive_simplify (b |@ fx) (`r :: rpath) side emit in
      match side with
      | `l -> mk_or a.data b.data |@ fx
      | `r -> begin
          match expose a.data, expose b.data with
          | _, Top ->
              emit { name = Simp_or_true `l ; path = List.rev rpath } ; b
          | Top, _ ->
              emit { name = Simp_or_true `r ; path = List.rev rpath } ; a
          | _ ->
              mk_or a.data b.data |@ fx
        end
    end
  | Imp (a, b) -> begin
      let a = recursive_simplify (a |@ fx) (`l :: rpath) (flip side) emit in
      let b = recursive_simplify (b |@ fx) (`r :: rpath) side emit in
      match side with
      | `l -> mk_imp a.data b.data |@ fx
      | `r -> begin
          match expose a.data, expose b.data with
          | _, Top ->
              emit { name = Simp_imp_true ; path = List.rev rpath } ; b
          | Bot, _ ->
              emit { name = Simp_imp_true ; path = List.rev rpath } ;
              mk_top |@ fx
          | _ ->
              mk_imp a.data b.data |@ fx
        end
    end
  | Forall (x, ty, b) ->
      with_var ~fresh:true fx.tycx { var = x ; ty } begin fun tycx ->
        let b = { tycx ; data = b } in
        let b = recursive_simplify b (`d :: rpath) side emit in
        match side with
        | `l -> mk_all x ty b.data |@ fx
        | `r -> begin
            match expose b.data with
            | Top ->
                emit { name = Simp_all_true ; path = List.rev rpath } ; b
            | _ ->
                mk_all x ty b.data |@ fx
          end
      end
  | Exists (x, ty, b) ->
      with_var ~fresh:true fx.tycx { var = x ; ty } begin fun tycx ->
        let b = { tycx ; data = b } in
        let b = recursive_simplify b (`d :: rpath) side emit in
        mk_ex x ty b.data |@ fx
      end
  | Atom _ | Eq _ | Top | Bot -> fx

(******************************************************************************)
(* Testing *)

module Test = struct

  let a = App { head = Const ("a", ty_o) ; spine = [] }
  let b = App { head = Const ("b", ty_o) ; spine = [] }
  let c = App { head = Const ("c", ty_o) ; spine = [] }

  let formx_to_string fx = Term.term_to_string ~cx:fx.tycx fx.data

  let rec compute_forms ?(hist = []) goal deriv =
    match deriv with
    | [] -> formx_to_string goal :: hist
    | rule :: deriv ->
        let prem = compute_premise goal rule in
        compute_forms prem deriv
          ~hist:(rule_to_string goal rule :: formx_to_string goal :: hist)

  let rec compute_forms_simp ?(hist = []) goal deriv =
    match deriv with
    | [] -> formx_to_string goal :: hist
    | rule :: deriv ->
        let prem = ref @@ compute_premise goal rule in
        let hist = ref @@ rule_to_string goal rule :: formx_to_string goal :: hist in
        let emit rule =
          hist := formx_to_string !prem :: !hist ;
          hist := rule_to_string !prem rule :: !hist ;
          prem := compute_premise !prem rule
        in
        let simp_prem = recursive_simplify !prem [] `r emit in
        compute_forms_simp simp_prem deriv ~hist:!hist

 let kcomb = { tycx = empty ; data = mk_imp a (mk_imp b a) }

  let t1 () =
    let kderiv = [
      { name = Goal_ts_imp `r ; path = []   } ;
      { name = Init           ; path = [`r] } ;
    ] in
    compute_forms_simp kcomb kderiv

  let scomb = { tycx = empty ;
                data = mk_imp (mk_imp a (mk_imp b c)) (mk_imp (mk_imp a b) (mk_imp a c)) }

  let t2 () =
    let sderiv = [
      { name = Contract ; path = [`r ; `r] } ;
      { name = Goal_ts_imp `l ; path = [`r] } ;
      { name = Asms_imp { minor = `r ; pick = `l } ; path = [`r ; `l] } ;
      { name = Init ; path = [`r ; `l ; `l] } ;
      { name = Goal_ts_imp `r ; path = [] } ;
      { name = Goal_ts_imp `r ; path = [`r] } ;
      { name = Goal_imp_ts ; path = [`r ; `r] } ;
      { name = Goal_imp_ts ; path = [`r ; `r ; `r] } ;
      { name = Init ; path = [`r ; `r ; `r ; `r] } ;
      { name = Goal_imp_ts ; path = [] } ;
      { name = Goal_ts_imp `r ; path = [] } ;
      { name = Goal_ts_and `r ; path = [`r] } ;
      { name = Goal_ts_and `l ; path = [] } ;
      { name = Init ; path = [`l] } ;
      { name = Init ; path = [] } ;
    ] in
    compute_forms_simp scomb sderiv

  let r x y = App { head = Const ("r", Arrow (ty_i, Arrow (ty_i, ty_o))) ;
                    spine = [x ; y] }
  let dbx n = App { head = Index n ; spine = [] }

  let qexch = {
    tycx = empty ;
    data = mk_imp
        (mk_ex "x" ty_i
           (mk_all "y" ty_i (r (dbx 1) (dbx 0))))
        (mk_all "y" ty_i
           (mk_ex "x" ty_i (r (dbx 0) (dbx 1)))) }

  let t3 () =
    let deriv = [
      { name = Goal_ts_all ; path = [] } ;
      { name = Goal_ex_ts ; path = [`d] } ;
      { name = Goal_ts_ex ; path = [`d ; `d] } ;
      { name = Goal_all_ts ; path = [`d ; `d ; `d] } ;
      { name = Init ; path = [`d ; `d ; `d ; `d] } ;
      { name = Inst (dbx 0) ; path = [`d ; `d] } ;
      { name = Inst (dbx 1) ; path = [`d ; `d] } ;
    ] in
    compute_forms_simp qexch deriv
end
