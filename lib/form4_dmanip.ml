(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util
open! Types
open! T
open! Form4

(******************************************************************************)
(* Direct Manipulation Rules *)

type concl = {
  cpath : path ;                (* REVERSED path to fx *)
  side : side ;                 (* which side is fx *)
  fx : formx ;                  (* scrutinee *)
  lpath : path ;                (* where to go in left subformula *)
  rpath : path ;                (* where to go in right subformula *)
  link_dir : side ;             (* `r : l->r, `l : r->l *)
}

type rule_result =
  | Done
  | Continue of concl

exception Inapplicable
let abort_if cond : unit = if cond then raise Inapplicable
let abort_unless cond : unit = abort_if (not cond)
let abort () = raise Inapplicable

let try_goal_init ~emit concl =
  abort_unless (concl.side = `r) ;
  abort_unless (concl.lpath = [`l]) ;
  abort_unless (concl.rpath = [`r]) ;
  match expose concl.fx.data with
  | Imp (App {head = Const (a1, _) ; spine = _},
         App {head = Const (a2, _) ; spine = _})
      when a1 = a2 && not (IdMap.mem a1 global_sig) ->
        emit { name = Init ; path = List.rev concl.cpath } ;
        Done
  | _ -> abort ()

let try_goal_ts_and ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, concl.rpath with
  | Imp (a, f), (`r :: rpath) -> begin
      match expose f, rpath with
      | And (b, f), (`l :: rpath) ->
          emit { name = Goal_ts_and `l ; path = List.rev concl.cpath } ;
          let fx = mk_and (mk_imp a b) f |@ concl.fx in
          let cpath = `l :: concl.cpath in
          let rpath = `r :: rpath in
          Continue { concl with fx ; cpath ; rpath }
      | And (f, b), (`r :: rpath) ->
          emit { name = Goal_ts_and `r ; path = List.rev concl.cpath } ;
          let fx = mk_and f (mk_imp a b) |@ concl.fx in
          let cpath = `r :: concl.cpath in
          let rpath = `r :: rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_and_ts ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, concl.lpath with
  | Imp (f, b), (`l :: lpath) -> begin
      match expose f, lpath with
      | And (a, _), (`l as dir :: lpath)
      | And (_, a), (`r as dir :: lpath) ->
          emit { name = Goal_and_ts dir ; path = List.rev concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let cpath = `l :: concl.cpath in
          let lpath = `l :: lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_ts_or ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, concl.rpath with
  | Imp (a, f), (`r :: rpath) -> begin
      match expose f, rpath with
      | Or (b, _), (`l as dir :: rpath)
      | Or (_, b), (`r as dir :: rpath) ->
          emit { name = Goal_ts_or dir ; path = List.rev concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let cpath = `r :: concl.cpath in
          let rpath = `r :: rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_or_ts ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, concl.lpath with
  | Imp (f, b), (`l :: lpath) -> begin
      match expose f, lpath with
      | Or (a, _), (`l as dir :: lpath)
      | Or (_, a), (`r as dir :: lpath) ->
          emit { name = Goal_or_ts ; path = List.rev concl.cpath } ;
          let fx = (mk_imp a b) |@ concl.fx in
          let cpath = dir :: concl.cpath in
          let lpath = `l :: lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_ts_imp ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, concl.rpath with
  | Imp (a, f), (`r :: rpath) -> begin
      match expose f, rpath with
      | Imp (b, _), (`l :: rpath) ->
          emit { name = Goal_ts_imp `l ; path = List.rev concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let side = flip concl.side in
          let cpath = `l :: concl.cpath in
          let rpath = `r :: rpath in
          Continue { concl with fx ; side ; cpath ; rpath }
      | Imp (_, b), (`r :: rpath) ->
          emit { name = Goal_ts_imp `r ; path = List.rev concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let cpath = `r :: concl.cpath in
          let rpath = `r :: rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_imp_ts ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, concl.lpath with
  | Imp (f, b), (`l :: lpath) -> begin
      match expose f, lpath with
      | Imp (_, a), (`r :: lpath) ->
          emit { name = Goal_imp_ts ; path = List.rev concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let cpath = `r :: concl.cpath in
          let lpath = `l :: lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let is_forall = function
  | Forall _ -> true
  | _ -> false

let is_exists = function
  | Exists _ -> true
  | _ -> false

let try_goal_ts_allex ~qsel ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, concl.rpath with
  | Imp (a, f), (`r :: rpath) -> begin
      match expose f, rpath with
      | (Forall (var, ty, b) as fexp), (`d :: rpath)
      | (Exists (var, ty, b) as fexp), (`d :: rpath)
        when qsel fexp ->
          with_var concl.fx.tycx { var ; ty } begin fun tycx ->
            let name = if is_forall fexp then Goal_ts_all else Goal_ts_ex in
            emit { name ; path = List.rev concl.cpath } ;
            let fx = { data = mk_imp (shift 1 a) b ; tycx } in
            let cpath = `d :: concl.cpath in
            let rpath = `r :: rpath in
            Continue { concl with fx ; cpath ; rpath }
          end
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_allex_ts ~qsel ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, concl.lpath with
  | Imp (f, b), (`l :: lpath) -> begin
      match expose f, lpath with
      | (Forall (var, ty, a) as fexp), (`d :: lpath)
      | (Exists (var, ty, a) as fexp), (`d :: lpath)
        when qsel fexp ->
          with_var concl.fx.tycx { var ; ty } begin fun tycx ->
            let name = if is_forall fexp then Goal_all_ts else Goal_ex_ts in
            emit { name ; path = List.rev concl.cpath } ;
            let fx = { data = mk_imp a (shift 1 b) ; tycx } in
            let cpath = `d :: concl.cpath in
            let lpath = `l :: lpath in
            Continue { concl with fx ; cpath ; lpath }
          end
      | _ -> abort ()
    end
  | _ -> abort ()

let can_descend (dir : side) concl =
  match dir, concl.link_dir with
  | `l, `l ->
      (* descend left on r2l links unless already at dest *)
      concl.lpath <> [`l]
  | `l, `r ->
      (* descend left on l2r links only if already at dest *)
      concl.rpath = [`r]
  | `r, `l ->
      (* descend right on r2l links only if already at dest *)
      concl.lpath = [`l]
  | `r, `r ->
      (* descend right on l2r links unless already at dest *)
      concl.rpath <> [`r]

let try_asms_and ~emit concl =
  abort_unless (concl.side = `l) ;
  match expose concl.fx.data, concl.lpath, concl.rpath with
  | And (f, b), (`l :: lpath), _
    when can_descend `l concl -> begin
      match expose f, lpath with
      | And (a, _), (`l as dir :: lpath)
      | And (_, a), (`r as dir :: lpath) ->
          emit { name = Asms_and { minor = `r ; pick = dir } ;
                 path = List.rev concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          (* cpath unchanged *)
          let lpath = `l :: lpath in
          Continue { concl with fx ; lpath }
      | _ -> abort ()
    end
  | And (a, f), _, (`r :: rpath)
    when can_descend `r concl -> begin
      match expose f, rpath with
      | And (b, _), (`l as dir :: rpath)
      | And (_, b), (`r as dir :: rpath) ->
          emit { name = Asms_and { minor = `l ; pick = dir } ;
                 path = List.rev concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          (* cpath unchanged *)
          let rpath = `r :: rpath in
          Continue { concl with fx ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_asms_or ~emit concl =
  abort_unless (concl.side = `l) ;
  match expose concl.fx.data, concl.lpath, concl.rpath with
  | And (f, b), (`l :: lpath), _
    when can_descend `l concl -> begin
      match expose f, lpath with
      | Or (a, _), (`l as dir :: lpath)
      | Or (_, a), (`r as dir :: lpath) ->
          emit { name = Asms_or { minor = `r ; pick = dir } ;
                 path = List.rev concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let cpath = dir :: concl.cpath in
          let lpath = `l :: lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | And (a, f), _, (`r :: rpath)
    when can_descend `r concl -> begin
      match expose f, rpath with
      | Or (b, _), (`l as dir :: rpath)
      | Or (_, b), (`r as dir :: rpath) ->
          emit { name = Asms_or { minor = `l ; pick = dir } ;
                 path = List.rev concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let cpath = dir :: concl.cpath in
          let rpath = `r :: rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_asms_imp ~emit concl =
  abort_unless (concl.side = `l) ;
  match expose concl.fx.data, concl.lpath, concl.rpath with
  | And (f, b), (`l :: lpath), _
    when can_descend `l concl -> begin
      match expose f, lpath with
      | Imp (a, _), (`l :: lpath) ->
          emit { name = Asms_imp { minor = `r ; pick = `l } ;
                 path = List.rev concl.cpath } ;
          let fx = mk_imp b a |@ concl.fx in
          let side = flip concl.side in
          let cpath = `l :: concl.cpath in
          let rpath = `r :: lpath in
          let lpath = `l :: List.tl concl.rpath in
          Continue { concl with fx ; side ; cpath ; lpath ; rpath }
      | Imp (_, a), (`r :: lpath) ->
          emit { name = Asms_imp { minor = `r ; pick = `r } ;
                 path = List.rev concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let cpath = `r :: concl.cpath in
          let lpath = `l :: lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | And (a, f), _, (`r :: rpath)
    when can_descend `r concl -> begin
      match expose f, rpath with
      | Imp (b, _), (`l :: rpath) ->
          emit { name = Asms_imp { minor = `l ; pick = `l } ;
                 path = List.rev concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let side = flip concl.side in
          let cpath = `l :: concl.cpath in
          let rpath = `r :: rpath in
          Continue { concl with fx ; side ; cpath ; rpath }
      | Imp (_, b), (`r :: rpath) ->
          emit { name = Asms_imp { minor = `l ; pick = `r } ;
                 path = List.rev concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let cpath = `r :: concl.cpath in
          let rpath = `r :: rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_asms_allex ~emit concl =
  abort_unless (concl.side = `l) ;
  match expose concl.fx.data, concl.lpath, concl.rpath with
  | And (f, b), (`l :: lpath), _
    when can_descend `l concl -> begin
      match expose f, lpath with
      | (Forall (var, ty, a) as fexp), (`d :: lpath)
      | (Exists (var, ty, a) as fexp), (`d :: lpath) ->
          with_var concl.fx.tycx { var ; ty } begin fun tycx ->
            let name = match fexp with
              | Forall _ -> Asms_all { minor = `r }
              | _ -> Asms_ex { minor = `r }
            in
            emit { name ; path = List.rev concl.cpath } ;
            let fx = { data = mk_and a (shift 1 b) ; tycx } in
            let cpath = `d :: concl.cpath in
            let lpath = `l :: lpath in
            Continue { concl with fx ; cpath ; lpath }
          end
      | _ -> abort ()
    end
  | And (a, f), _, (`r :: rpath)
    when can_descend `r concl -> begin
      match expose f, rpath with
      | (Forall (var, ty, b) as fexp), (`d :: rpath)
      | (Exists (var, ty, b) as fexp), (`d :: rpath) ->
          with_var concl.fx.tycx { var ; ty } begin fun tycx ->
            let name = match fexp with
              | Forall _ -> Asms_all { minor = `l }
              | _ -> Asms_ex { minor = `l }
            in
            emit { name ; path = List.rev concl.cpath } ;
            let fx = { data = mk_and (shift 1 a) b ; tycx } in
            let cpath = `d :: concl.cpath in
            let rpath = `r :: rpath in
            Continue { concl with fx ; cpath ; rpath }
          end
      | _ -> abort ()
    end
  | _ -> abort ()

let all_rules = [
  try_goal_init ;
  (* async *)
  try_goal_ts_and ;
  try_goal_or_ts ;
  try_goal_ts_imp ;
  try_goal_ts_allex ~qsel:is_forall ;
  try_goal_allex_ts ~qsel:is_exists ;
  (* sync *)
  try_goal_and_ts ;
  try_goal_ts_or ;
  try_goal_imp_ts ;
  try_goal_ts_allex ~qsel:is_exists ;
  try_goal_allex_ts ~qsel:is_forall ;
  (* forward *)
  try_asms_and ;
  try_asms_or ;
  try_asms_imp ;
  try_asms_allex ;
]

let rec spin_rules ~emit concl =
  let rec try_all concl rules =
    match rules with
    | [] ->
        Format.eprintf "spin_rules: stuck on: @[%a@]@. lpath = %a@. rpath = %a@.%!"
          (Term.pp_term ~cx:concl.fx.tycx) concl.fx.data
          pp_path concl.lpath
          pp_path concl.rpath ;
        failwith "stuck"
    | rule :: rules -> begin
        match rule ~emit concl with
        | Done -> ()
        | Continue concl -> spin_rules ~emit concl
        | exception Inapplicable -> try_all concl rules
      end
  in
  try_all concl all_rules

type dmanip_rule =
  | Pristine
  | Point_form of path
  | Point_term of path
  | Link_form of { src    : path ;
                   dest   : path }
  | Link_eq   of { src : path ;
                   dest : path ;
                   side : side }
  | Contract  of path
  | Weaken    of path

exception Bad_link of { goal : formx ; mrule : dmanip_rule }

let compute_derivation ~emit goal mrule =
  let fail () = raise @@ Bad_link { goal ; mrule } in
  let rec analyze_link src dest =
    match src, dest with
    | (ds :: src), (dd :: dest) when ds = dd ->
        let (cpath, lpath, rpath, ldir) = analyze_link src dest in
        (ds :: cpath, lpath, rpath, ldir)
    | (ds :: _), (dd :: _) ->
        if ds = `l && dd = `r then
          ([], src, dest, `r)
        else if ds = `r && dd = `l then
          ([], dest, src, `l)
        else fail ()
    | _ -> fail ()
  in
  match mrule with
  | Pristine
  | Point_form _
  | Point_term _ ->
      ()
  | Contract path ->
      emit { name = Contract ; path }
  | Weaken path ->
      emit { name = Weaken ; path }
  | Link_eq _ ->
      failwith "unfinished"
  | Link_form { src ; dest } -> begin
      let (cpath, lpath, rpath, link_dir) = analyze_link src dest in
      let (fx, side) = formx_at goal (List.rev cpath) in
      let concl = { cpath ; fx ; side ; lpath ; rpath ; link_dir } in
      spin_rules ~emit concl
    end

(******************************************************************************)
(* Testing *)

module Test = struct
  include Form4.Test

  let scomb_d () =
    let deriv = ref [] in
    let emit rule = deriv := rule :: !deriv in
    compute_derivation ~emit scomb @@ Link_form {
      src = [`l ; `r ; `r] ;
      dest = [`r ; `r ; `r] ;
    } ;
    compute_forms_simp scomb (List.rev !deriv)

  let qexch_d () =
    let deriv = ref [] in
    let emit rule = deriv := rule :: !deriv in
    compute_derivation ~emit qexch @@ Link_form {
      src = [`l ; `d ; `d] ;
      dest = [`r ; `d ; `d] ;
    } ;
    compute_forms_simp qexch (List.rev !deriv)
end
