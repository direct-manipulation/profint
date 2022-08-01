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
open Form4_cos

(******************************************************************************)
(* Direct Manipulation Rules *)

type concl = {
  cpath : path ;                (* path to fx *)
  side : side ;                 (* which side is fx *)
  fx : formx ;                  (* scrutinee *)
  lpath : path ;                (* where to go in left subformula *)
  rpath : path ;                (* where to go in right subformula *)
  dest_in : side ;              (* `r : l->r, `l : r->l *)
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
  abort_unless (concl.lpath = Q.of_list [`l]) ;
  abort_unless (concl.rpath = Q.of_list [`r]) ;
  match expose concl.fx.data with
  | Imp (App {head = Const (a1, _) ; spine = _},
         App {head = Const (a2, _) ; spine = _})
      when a1 = a2 && not (IdMap.mem a1 global_sig) ->
        emit { name = Init ; path = concl.cpath } ;
        Done
  | _ -> abort ()

let try_goal_ts_and ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, Q.take_front concl.rpath with
  | Imp (a, f), Some (`r, rpath) -> begin
      match expose f, Q.take_front rpath with
      | And (b, f), Some (`l, rpath) ->
          emit { name = Goal_ts_and `l ; path = concl.cpath } ;
          let fx = mk_and (mk_imp a b) f |@ concl.fx in
          let cpath = Q.snoc concl.cpath `l in
          let rpath = Q.cons `r rpath in
          Continue { concl with fx ; cpath ; rpath }
      | And (f, b), Some (`r, rpath) ->
          emit { name = Goal_ts_and `r ; path = concl.cpath } ;
          let fx = mk_and f (mk_imp a b) |@ concl.fx in
          let cpath = Q.snoc concl.cpath `r in
          let rpath = Q.cons `r rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_and_ts ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, Q.take_front concl.lpath with
  | Imp (f, b), Some (`l, lpath) -> begin
      match expose f, Q.take_front lpath with
      | And (a, _), Some (`l as dir, lpath)
      | And (_, a), Some (`r as dir, lpath) ->
          emit { name = Goal_and_ts dir ; path = concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let cpath = Q.snoc concl.cpath `l in
          let lpath = Q.cons `l lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_ts_or ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, Q.take_front concl.rpath with
  | Imp (a, f), Some (`r, rpath) -> begin
      match expose f, Q.take_front rpath with
      | Or (b, _), Some (`l as dir, rpath)
      | Or (_, b), Some (`r as dir, rpath) ->
          emit { name = Goal_ts_or dir ; path = concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let cpath = Q.snoc concl.cpath `r in
          let rpath = Q.cons `r rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_or_ts ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, Q.take_front concl.lpath with
  | Imp (f, b), Some (`l, lpath) -> begin
      match expose f, Q.take_front lpath with
      | Or (a, _), Some (`l as dir, lpath)
      | Or (_, a), Some (`r as dir, lpath) ->
          emit { name = Goal_or_ts ; path = concl.cpath } ;
          let fx = (mk_imp a b) |@ concl.fx in
          let cpath =Q.snoc concl.cpath  dir in
          let lpath = Q.cons `l lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_ts_imp ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, Q.take_front concl.rpath with
  | Imp (a, f), Some (`r, rpath) -> begin
      match expose f, Q.take_front rpath with
      | Imp (b, _), Some (`l, rpath) ->
          emit { name = Goal_ts_imp `l ; path = concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let side = flip concl.side in
          let cpath = Q.snoc concl.cpath `l in
          let rpath = Q.cons `r rpath in
          Continue { concl with fx ; side ; cpath ; rpath }
      | Imp (_, b), Some (`r, rpath) ->
          emit { name = Goal_ts_imp `r ; path = concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let cpath = Q.snoc concl.cpath `r in
          let rpath = Q.cons `r rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_imp_ts ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, Q.take_front concl.lpath with
  | Imp (f, b), Some (`l, lpath) -> begin
      match expose f, Q.take_front lpath with
      | Imp (_, a), Some (`r, lpath) ->
          emit { name = Goal_imp_ts ; path = concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let cpath = Q.snoc concl.cpath `r in
          let lpath = Q.cons `l lpath in
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
  match expose concl.fx.data, Q.take_front concl.rpath with
  | Imp (a, f), Some (`r, rpath) -> begin
      match expose f, Q.take_front rpath with
      | (Forall (vty, b) as fexp), Some (`d, rpath)
      | (Exists (vty, b) as fexp), Some (`d, rpath)
        when qsel fexp ->
          with_var concl.fx.tycx vty begin fun _ tycx ->
            let name = if is_forall fexp then Goal_ts_all else Goal_ts_ex in
            emit { name ; path = concl.cpath } ;
            let fx = { data = mk_imp (shift 1 a) b ; tycx } in
            let cpath = Q.snoc concl.cpath `d in
            let rpath = Q.cons `r rpath in
            Continue { concl with fx ; cpath ; rpath }
          end
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_allex_ts ~qsel ~emit concl =
  abort_unless (concl.side = `r) ;
  match expose concl.fx.data, Q.take_front concl.lpath with
  | Imp (f, b), Some (`l, lpath) -> begin
      match expose f, Q.take_front lpath with
      | (Forall (vty, a) as fexp), Some (`d, lpath)
      | (Exists (vty, a) as fexp), Some (`d, lpath)
        when qsel fexp ->
          with_var concl.fx.tycx vty begin fun _ tycx ->
            let name = if is_forall fexp then Goal_all_ts else Goal_ex_ts in
            emit { name ; path = concl.cpath } ;
            let fx = { data = mk_imp a (shift 1 b) ; tycx } in
            let cpath = Q.snoc concl.cpath `d in
            let lpath = Q.cons `l lpath in
            Continue { concl with fx ; cpath ; lpath }
          end
      | _ -> abort ()
    end
  | _ -> abort ()

let single_l : path = Q.singleton `l
let single_r : path = Q.singleton `r

let can_descend (dir : side) concl =
  match dir, concl.dest_in with
  | `l, `l ->
      (* descend left on r2l links unless already at dest *)
      concl.lpath <> single_l
  | `l, `r ->
      (* descend left on l2r links only if already at dest *)
      concl.rpath = single_r
  | `r, `l ->
      (* descend right on r2l links only if already at dest *)
      concl.lpath = single_l
  | `r, `r ->
      (* descend right on l2r links unless already at dest *)
      concl.rpath <> single_r

let try_asms_and ~emit concl =
  abort_unless (concl.side = `l) ;
  match expose concl.fx.data,
        Q.take_front concl.lpath,
        Q.take_front concl.rpath with
  | And (f, b), Some (`l, lpath), _
    when can_descend `l concl -> begin
      match expose f, Q.take_front lpath with
      | And (a, _), Some (`l as dir, lpath)
      | And (_, a), Some (`r as dir, lpath) ->
          emit { name = Asms_and { minor = `r ; pick = dir } ;
                 path = concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          (* cpath unchanged *)
          let lpath = Q.cons `l lpath in
          Continue { concl with fx ; lpath }
      | _ -> abort ()
    end
  | And (a, f), _, Some (`r, rpath)
    when can_descend `r concl -> begin
      match expose f, Q.take_front rpath with
      | And (b, _), Some (`l as dir, rpath)
      | And (_, b), Some (`r as dir, rpath) ->
          emit { name = Asms_and { minor = `l ; pick = dir } ;
                 path = concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          (* cpath unchanged *)
          let rpath = Q.cons `r rpath in
          Continue { concl with fx ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_asms_or ~emit concl =
  abort_unless (concl.side = `l) ;
  match expose concl.fx.data,
        Q.take_front concl.lpath,
        Q.take_front concl.rpath with
  | And (f, b), Some (`l, lpath), _
    when can_descend `l concl -> begin
      match expose f, Q.take_front lpath with
      | Or (a, _), Some (`l as dir, lpath)
      | Or (_, a), Some (`r as dir, lpath) ->
          emit { name = Asms_or { minor = `r ; pick = dir } ;
                 path = concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let cpath =Q.snoc concl.cpath  dir in
          let lpath = Q.cons `l lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | And (a, f), _, Some (`r, rpath)
    when can_descend `r concl -> begin
      match expose f, Q.take_front rpath with
      | Or (b, _), Some (`l as dir, rpath)
      | Or (_, b), Some (`r as dir, rpath) ->
          emit { name = Asms_or { minor = `l ; pick = dir } ;
                 path = concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let cpath =Q.snoc concl.cpath  dir in
          let rpath = Q.cons `r rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_asms_imp ~emit concl =
  abort_unless (concl.side = `l) ;
  match expose concl.fx.data,
        Q.take_front concl.lpath,
        Q.take_front concl.rpath with
  | And (f, b), Some (`l, lpath), _
    when can_descend `l concl -> begin
      match expose f, Q.take_front lpath with
      | Imp (a, _), Some (`l, lpath) ->
          emit { name = Asms_imp { minor = `r ; pick = `l } ;
                 path = concl.cpath } ;
          let fx = mk_imp b a |@ concl.fx in
          let side = flip concl.side in
          let cpath = Q.snoc concl.cpath `l in
          let rpath = Q.cons `r lpath in
          let lpath = Q.cons `l (Q.take_front_exn concl.rpath |> snd) in
          Continue { concl with fx ; side ; cpath ; lpath ; rpath }
      | Imp (_, a), Some (`r, lpath) ->
          emit { name = Asms_imp { minor = `r ; pick = `r } ;
                 path = concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let cpath = Q.snoc concl.cpath `r in
          let lpath = Q.cons `l lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | And (a, f), _, Some (`r, rpath)
    when can_descend `r concl -> begin
      match expose f, Q.take_front rpath with
      | Imp (b, _), Some (`l, rpath) ->
          emit { name = Asms_imp { minor = `l ; pick = `l } ;
                 path = concl.cpath } ;
          let fx = mk_imp a b |@ concl.fx in
          let side = flip concl.side in
          let cpath = Q.snoc concl.cpath `l in
          let rpath = Q.cons `r rpath in
          Continue { concl with fx ; side ; cpath ; rpath }
      | Imp (_, b), Some (`r, rpath) ->
          emit { name = Asms_imp { minor = `l ; pick = `r } ;
                 path = concl.cpath } ;
          let fx = mk_and a b |@ concl.fx in
          let cpath = Q.snoc concl.cpath `r in
          let rpath = Q.cons `r rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_asms_allex ~emit concl =
  abort_unless (concl.side = `l) ;
  match expose concl.fx.data,
        Q.take_front concl.lpath,
        Q.take_front concl.rpath with
  | And (f, b), Some (`l, lpath), _
    when can_descend `l concl -> begin
      match expose f, Q.take_front lpath with
      | (Forall (vty, a) as fexp), Some (`d, lpath)
      | (Exists (vty, a) as fexp), Some (`d, lpath) ->
          with_var concl.fx.tycx vty begin fun _ tycx ->
            let name = match fexp with
              | Forall _ -> Asms_all { minor = `r }
              | _ -> Asms_ex { minor = `r }
            in
            emit { name ; path = concl.cpath } ;
            let fx = { data = mk_and a (shift 1 b) ; tycx } in
            let cpath = Q.snoc concl.cpath `d in
            let lpath = Q.cons `l lpath in
            Continue { concl with fx ; cpath ; lpath }
          end
      | _ -> abort ()
    end
  | And (a, f), _, Some (`r, rpath)
    when can_descend `r concl -> begin
      match expose f, Q.take_front rpath with
      | (Forall (vty, b) as fexp), Some (`d, rpath)
      | (Exists (vty, b) as fexp), Some (`d, rpath) ->
          with_var concl.fx.tycx vty begin fun _ tycx ->
            let name = match fexp with
              | Forall _ -> Asms_all { minor = `l }
              | _ -> Asms_ex { minor = `l }
            in
            emit { name ; path = concl.cpath } ;
            let fx = { data = mk_and (shift 1 a) b ; tycx } in
            let cpath = Q.snoc concl.cpath `d in
            let rpath = Q.cons `r rpath in
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
  (* | Point_term of path *)
  | Link_form of { src   : path ;
                   dest  : path }
  (* | Link_eq   of { src : path ; *)
  (*                  dest : path } *)
  | Contract  of path
  | Weaken    of path

exception Bad_link of { goal : formx ; mrule : dmanip_rule }

let compute_derivation ~emit goal mrule =
  let fail () = raise @@ Bad_link { goal ; mrule } in
  let rec analyze_link cpath src dest =
    match Q.take_front src, Q.take_front dest with
    | Some (ds, src), Some (dd, dest) when ds = dd ->
        analyze_link (Q.snoc cpath ds) src dest
    | Some (ds, _), Some (dd, _) ->
        if ds = `l && dd = `r then
          (cpath, src, dest, `r)
        else if ds = `r && dd = `l then
          (cpath, dest, src, `l)
        else fail ()
    | _ -> fail ()
  in
  match mrule with
  | Pristine
  | Point_form _
  (* | Point_term _ *)
    -> ()
  | Contract path ->
      emit { name = Contract ; path }
  | Weaken path ->
      emit { name = Weaken ; path }
  | Link_form { src ; dest } -> begin
      let (cpath, lpath, rpath, dest_in) = analyze_link Q.empty src dest in
      let (fx, side) = formx_at goal cpath in
      let concl = { cpath ; fx ; side ; lpath ; rpath ; dest_in } in
      spin_rules ~emit concl
    end
  (* | Link_eq _ -> failwith "unfinished" *)
