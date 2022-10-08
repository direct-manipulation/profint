(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

open Types
open T
open Form4_core
open Form4_paths
open Form4_cos
open Form4_simplify

(******************************************************************************)
(* Direct Manipulation Rules *)

type concl = {
  cpath : Path.t ;                (* path to fx *)
  side : Path.Dir.t ;             (* which side is fx *)
  fx : formx ;                    (* scrutinee *)
  lpath : Path.t ;                (* where to go in left subformula *)
  rpath : Path.t ;                (* where to go in right subformula *)
  dest_in : Path.Dir.t ;          (* R : l->r, L : r->l *)
}

type rule_result =
  | Done
  | Continue of concl

exception Inapplicable
let abort_if cond : unit = if cond then raise Inapplicable
let abort_unless cond : unit = abort_if (not cond)
let abort () = raise Inapplicable

type dmanip = emit:(rule -> cos_premise) -> concl -> rule_result

let prin (cp : cos_premise) = cp.prin

let go_path fx cpath dir =
  let (fx, dir) = go fx dir in
  let cpath = Path.snoc cpath dir in
  (fx, cpath)

let sing_l = Path.(cons L init)
let sing_r = Path.(cons R init)

let try_goal_init : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  abort_unless (Path.equal concl.lpath sing_l) ;
  abort_unless (Path.equal concl.rpath sing_r) ;
  match expose concl.fx.data with
  | Imp (a, b) -> begin
      match expose a, expose b with
      | Atom T.(App a), Atom T.(App b) when T.equal_head a.head b.head ->
          ignore @@ emit { name = Init ; path = concl.cpath } ;
          Done
      | Eq (s, t, _), _ ->
          if Term.is_subterm s b then
            ignore @@ emit { name = Rewrite { from = L } ; path = concl.cpath }
          else if Term.is_subterm t b then
            ignore @@ emit { name = Rewrite { from = R } ; path = concl.cpath }
          else abort () ;
          Done
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_release : dmanip = fun ~emit:_ concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  abort_unless (Path.equal concl.lpath sing_l) ;
  abort_unless (Path.equal concl.rpath sing_r) ;
  match expose concl.fx.data with
  | Imp _ ->
      (* nothing to emit *)
      Done
  | _ -> abort ()

let try_goal_ts_and : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  match expose concl.fx.data, Path.expose_front concl.rpath with
  | Imp (_, f), Some (R, rpath) -> begin
      match expose f, Path.expose_front rpath with
      | And _, Some ((L | R) as dir, rpath) ->
          let fx = prin @@ emit { name = Goal_ts_and { pick = dir } ; path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath dir in
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_and_ts : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  match expose concl.fx.data, Path.expose_front concl.lpath with
  | Imp (f, _), Some (L, lpath) -> begin
      match expose f, Path.expose_front lpath with
      | And _, Some ((L | R) as dir, lpath) ->
          let pick = match dir with Path.Dir.L -> Path.Dir.L | _ -> Path.Dir.R in
          let fx = prin @@ emit { name = Goal_and_ts { pick } ; path = concl.cpath } in
          let lpath = Path.cons Path.Dir.L lpath in
          Continue { concl with fx ; lpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_ts_or : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  match expose concl.fx.data, Path.expose_front concl.rpath with
  | Imp (_, f), Some (R, rpath) -> begin
      match expose f, Path.expose_front rpath with
      | Or _, Some ((L | R) as dir, rpath) ->
          let pick = match dir with Path.Dir.L -> Path.Dir.L | _ -> Path.Dir.R in
          let fx = prin @@ emit { name = Goal_ts_or { pick } ; path = concl.cpath } in
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_or_ts : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  match expose concl.fx.data, Path.expose_front concl.lpath with
  | Imp (f, _), Some (L, lpath) -> begin
      match expose f, Path.expose_front lpath with
      | Or _, Some ((L | R) as dir, lpath) ->
          let fx = prin @@ emit { name = Goal_or_ts ; path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath dir in
          let lpath = Path.cons Path.Dir.L lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_ts_imp : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  match expose concl.fx.data, Path.expose_front concl.rpath with
  | Imp (_, f), Some (R, rpath) -> begin
      match expose f, Path.expose_front rpath with
      | Imp _, Some (L, rpath) ->
          let fx = prin @@ emit { name = Goal_ts_imp { pick = L } ; path = concl.cpath } in
          let side = Path.Dir.flip concl.side in
          let fx, cpath = go_path fx concl.cpath L in
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; side ; cpath ; rpath }
      | Imp _, Some (R, rpath) ->
          let fx = prin @@ emit { name = Goal_ts_imp { pick = R } ; path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath R in
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_imp_ts : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  match expose concl.fx.data, Path.expose_front concl.lpath with
  | Imp (f, _), Some (L, lpath) -> begin
      match expose f, Path.expose_front lpath with
      | Imp _, Some (R, lpath) ->
          let fx = prin @@ emit { name = Goal_imp_ts ; path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath R in
          let lpath = Path.cons Path.Dir.L lpath in
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

let try_goal_ts_allex ~qsel : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  match expose concl.fx.data, Path.expose_front concl.rpath with
  | Imp (_, f), Some (R, rpath) -> begin
      match expose f, Path.expose_front rpath with
      | (Forall _ as fexp), Some (L, rpath)
      | (Exists _ as fexp), Some (L, rpath)
        when qsel fexp ->
          let name = if is_forall fexp then Goal_ts_all else Goal_ts_ex in
          let fx = prin @@ emit { name ; path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath L in
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_goal_allex_ts ~qsel : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side R) ;
  match expose concl.fx.data, Path.expose_front concl.lpath with
  | Imp (f, _), Some (L, lpath) -> begin
      match expose f, Path.expose_front lpath with
      | (Forall _ as fexp), Some (L, lpath)
      | (Exists _ as fexp), Some (L, lpath)
        when qsel fexp ->
          let name = if is_forall fexp then Goal_all_ts else Goal_ex_ts in
          let fx = prin @@ emit { name ; path = concl.cpath } in
          (* Caml.Format.printf "goal_allex_ts[%s]: %a => %a@." var *)
          (*   pp_formx fx pp_formx (go fx (I var)) ; *)
          let fx, cpath = go_path fx concl.cpath L in
          let lpath = Path.cons Path.Dir.L lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let can_descend (dir : Path.Dir.t) concl =
  match dir, concl.dest_in with
  | L, L ->
      (* descend left on r2l links unless already at dest *)
      (not @@ Path.equal concl.lpath sing_l)
  | L, R ->
      (* descend left on l2r links only if already at dest *)
      (Path.equal concl.rpath sing_r)
  | R, L ->
      (* descend right on r2l links only if already at dest *)
      (Path.equal concl.lpath sing_l)
  | R, R ->
      (* descend right on l2r links unless already at dest *)
      (not @@ Path.equal concl.rpath sing_r)

let try_asms_release ~emit:_ concl =
  abort_unless (Path.Dir.equal concl.side L) ;
  match expose concl.fx.data with
  | And _ ->
      (* nothing to emit *)
      Done
  | _ -> abort ()

let try_asms_and : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side L) ;
  match expose concl.fx.data,
        Path.expose_front concl.lpath,
        Path.expose_front concl.rpath with
  | And (f, _), Some (L, lpath), _
    when can_descend L concl -> begin
      match expose f, Path.expose_front lpath with
      | And _, Some ((L | R) as dir, lpath) ->
          let pick = match dir with L -> Path.Dir.L | _ -> Path.Dir.R in
          let fx = prin @@ emit { name = Asms_and { minor = R ; pick } ;
                                  path = concl.cpath } in
          (* cpath unchanged *)
          let lpath = Path.cons Path.Dir.L lpath in
          Continue { concl with fx ; lpath }
      | _ -> abort ()
    end
  | And (_, f), _, Some (R, rpath)
    when can_descend R concl -> begin
      match expose f, Path.expose_front rpath with
      | And _, Some ((L | R) as dir, rpath) ->
          let pick = match dir with L -> Path.Dir.L | _ -> Path.Dir.R in
          let fx = prin @@ emit { name = Asms_and { minor = L ; pick } ;
                                  path = concl.cpath } in
          (* cpath unchanged *)
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_asms_or : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side L) ;
  match expose concl.fx.data,
        Path.expose_front concl.lpath,
        Path.expose_front concl.rpath with
  | And (f, _), Some (L, lpath), _
    when can_descend L concl -> begin
      match expose f, Path.expose_front lpath with
      | Or _, Some ((L | R) as dir, lpath) ->
          let pick = match dir with L -> Path.Dir.L | _ -> Path.Dir.R in
          let fx = prin @@ emit { name = Asms_or { minor = R ; pick } ;
                                  path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath dir in
          let lpath = Path.cons Path.Dir.L lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | And (_, f), _, Some (R, rpath)
    when can_descend R concl -> begin
      match expose f, Path.expose_front rpath with
      | Or _, Some ((L | R) as dir, rpath) ->
          let pick = match dir with L -> Path.Dir.L | _ -> Path.Dir.R in
          let fx = prin @@ emit { name = Asms_or { minor = L ; pick } ;
                                  path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath dir in
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_asms_imp : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side L) ;
  match expose concl.fx.data,
        Path.expose_front concl.lpath,
        Path.expose_front concl.rpath with
  | And (f, _), Some (L, lpath), _
    when can_descend L concl -> begin
      match expose f, Path.expose_front lpath with
      | Imp _, Some (L, lpath) ->
          let fx = prin @@ emit { name = Asms_imp { minor = R ; pick = L } ;
                                  path = concl.cpath } in
          let side = Path.Dir.flip concl.side in
          let fx, cpath = go_path fx concl.cpath L in
          let rpath = Path.cons Path.Dir.R lpath in
          let lpath = Path.cons Path.Dir.L (Path.expose_front_exn concl.rpath |> snd) in
          Continue { concl with fx ; side ; cpath ; lpath ; rpath }
      | Imp _, Some (R, lpath) ->
          let fx = prin @@ emit { name = Asms_imp { minor = R ; pick = R } ;
                                  path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath R in
          let lpath = Path.cons Path.Dir.L lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | And (_, f), _, Some (R, rpath)
    when can_descend R concl -> begin
      match expose f, Path.expose_front rpath with
      | Imp _, Some (L, rpath) ->
          let fx = prin @@ emit { name = Asms_imp { minor = L ; pick = L } ;
                                  path = concl.cpath } in
          let side = Path.Dir.flip concl.side in
          let fx, cpath = go_path fx concl.cpath L in
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; side ; cpath ; rpath }
      | Imp _, Some (R, rpath) ->
          let fx = prin @@ emit { name = Asms_imp { minor = L ; pick = R } ;
                                  path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath R in
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let try_asms_allex : dmanip = fun ~emit concl ->
  abort_unless (Path.Dir.equal concl.side L) ;
  match expose concl.fx.data,
        Path.expose_front concl.lpath,
        Path.expose_front concl.rpath with
  | And (f, _), Some (L, lpath), _
    when can_descend L concl -> begin
      match expose f, Path.expose_front lpath with
      | (Forall _ as fexp), Some (L, lpath)
      | (Exists _ as fexp), Some (L, lpath) ->
          let name = match fexp with
            | Forall _ -> Asms_all { minor = R }
            | _ -> Asms_ex { minor = R }
          in
          let fx = prin @@ emit { name ; path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath L in
          let lpath = Path.cons Path.Dir.L lpath in
          Continue { concl with fx ; cpath ; lpath }
      | _ -> abort ()
    end
  | And (_, f), _, Some (R, rpath)
    when can_descend R concl -> begin
      match expose f, Path.expose_front rpath with
      | (Forall _ as fexp), Some (L, rpath)
      | (Exists _ as fexp), Some (L, rpath) ->
          let name = match fexp with
            | Forall _ -> Asms_all { minor = L }
            | _ -> Asms_ex { minor = L }
          in
          let fx = prin @@ emit { name ; path = concl.cpath } in
          let fx, cpath = go_path fx concl.cpath L in
          let rpath = Path.cons Path.Dir.R rpath in
          Continue { concl with fx ; cpath ; rpath }
      | _ -> abort ()
    end
  | _ -> abort ()

let all_rules : dmanip list = [
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
  (* end *)
  try_goal_release ;
  try_asms_release ;
]

let rec spin_rules ~emit concl =
  let rec try_all concl rules =
    match rules with
    | [] ->
        Caml.Format.eprintf "spin_rules: stuck on: @[%a@]@. lpath = %a@. rpath = %a@. cpath = %a@.%!"
          pp_formx concl.fx
          pp_path concl.lpath
          pp_path concl.rpath
          pp_path concl.cpath ;
        failwith "stuck"
    | rule :: rules -> begin
        match rule ~emit concl with
        | Done -> ()
        | Continue concl -> spin_rules ~emit concl
        | exception Inapplicable -> try_all concl rules
      end
  in
  try_all concl all_rules

type mstep =
  | Pristine
  | Contract of { path : Path.t }
  | Weaken   of { path : Path.t }
  | Link     of { src  : Path.t ;
                  dest : Path.t ;
                  copy : bool } (* contract? *)
  | Inst     of { path : Path.t ;
                  term : U.term }

exception Bad_mstep of mstep

let compute_derivation goal msteps =
  let bottom = goal in
  let middle = ref [] in
  let top = ref bottom in
  let emit rule =
    (* Caml.Format.eprintf "compute_derivation: rule = %a@." pp_rule rule ; *)
    (* Caml.Format.eprintf "compute_derivation: goal = %a@." pp_formx !top ; *)
    let prem = compute_premise !top rule in
    (* Caml.Format.eprintf "compute_derivation: prem = %a@." pp_formx prem.goal ; *)
    middle := (prem.goal, rule, !top) :: !middle ;
    top := prem.goal ;
    prem
  in
  let compute_one mstep =
    let fail () = raise @@ Bad_mstep mstep in
    let goal = !top in
    let rec analyze_link cpath src dest =
      match Path.expose_front src, Path.expose_front dest with
      | Some (ds, src), Some (dd, dest) when Path.Dir.equal ds dd ->
          analyze_link (Path.snoc cpath ds) src dest
      | Some (ds, _), Some (dd, _) ->
          if Path.Dir.equal ds Path.Dir.L && Path.Dir.equal dd R then
            (cpath, src, dest, Path.Dir.R)
          else if Path.Dir.equal ds R && Path.Dir.equal dd L then
            (cpath, dest, src, Path.Dir.L)
          else fail ()
      | _ -> fail ()
    in begin
      match mstep with
      | Pristine -> ()
      | Contract { path ; _ } ->
          ignore @@ emit { name = Contract ; path }
      | Weaken { path ; _ } ->
          ignore @@ emit { name = Weaken ; path }
      | Inst { term ; path } ->
          let (fx, side) = formx_at goal path in
          let (term, _) = Uterm.ty_check fx.tycx term in
          let term = term |@ fx in
          let goal = (emit { name = Inst { side ; term } ; path }).goal in
          recursive_simplify ~emit goal Path.init R
      | Link { src ; dest ; copy } -> begin
          let (cpath, lpath, rpath, dest_in) = analyze_link Path.init src dest in
          let (goal, cpath) =
            if not copy then (goal, cpath) else
            if Path.Dir.equal dest_in L then begin
              match Path.expose_back rpath with
              | Some (path, L) ->
                  let rule = { name = Contract ;
                               path = Path.append cpath path } in
                  let goal = (emit rule).goal in
                  (goal, cpath)
              | _ -> fail ()
            end else begin
              let rule = { name = Contract ; path = cpath } in
              let goal = (emit rule).goal in
              let cpath = Path.snoc cpath R in
              (goal, cpath)
            end
          in
          let (fx, side) = formx_at goal cpath in
          let concl = { cpath ; fx ; side ; lpath ; rpath ; dest_in } in
          spin_rules ~emit concl ;
          recursive_simplify ~emit !top Path.empty R
        end
    end in
  List.iter ~f:compute_one msteps ;
  Form4_cos.{ top = !top ; middle = !middle ; bottom }

let mk_src f =
  Mk.mk_mdata (T.App { head = Const (Ident.of_string "src", K.ty_any) ; spine = [] }) K.ty_any f
let mk_dest f =
  Mk.mk_mdata (T.App { head = Const (Ident.of_string "dest", K.ty_any) ; spine = [] }) K.ty_any f

let mark_locations goal mstep =
  match mstep with
  | Pristine -> goal
  | Contract { path }
  | Weaken { path } ->
      transform_at goal.data path mk_src |@ goal
  | Inst { path ; _ } ->
      transform_at goal.data path mk_src |@ goal
  | Link lf ->
      let f = transform_at goal.data lf.src mk_src in
      transform_at f lf.dest mk_dest |@ goal

let pp_mstep out mstep =
  match mstep with
  | Pristine -> Caml.Format.pp_print_string out "Pristine"
  | Contract { path } ->
      Caml.Format.fprintf out "Contract { path = %a }"
        pp_path path
  | Weaken { path } ->
      Caml.Format.fprintf out "Weaken { path = %a }"
        pp_path path
  | Inst { path ; term } ->
      Caml.Format.fprintf out "Inst @[<hv2>{ path = %a ;@ termx = @[<hov2>%a@] }@]"
        pp_path path
        Uterm.pp_uterm_ term
  | Link { src ; dest ; copy } ->
      Caml.Format.fprintf out "Link @[<hv2>{ src = %a ;@ dest = %a ;@ copy = %b }@]"
        pp_path src
        pp_path dest
        copy

let dir_to_uterm n (d : Path.Dir.t) =
  match d with
  | L -> 2 * n
  | R -> 2 * n + 1

let path_to_uterm (path : Path.t) : U.term =
  let buf = Buffer.create (Path.length path) in
  Buffer.add_char buf 'P' ;
  Path.to_list path |>
  List.fold_left ~init:1 ~f:dir_to_uterm |>
  Int.to_string |>
  Buffer.add_string buf ;
  U.var_s (Buffer.contents buf)

let mstep_to_uterm mstep =
  match mstep with
  | Pristine -> U.var_s "P"
  | Contract { path } -> U.app (U.var_s "C") [path_to_uterm path]
  | Weaken { path } -> U.app (U.var_s "W") [path_to_uterm path]
  | Link { src ; dest ; copy } ->
      let src = path_to_uterm src in
      let dst = path_to_uterm dest in
      let copy = if copy then U.var_s "t" else U.var_s "f" in
      U.app (U.var_s "L") [src ; dst ; copy]
  | Inst { path ; term } ->
      let path = path_to_uterm path in
      U.app (U.var_s "I") [path ; term]

exception Bad_path

let to_path (form : form) (id : int) : Path.t =
  if id = 0 then raise Bad_path else
  let rec aux here form trail =
    if List.equal Int.equal trail [] then here else
    match expose form, trail with
    | ( And (form, _) | Or (form, _) | Imp (form, _) ), (0 :: trail) ->
        let here = Path.snoc here Path.Dir.L in
        aux here form trail
    | ( And (_, form) | Or (_, form) | Imp (_, form) ), (1 :: trail) ->
        let here = Path.snoc here Path.Dir.R in
        aux here form trail
    | ( Forall (_, form) | Exists (_, form) ), (0 :: trail) ->
        let here = Path.snoc here L in
        aux here form trail
    | Mdata (_, _, form), _ ->
        aux here form trail
    | _ ->
        raise Bad_path
  in
  let trail =
    let bits = ref [] in
    let n = ref id in
    while !n <> 0 do
      bits := (!n land 1) :: !bits ;
      n := !n lsr 1
    done ;
    List.tl_exn !bits
  in
  aux Path.empty form trail

