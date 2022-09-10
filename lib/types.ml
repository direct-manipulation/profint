(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util

type ty =
  | Basic of ident
  | Arrow of ty * ty
  | Tyvar of {id : int ; mutable subst : ty option}

let rec ty_norm = function
  | Tyvar { subst = Some ty ; _ } -> ty_norm ty
  | ty -> ty

module K = struct
  let next_internal =
    let count = ref 0 in
    fun hint -> incr count ;
      Printf.sprintf {|#%s@%d#|} hint !count

  let k_mdata = next_internal "mdata"
  let k_all = next_internal "forall"
  let k_ex  = next_internal "exists"
  let k_and = next_internal "and"
  let k_top = next_internal "top"
  let k_or  = next_internal "or"
  let k_bot = next_internal "bot"
  let k_imp = next_internal "imp"
  let k_eq  = next_internal "eq"
  let k_pos_int = next_internal "posint"
  let k_neg_int = next_internal "negint"
  let k_o  = next_internal "o"
  let ty_o = Basic k_o
  (* let k_i  = next_internal "i" *)
  (* let ty_i = Basic k_i *)
  let ty_any = Basic (next_internal "?")
end

let rec ty_to_exp ty =
  match ty with
  | Basic a ->
      if a = K.k_o then Doc.(Atom (String "\\o"))
      else Doc.(Atom (String a))
  | Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (String " -> ", Right,
                           [ty_to_exp ta ; ty_to_exp tb])))
  | Tyvar v -> begin
      match v.subst with
      | None ->
          let rep = "'a" ^ string_of_int v.id in
          Doc.(Atom (String rep))
      | Some ty -> ty_to_exp ty
    end

let pp_ty out ty =
  ty_to_exp ty |> Doc.bracket |> Doc.pp_doc out

let ty_to_string ty =
  ty_to_exp ty |> Doc.bracket |> Doc.lin_doc


type poly_ty = {nvars : int ; ty : ty}

type sigma = {
  basics : IdSet.t ;
  consts : poly_ty IdMap.t ;
}

exception Ill_formed_type of { sigma : sigma ; pty : poly_ty }

let check_well_formed sigma pty =
  let fail () = raise @@ Ill_formed_type { sigma ; pty } in
  let rec aux = function
    | Arrow (t1, t2) -> aux t1 ; aux t2
    | Basic b ->
        if not @@ IdSet.mem b sigma.basics then fail ()
    | Tyvar {subst = Some _ ; _} -> fail ()
    | Tyvar {id ; _} ->
        if not (0 <= id && id < pty.nvars) then fail ()
  in
  aux pty.ty

exception Invalid_sigma_extension

let is_declared sigma k =
  IdSet.mem k sigma.basics || IdMap.mem k sigma.consts

let add_basic sigma b =
  if is_declared sigma b then begin
    (* Format.eprintf "Basic type %S already declared@." b ; *)
    raise Invalid_sigma_extension
  end ;
  { sigma with basics = IdSet.add b sigma.basics }

let add_const sigma k pty =
  if is_declared sigma k then begin
    (* Format.eprintf "Constant %S already declared@." k ; *)
    raise Invalid_sigma_extension
  end ;
  check_well_formed sigma pty ;
  { sigma with consts = IdMap.add k pty sigma.consts }

let sigma0 : sigma =
  let vnum n = Tyvar {id = n ; subst = None} in
  let binds = [
    K.k_all,     {nvars = 1 ; ty = Arrow (Arrow (vnum 0, K.ty_o), K.ty_o)} ;
    K.k_ex,      {nvars = 1 ; ty = Arrow (Arrow (vnum 0, K.ty_o), K.ty_o)} ;
    K.k_and,     {nvars = 0 ; ty = Arrow (K.ty_o, Arrow (K.ty_o, K.ty_o))} ;
    K.k_top,     {nvars = 0 ; ty = K.ty_o} ;
    K.k_or,      {nvars = 0 ; ty = Arrow (K.ty_o, Arrow (K.ty_o, K.ty_o))} ;
    K.k_bot,     {nvars = 0 ; ty = K.ty_o} ;
    K.k_imp,     {nvars = 0 ; ty = Arrow (K.ty_o, Arrow (K.ty_o, K.ty_o))} ;
    K.k_eq,      {nvars = 1 ; ty = Arrow (vnum 0, Arrow (vnum 0, K.ty_o))} ;
    K.k_pos_int, {nvars = 0 ; ty = Arrow (K.ty_o, Arrow (K.ty_o, K.ty_o))} ;
    K.k_neg_int, {nvars = 0 ; ty = Arrow (K.ty_o, Arrow (K.ty_o, K.ty_o))} ;
  ] in
  (* note: checks are being bypassed because these have been manually
     checked to be well-formed. *)
  { basics = IdSet.of_list [K.k_o (* ; K.k_i *)] ;
    consts =
      List.fold_left (fun consts (k, pty) -> IdMap.add k pty consts)
        IdMap.empty binds }

let sigma : sigma ref = ref sigma0
let reset_sigma () = sigma := sigma0

let fresh_tyvar =
  let count = ref 0 in
  fun () ->
    incr count ;
    Tyvar {id = !count ; subst = None}

let thaw_ty pty =
  if pty.nvars = 0 then pty.ty else
  let tab = Array.init pty.nvars (fun _ -> fresh_tyvar ()) in
  let rec aux ty =
    match ty with
    | Basic _ -> ty
    | Arrow (tya, tyb) -> Arrow (aux tya, aux tyb)
    | Tyvar {id ; _} -> Array.get tab id
  in
  aux pty.ty

let pp_sigma out sigma =
  IdSet.iter begin fun i ->
    if not @@ IdSet.mem i sigma0.basics then
      Format.fprintf out "%s : \\type.@." i
  end sigma.basics ;
  IdMap.iter begin fun k pty ->
    if not @@ IdMap.mem k sigma0.consts then
      Format.fprintf out "%s : %a.@." k pp_ty (thaw_ty pty)
  end sigma.consts

let lookup_ty k = thaw_ty @@ IdMap.find k !sigma.consts
let lookup_ty_or_fresh k =
  try lookup_ty k with Not_found -> fresh_tyvar ()

(** Untyped terms *)
module U = struct
  type term =
    | Idx of int
    | Var of ident
    | Kon of ident * ty option
    | App of term * term
    | Abs of ident * ty option * term
end

(** Typed and normalized terms *)
module T = struct
  type term =
    | Abs of {var : ident ; body : term}
    | App of {head : head ; spine : spine}

  and head =
    | Const of ident * ty
    | Index of int

  and spine = term list

  type sub =
    | Shift of int
    | Dot of sub * term
end

type typed_var = {
  var : ident ;
  ty : ty
}

type tycx = {
  linear : typed_var list ;
  used : IdSet.t ;
}

let empty = {
  linear = [] ;
  used = IdSet.empty ;
}

let[@inline] salt v k =
  if k = 0 then v else v ^ "_" ^ string_of_int k

let with_var ?(fresh = false) tycx vty go =
  let rec freshen v k =
    let vk = salt v k in
    if IdSet.mem vk tycx.used then freshen v (k + 1) else vk
  in
  let var = if fresh then freshen vty.var 0 else vty.var in
  let used = IdSet.add var tycx.used in
  let vty = { vty with var } in
  let linear = vty :: tycx.linear in
  go vty {linear ; used}

let last_var tycx = List.hd tycx.linear

let last tycx =
  match tycx.linear with
  | [] -> raise Not_found
  | tv :: linear ->
      (tv, { linear ; used = IdSet.remove tv.var tycx.used })

let last_opt tycx =
  match tycx.linear with
  | [] -> None
  | tv :: linear ->
      Some (tv, { linear ; used = IdSet.remove tv.var tycx.used })

type 'a incx = {
  tycx : tycx ;
  data : 'a ;
 }

let ( |@ ) f th = { th with data = f }

let triv th = { tycx = empty ; data = th }

type dirtree =
  | File of { fname : string ; contents : string }
  | Dir of { dname : string ; contents : dirtree list }
