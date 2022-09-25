(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

module Ty = struct

  type t =
    | Basic of Ident.t
    | Arrow of t * t
    | Var of {
        id : int ;
        mutable subst : t Option.t ;
      }
  [@@deriving equal, sexp_of]

  type ty = t

  let rec norm = function
    | Var { subst = Some ty ; _ } -> norm ty
    | ty -> ty

  let k_o = Ident.of_string "\\o"
  let o = Basic k_o

  let rec to_exp ty =
    match ty with
    | Basic a ->
        if Ident.equal a k_o then Doc.(Atom (String "\\o"))
        else Doc.(Atom (String (Ident.to_string a)))
    | Arrow (ta, tb) ->
        Doc.(Appl (1, Infix (String " -> ", Right,
                             [to_exp ta ; to_exp tb])))
    | Var v -> begin
        match v.subst with
        | None ->
            let rep = "'a" ^ Int.to_string v.id in
            Doc.(Atom (String rep))
        | Some ty -> to_exp ty
      end

  let pp out ty =
    to_exp ty |> Doc.bracket |> Doc.pp_doc out

  let to_string ty =
    to_exp ty |> Doc.bracket |> Doc.lin_doc
end

type poly_ty = {
  nvars : int ;
  ty : Ty.t
}

type sigma = {
  basics : Ident.set ;
  consts : poly_ty Ident.map ;
}

exception Ill_formed_type of {
    sigma : sigma ;
    pty : poly_ty ;
  }

let check_well_formed sigma pty =
  let fail () = raise @@ Ill_formed_type { sigma ; pty } in
  let rec aux = function
    | Ty.Arrow (t1, t2) -> aux t1 ; aux t2
    | Ty.Basic b ->
        if not @@ Set.mem sigma.basics b then fail ()
    | Ty.Var {subst = Some _ ; _} -> fail ()
    | Ty.Var {id ; _} ->
        if not (0 <= id && id < pty.nvars) then fail ()
  in
  aux pty.ty

exception Invalid_sigma_extension

let is_declared sigma k =
  Set.mem sigma.basics k || Map.mem sigma.consts k

let add_basic sigma b =
  if is_declared sigma b then begin
    (* Format.eprintf "Basic type %S already declared@." b ; *)
    raise Invalid_sigma_extension
  end ;
  { sigma with basics = Set.add sigma.basics b }

let add_const sigma k pty =
  if is_declared sigma k then begin
    (* Format.eprintf "Constant %S already declared@." k ; *)
    raise Invalid_sigma_extension
  end ;
  check_well_formed sigma pty ;
  { sigma with consts = Map.set ~key:k ~data:pty sigma.consts }

module K = struct
  let next_internal =
    let count = ref 0 in
    fun hint -> Int.incr count ;
      Printf.ksprintf Ident.of_string {|#%s@%d#|} hint !count

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
  let ty_any = Ty.Basic (next_internal "?")
end

let sigma0 : sigma =
  let vnum n = Ty.Var {id = n ; subst = None} in
  let binds = [
    K.k_all,     {nvars = 1 ; ty = Arrow (Arrow (vnum 0, Ty.o), Ty.o)} ;
    K.k_ex,      {nvars = 1 ; ty = Arrow (Arrow (vnum 0, Ty.o), Ty.o)} ;
    K.k_and,     {nvars = 0 ; ty = Arrow (Ty.o, Arrow (Ty.o, Ty.o))} ;
    K.k_top,     {nvars = 0 ; ty = Ty.o} ;
    K.k_or,      {nvars = 0 ; ty = Arrow (Ty.o, Arrow (Ty.o, Ty.o))} ;
    K.k_bot,     {nvars = 0 ; ty = Ty.o} ;
    K.k_imp,     {nvars = 0 ; ty = Arrow (Ty.o, Arrow (Ty.o, Ty.o))} ;
    K.k_eq,      {nvars = 1 ; ty = Arrow (vnum 0, Arrow (vnum 0, Ty.o))} ;
    K.k_pos_int, {nvars = 0 ; ty = Arrow (Ty.o, Arrow (Ty.o, Ty.o))} ;
    K.k_neg_int, {nvars = 0 ; ty = Arrow (Ty.o, Arrow (Ty.o, Ty.o))} ;
  ] in
  (* note: checks are being bypassed because these have been manually
     checked to be well-formed. *)
  { basics = Set.of_list (module Ident) [Ty.k_o] ;
    consts = Map.of_alist_exn (module Ident) binds }

let sigma : sigma ref = ref sigma0
let reset_sigma () = sigma := sigma0

let fresh_tyvar =
  let count = ref 0 in
  fun () ->
    Int.incr count ;
    Ty.Var {id = !count ; subst = None}

let thaw_ty pty =
  if pty.nvars = 0 then pty.ty else
  let tab = Array.init pty.nvars ~f:(fun _ -> fresh_tyvar ()) in
  let rec aux ty =
    match ty with
    | Ty.Basic _ -> ty
    | Ty.Arrow (tya, tyb) -> Arrow (aux tya, aux tyb)
    | Ty.Var {id ; _} -> Array.get tab id
  in
  aux pty.ty

let pp_sigma out sigma =
  Set.iter sigma.basics ~f:begin fun i ->
    if not @@ Set.mem sigma0.basics i then
      Caml.Format.fprintf out "%s : \\type.@." (Ident.to_string i)
  end ;
  Map.iteri sigma.consts ~f:begin fun ~key:k ~data:pty ->
    if not @@ Map.mem sigma0.consts k then
      Caml.Format.fprintf out "%s : %a.@."
        (Ident.to_string k)
        Ty.pp (thaw_ty pty)
  end

let lookup_ty k = Option.map ~f:thaw_ty @@ Map.find !sigma.consts k
let lookup_ty_or_fresh k =
  lookup_ty k |>
  Option.value_or_thunk ~default:fresh_tyvar

(** Untyped terms *)
module U = struct
  type term =
    | Idx of int
    | Var of Ident.t
    | Kon of Ident.t * Ty.t option
    | App of term * term
    | Abs of Ident.t * Ty.t option * term
  [@@deriving equal, sexp_of]
end

(** Typed and normalized terms *)
module T = struct
  type term =
    | Abs of {var : Ident.t [@equal.ignore] ; body : term}
    | App of {head : head ; spine : spine}

  and head =
    | Const of Ident.t * Ty.t
    | Index of int

  and spine = term list
  [@@deriving equal, sexp_of]

  type sub =
    | Shift of int
    | Dot of sub * term
  [@@deriving equal, sexp_of]
end

type typed_var = {
  var : Ident.t ;
  ty : Ty.t ;
}
[@@deriving equal, sexp_of]

type tycx = {
  linear : typed_var list ;
  lasts : (string, Ident.t, String.comparator_witness) Map.t;
}
(* [HACK] this does not currently work. 2022-09-25T23:11:57+02:00 *)
(* [@@deriving sexp_of] *)

let sexp_of_tycx tycx = [%sexp_of : typed_var list] tycx.linear

let empty = {
  linear = [] ;
  lasts = Map.empty (module String) ;
}

let with_var tycx vty go =
  let salt = match Map.find tycx.lasts vty.var.base with
    | None -> 0
    | Some old -> old.salt + 1
  in
  let vty = { vty with var = { vty.var with salt } } in
  let lasts = Map.set ~key:vty.var.base ~data:vty.var tycx.lasts in
  let linear = vty :: tycx.linear in
  let tycx = { linear ; lasts } in
  go vty tycx

type 'a incx = {
  tycx : tycx ;
  data : 'a ;
 }
[@@deriving sexp_of]

let ( |@ ) f th = { th with data = f }

let triv th = { tycx = empty ; data = th }

type dirtree =
  | File of { fname : string ; contents : string }
  | Dir of { dname : string ; contents : dirtree list }
[@@deriving sexp_of]
