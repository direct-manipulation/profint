(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

module Ty = struct

  type t =
    | Basic of Ident.t
    | Arrow of t * t
    | Var of {
        id : int ;
        mutable subst : t Option.t ;
      }

  type ty = t

  let rec norm = function
    | Basic _ as ty -> Some ty
    | Arrow (tya, tyb) -> begin
        match norm tya, norm tyb with
        | Some tya, Some tyb ->
            Some (Arrow (tya, tyb))
        | _ -> None
      end
    | Var { subst = Some ty ; _ } ->
        norm ty
    | Var { subst = None ; _ } ->
        None

  let rec equal ty1 ty2 =
    match ty1, ty2 with
    | Basic x, Basic y -> Ident.equal x y
    | Arrow (ty1a, ty1b), Arrow (ty2a, ty2b) ->
        equal ty1a ty2a && equal ty1b ty2b
    | ty1, Var { subst = Some ty2 ; _ }
    | Var { subst = Some ty1 ; _ }, ty2 -> equal ty1 ty2
    | Var { id = v1 ; _ }, Var { id = v2 ; _ } -> v1 = v2
    | _ -> false

  exception Norm

  let norm_exn ty =
    match norm ty with
    | None -> raise Norm
    | Some ty -> ty

  let k_o = Ident.of_string "\\o"
  let o = Basic k_o

  let rec to_exp ty =
    match ty with
    | Basic a ->
        if Ident.equal a k_o then Doc.(Atom (string "\\o"))
        else Doc.(Atom (string (Ident.to_string a)))
    | Arrow (ta, tb) ->
        Doc.(Appl (1, Infix (string " -> ", Right,
                             [to_exp ta ; to_exp tb])))
    | Var v -> begin
        match v.subst with
        | None ->
            let rep = "'a" ^ Int.to_string v.id in
            Doc.(Atom (string rep))
        | Some ty -> to_exp ty
      end

  let pp out ty =
    to_exp ty |> Doc.bracket |> Doc.pp out

  let to_string ty =
    to_exp ty |> Doc.bracket |> Doc.to_string
end

type poly_ty = {
  nvars : int ;
  ty : Ty.t
}

type sigma = {
  basics : Ident.Set.t ;
  consts : poly_ty Ident.Map.t ;
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
        if not @@ Ident.Set.mem b sigma.basics then fail ()
    | Ty.Var {subst = Some _ ; _} -> fail ()
    | Ty.Var {id ; _} ->
        if not (0 <= id && id < pty.nvars) then fail ()
  in
  aux pty.ty

exception Invalid_sigma_extension

let is_declared sigma k =
  Ident.Set.mem k sigma.basics || Ident.Map.mem k sigma.consts

let add_basic sigma b =
  if is_declared sigma b then begin
    (* Format.eprintf "Basic type %S already declared@." b ; *)
    raise Invalid_sigma_extension
  end ;
  { sigma with basics = Ident.Set.add b sigma.basics }

let add_const sigma k pty =
  if is_declared sigma k then begin
    (* Format.eprintf "Constant %S already declared@." k ; *)
    raise Invalid_sigma_extension
  end ;
  check_well_formed sigma pty ;
  { sigma with consts = Ident.Map.add k pty sigma.consts }

module K = struct
  let next_internal =
    let count = ref 0 in
    fun hint -> count := !count + 1 ;
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
  ] in
  (* note: checks are being bypassed because these have been manually
     checked to be well-formed. *)
  { basics = Ident.Set.of_list [Ty.k_o] ;
    consts = Ident.Map.of_seq @@ List.to_seq binds }

let sigma : sigma ref = ref sigma0
let reset_sigma () = sigma := sigma0

let fresh_tyvar =
  let count = ref 0 in
  fun () ->
    count := !count + 1 ;
    Ty.Var {id = !count ; subst = None}

let thaw_ty pty =
  if pty.nvars = 0 then pty.ty else
  let tab = Array.init pty.nvars (fun _ -> fresh_tyvar ()) in
  let rec aux ty =
    match ty with
    | Ty.Basic _ -> ty
    | Ty.Arrow (tya, tyb) -> Arrow (aux tya, aux tyb)
    | Ty.Var {id ; _} -> Array.get tab id
  in
  aux pty.ty

let pp_sigma out sigma =
  Ident.Set.iter begin fun i ->
    if not @@ Ident.Set.mem i sigma0.basics then
      Stdlib.Format.fprintf out "%s : \\type.@." (Ident.to_string i)
  end sigma.basics ;
  Ident.Map.iter begin fun k pty ->
    if not @@ Ident.Map.mem k sigma0.consts then
      Stdlib.Format.fprintf out "%s : %a.@."
        (Ident.to_string k)
        Ty.pp (thaw_ty pty)
  end sigma.consts

let lookup_ty k = Option.map thaw_ty @@ Ident.Map.find_opt k !sigma.consts
let lookup_ty_or_fresh k =
  match lookup_ty k with
  | Some ty -> ty
  | None -> fresh_tyvar ()

(** Untyped terms *)
module U = struct
  type term =
    | Idx of int
    | Var of Ident.t
    | Kon of Ident.t * Ty.t option
    | App of term * term
    | Abs of Ident.t * Ty.t option * term

  let rec app h args =
    match args with
    | [] -> h
    | arg :: args -> app (App (h, arg)) args

  let var_s s = Var (Ident.of_string s)
end

(** Typed and normalized terms *)
module T = struct
  type term =
    | Abs of {var : Ident.t ; body : term}
    | App of {head : head ; spine : spine}

  and head =
    | Const of Ident.t * Ty.t
    | Index of int

  and spine = term list

  let equal_head h1 h2 =
    match h1, h2 with
    | Const (k1, ty1), Const (k2, ty2) ->
        Ident.equal k1 k2 && Ty.equal ty1 ty2
    | Index n1, Index n2 ->
        n1 = n2
    | _ -> false

  let rec equal t1 t2 =
    match t1, t2 with
    | Abs l1, Abs l2 -> equal l1.body l2.body
    | App ap1, App ap2 ->
        equal_head ap1.head ap2.head &&
        equal_spine ap1.spine ap2.spine
    | _ -> false

  and equal_spine sp1 sp2 =
    match sp1, sp2 with
    | [], [] -> true
    | (t1 :: sp1), (t2 :: sp2) ->
        equal t1 t2 && equal_spine sp1 sp2
    | _ -> false

  type sub =
    | Shift of int
    | Dot of sub * term
end

type typed_var = {
  var : Ident.t ;
  ty : Ty.t ;
}

module StringMap = Map.Make(String)

type tycx = {
  linear : typed_var list ;
  lasts : Ident.t StringMap.t ;
}

let empty = {
  linear = [] ;
  lasts = StringMap.empty ;
}

let with_var tycx vty go =
  let salt = match StringMap.find_opt vty.var.base tycx.lasts with
    | None -> 0
    | Some old -> old.salt + 1
  in
  let vty = { vty with var = { vty.var with salt } } in
  let lasts = StringMap.add vty.var.base vty.var tycx.lasts in
  let linear = vty :: tycx.linear in
  let tycx = { linear ; lasts } in
  go vty tycx

type 'a incx = {
  tycx : tycx ;
  data : 'a ;
 }

let ( |@ ) f th = { th with data = f }

let triv th = { tycx = empty ; data = th }

type dirtree =
  | File of { fname : string ; contents : string }
  | Dir of { dname : string ; contents : dirtree list }
