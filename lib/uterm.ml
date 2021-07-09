(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Untyped terms and types with free variables *)

open! Util

(* The constructors of uty need to be in the same order as in Term.ty;
   otherwise we will not get the O(1) transformations. *)

type uty =
  | Basic of ident
  | Arrow of uty * uty
  | Tyvar of {id : int ; mutable subst : uty option}

external uty_of_ty : Term.ty -> uty = "%identity"

type poly_uty = {nvars : int ; uty : uty}

let fresh_tyvar =
  let count = ref 0 in
  fun () ->
    incr count ;
    Tyvar {id = !count ; subst = None}

let rec subst tab uty =
  match uty with
  | Arrow (utya, utyb) ->
      Arrow (subst tab utya, subst tab utyb)
  | Basic _ -> uty
  | Tyvar v -> begin
      match ITab.find tab v.id with
      | uty -> uty
      | exception Not_found -> uty
    end

let freshen pty =
  let tab = ITab.create pty.nvars in
  range 0 pty.nvars
  |> Seq.iter (fun k -> ITab.replace tab k (fresh_tyvar ())) ;
  subst tab pty.uty

exception TypeError of string

let ty_error fmt =
  Printf.ksprintf (fun msg -> raise (TypeError msg)) fmt

let gsig : (ident, poly_uty) Hashtbl.t = Hashtbl.create 19

type uterm =
  | Idx of int
  | Var of ident
  | Kon of ident * uty option
  | App of uterm * uterm
  | Abs of ident * uty option * uterm

type cx = (ident * uty) list

let rec tygen ~emit (cx : cx) tm ty_expected =
  match tm with
  | Idx n ->
      emit (snd (List.nth cx n)) ty_expected ;
      Idx n
  | Var x ->
      let n, ty = tyget cx x in
      emit ty ty_expected ;
      Idx n
  | Kon (k, Some ty) ->
      emit ty ty_expected ;
      Kon (k, Some ty)
  | Kon (k, None) -> begin
      match Hashtbl.find gsig k with
      | pty ->
          emit (freshen pty) ty_expected ;
          Kon (k, Some ty_expected)
      | exception Not_found ->
          ty_error "unknown constant %s" k
    end
  | App (tm, tn) ->
      let tyarg = fresh_tyvar () in
      let tyres = fresh_tyvar () in
      let tm = tygen ~emit cx tm (Arrow (tyarg, tyres)) in
      let tn = tygen ~emit cx tn tyarg in
      emit tyres ty_expected ;
      App (tm, tn)
  | Abs (x, xty, bod) ->
      let tyarg = match xty with
        | Some ty -> ty
        | None -> fresh_tyvar ()
      in
      let tyres = fresh_tyvar () in
      let bod = tygen ~emit ((x, tyarg) :: cx) bod tyres in
      emit (Arrow (tyarg, tyres)) ty_expected ;
      Abs (x, xty, bod)

and tyget ?(depth = 0) cx x =
  match cx with
  | (y, ty) :: _ when x = y -> (depth, ty)
  | _ :: cx -> tyget ~depth:(depth + 1) cx x
  | [] -> ty_error "unknown variable %s" x

let rec occurs x ty =
  match ty with
  | Tyvar y -> x == y.id || begin
      match y.subst with
      | None -> false
      | Some ty -> occurs x ty
    end
  | Basic _ -> false
  | Arrow (tya, tyb) -> occurs x tya || occurs x tyb

let solve1 ~emit l r =
  match l, r with
  | Tyvar ({subst = None ; _} as v), ty
  | ty, Tyvar ({subst = None ; _} as v) ->
      if occurs v.id ty then ty_error "circularity" ;
      v.subst <- Some ty
  | Tyvar {subst = Some l ; _}, r
  | l, Tyvar {subst = Some r ; _} ->
      emit (l, r)
  | Basic a, Basic b when a = b ->
      ()
  | Arrow (la, lb), Arrow (ra, rb) ->
      emit (la, ra) ;
      emit (lb, rb)
  | _ ->
      ty_error "tycon mismatch"

let solve eqns =
  let eqns = ref eqns in
  let emit eqn = eqns := eqn :: !eqns in
  let rec spin () =
    match !eqns with
    | [] -> ()
    | (l, r) :: rest ->
        eqns := rest ;
        solve1 ~emit l r ;
        spin ()
  in
  spin ()

let rec ty_freeze ?inst ty =
  match ty with
  | Arrow (ty1, ty2) ->
      Arrow (ty_freeze ?inst ty1,
             ty_freeze ?inst ty2)
  | Basic _ -> ty
  | Tyvar v -> begin
      match v.subst with
      | None -> begin
          match inst with
          | Some f -> f v.id
          | None -> ty
        end
      | Some ty ->
          ty_freeze ?inst ty
    end

let rec norm_ty ty =
  match ty with
  | Basic a -> Term.Basic a
  | Arrow (tya, tyb) -> Term.Arrow (norm_ty tya, norm_ty tyb)
  | Tyvar _ -> assert false

let rec norm_term tm =
  match tm with
  | Idx n ->
      Term.(App {head = Index n ; spine = []})
  | Kon (k, Some uty) ->
      Term.(App {head = Const (k, norm_ty uty) ; spine = []})
  | App (tm, tn) ->
      Term.(do_app (norm_term tm) [norm_term tn])
  | Abs (x, _, tm) ->
      Term.(Abs {var = x ; body = norm_term tm})
  | Var _ | Kon (_, None) ->
      assert false

external ucx_of_cx : (ident * Term.ty) list -> cx = "%identity"

let ty_check cx term =
  let ty = fresh_tyvar () in
  let eqns = ref [] in
  let emit tya tyb = eqns := (tya, tyb) :: !eqns in
  let term = tygen ~emit (ucx_of_cx cx) term ty in
  solve !eqns ;
  let ty = ty_freeze ty ~inst:(fun _ -> ty_error "non-ground type inferred") in
  (norm_term term, norm_ty ty)

module Terms = struct
  let ti = Abs ("x", Some (Basic "a"), Var "x")
  let tk = Abs ("x", Some (Basic "a"), Abs ("y", Some (Basic "b"), Var "x"))
  let ts = Abs ("x", Some (Arrow (Basic "a", Arrow (Basic "b", Basic "c"))),
                Abs ("y", None,
                     Abs ("z", None,
                          App (App (Var "x", Var "z"),
                               App (Var "y", Var "z")))))
  let tdelta = Abs ("x", None, App (Var "x", Var "x"))
end
