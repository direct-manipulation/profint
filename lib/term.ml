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

type term =
  | Abs of {var : ident ; body : term}
  | App of {head : head ; spine : spine}

and head =
  | Const of ident * ty
  | Index of int

and spine = term list

let index n = App {head = Index n ; spine = []}

type sub =
  | Shift of int
  | Dot of sub * term

let rec do_app head spine =
  match head, spine with
  | _, [] -> head
  | Abs f, e :: spine ->
      let sub = Dot (Shift 0, e) in
      let head = sub_term sub f.body in
      do_app head spine
  | App u, _ -> App {u with spine = u.spine @ spine}

and sub_term sub term =
  match term with
  | Abs f -> Abs {f with body = sub_term (bump sub) f.body}
  | App u ->
      let head = sub_head sub u.head in
      let spine = List.map (sub_term sub) u.spine in
      do_app head spine

and sub_head sub head =
  match head with
  | Const _ -> App {head ; spine = []}
  | Index n -> sub_index sub n

and sub_index sub n =
  match sub with
  | Shift j -> App {head = Index (j + n) ; spine = [] }
  | Dot (sub, t) -> begin
      match n with
      | 0 -> t
      | _ -> sub_index sub (n - 1)
    end

and bump sub = Dot (seq (Shift 1) sub, App {head = Index 0 ; spine = []})

and seq sub1 sub2 =
  match sub1, sub2 with
  | Shift 0, _ -> sub2
  | _, Shift k ->
      let rec peel sub1 k =
        match sub1, k with
        | Shift j, _ -> Shift (j + k)
        | _, 0 -> sub1
        | Dot (sub1, _), _ -> peel sub1 (k - 1)
      in
      peel sub1 k
  | _, Dot (sub2, tm) ->
      Dot (seq sub1 sub2, sub_term sub1 tm)

exception TypeError of string

let type_error fmt =
  Format.ksprintf (fun s -> raise (TypeError s)) fmt

let rec ty_infer cx head =
  match head with
  | Index n -> snd (ty_lookup cx n)
  | Const (_, ty) -> ty

and ty_lookup cx n =
  match cx, n with
  | ty :: _, 0 -> ty
  | _ :: cx, n -> ty_lookup cx (n - 1)
  | [], _ -> type_error "invalid variable"

let rec ty_check cx term ty =
  match term, ty with
  | Abs f, Arrow (tya, tyb) ->
      let cx = (f.var, tya) :: cx in
      ty_check cx f.body tyb
  | Abs _, _ ->
      type_error "ty_check: abs"
  | App u, _ ->
      let hty = ty_infer cx u.head in
      let rty = ty_check_spine cx u.spine hty in
      if ty <> rty then
        type_error "ty_check: app"

and ty_check_spine cx spine hty =
  match spine, hty with
  | [], _ -> hty
  | (term :: spine), Arrow (ty, hty) ->
      ty_check cx term ty ;
      ty_check_spine cx spine hty
  | _ ->
      type_error "ty_check_spine"

let rec eq_term term1 term2 =
  match term1, term2 with
  | Abs f1, Abs f2 ->
      eq_term f1.body f2.body
  | App u1, App u2 ->
      eq_head u1.head u2.head &&
      eq_spine u1.spine u2.spine
  | _ -> false

and eq_head head1 head2 =
  match head1, head2 with
  | Const (k1, ty1), Const (k2, ty2) ->
      k1 = k2 && ty1 = ty2
  | Index n1, Index n2 ->
      n1 = n2
  | _ -> false

and eq_spine spine1 spine2 =
  match spine1, spine2 with
  | [], [] ->
      true
  | (t1 :: spine1), (t2 :: spine2) ->
      eq_term t1 t2 && eq_spine spine1 spine2
  | _ -> false
