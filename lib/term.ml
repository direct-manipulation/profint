(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

open! Util
open Types
open! T

let index n = App {head = Index n ; spine = []}

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
      let spine = List.map ~f:(sub_term sub) u.spine in
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
        | _, 0 -> sub1
        | Shift j, _ -> Shift (j + k)
        | Dot (sub1, _), _ -> peel sub1 (k - 1)
      in
      peel sub1 k
  | _, Dot (sub2, tm) ->
      Dot (seq sub1 sub2, sub_term sub1 tm)

let shift n tm =
  match n with
  | 0 -> tm
  | _ -> sub_term (Shift n) tm

exception TypeError of string

let type_error fmt =
  Caml.Format.ksprintf (fun s -> raise (TypeError s)) fmt

let rec ty_infer cx head =
  match head with
  | Index n -> (ty_lookup cx.linear n).ty
  | Const (_, ty) -> ty

and ty_lookup cx n =
  match cx, n with
  | tvar :: _, 0 -> tvar
  | _ :: cx, n -> ty_lookup cx (n - 1)
  | [], _ -> type_error "invalid variable"

let rec ty_check cx term ty =
  match term, ty with
  | Abs f, Ty.Arrow (tya, tyb) ->
      with_var cx {var = f.var ; ty = tya} begin fun _ cx ->
        ty_check cx f.body tyb
      end
  | Abs _, _ ->
      type_error "ty_check: abs"
  | App u, _ ->
      let hty = ty_infer cx u.head in
      let rty = ty_check_spine cx u.spine hty in
      if not @@ Ty.equal ty rty then
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
      Ident.equal k1 k2 && Ty.equal ty1 ty2
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

let rec is_subterm tin tout =
  eq_term tin tout ||
  match tout with
  | Abs f ->
      is_subterm (shift 1 tin) f.body
  | App ap ->
      List.exists ~f:(is_subterm tin) ap.spine

let rec rewrite ~tfrom ~tto tm =
  if eq_term tfrom tm then tto else
  match tm with
  | Abs f -> Abs { f with
                   body = rewrite f.body
                       ~tfrom:(shift 1 tfrom)
                       ~tto:(shift 1 tto) }
  | App ap -> App { ap with
                    spine = List.map ~f:(rewrite ~tfrom ~tto) ap.spine }

let rec term_to_exp ?(cx = empty) term =
  let open Doc in
  match term with
  | Abs {var ; body} ->
      with_var cx { var ; ty = K.ty_any } begin fun vty cx ->
        let rep = String (Printf.sprintf "[%s] " (Ident.to_string vty.var)) in
        Appl (1, Prefix (rep, term_to_exp ~cx body))
      end
  | App {head ; spine = []} ->
      head_to_exp ~cx head
  | App {head ; spine} ->
      let left = head_to_exp ~cx head in
      let right = match spine with
        | [t] -> term_to_exp ~cx t
        | _ ->
            Wrap (Opaque,
                  String "[",
                  Appl (0, Infix (String ",", Left,
                                  List.map ~f:(term_to_exp ~cx) spine)),
                  String "]")
      in
      Appl (2, Infix (String " ", Non, [left ; right]))

and head_to_exp ?(cx = empty) head =
  let open Doc in
  match head with
  | Index n -> begin
      try
        let vstr = Ident.to_string (List.nth_exn cx.linear n).var in
        Atom (String vstr)
      with _ -> Atom (String ("?" ^ Int.to_string n))
    end
  | Const (k, _) -> Atom (String (Ident.to_string k))

let termx_to_exp tx = term_to_exp ~cx:tx.tycx tx.data
let headx_to_exp hx = head_to_exp ~cx:hx.tycx hx.data

let pp_term ?cx out term =
  term_to_exp ?cx term
  |> Doc.bracket
  |> Doc.pp_doc out

let term_to_string ?cx term =
  term_to_exp ?cx term
  |> Doc.bracket
  |> Doc.lin_doc

let pp_head ?cx out head =
  head_to_exp ?cx head
  |> Doc.bracket
  |> Doc.pp_doc out

let head_to_string ?cx head =
  head_to_exp ?cx head
  |> Doc.bracket
  |> Doc.lin_doc
