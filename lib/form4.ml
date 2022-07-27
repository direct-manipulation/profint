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

let (@>) th cx = {cx with data = th}

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
  | Pos_int of form * form
  | Neg_int of form * form

let expose (form : form) =
  match form with
  | App {head = Const (k, _) ; spine = []} when k = k_top ->
      Top
  | App {head = Const (k, _) ; spine = []} when k = k_bot ->
      Bot
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_and ->
      And (fa, fb)
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_or ->
      Or (fa, fb)
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_imp ->
      Imp (fa, fb)
  | App {head = Const (k, Arrow (ty, _)) ; spine = [t1 ; t2]} when k = k_eq ->
      Eq (t1, t2, ty)
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_neg_int ->
      Neg_int (fa, fb)
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_pos_int ->
      Pos_int (fa, fb)
  | App {head = Const (k, Arrow (Arrow (ty, _), _)) ;
         spine = [Abs {var ; body}]} when k = k_all ->
      Forall (var, ty, body)
  | App {head = Const (k, Arrow (Arrow (ty, _), _)) ;
         spine = [Abs {var ; body}]} when k = k_ex ->
      Exists (var, ty, body)
  | _ ->
      Atom form

let ty_ooo = Arrow (ty_o, Arrow (ty_o, ty_o))

let hide fsk =
  match fsk with
  | Atom f -> f
  | Eq (t1, t2, ty) ->
      App {head = Const (k_eq, Arrow (ty, Arrow (ty, ty_o))) ;
           spine = [t1 ; t2]}
  | And (fa, fb) ->
      App {head = Const (k_and, ty_ooo) ; spine = [fa ; fb]}
  | Top -> App {head = Const (k_top, ty_o) ; spine = []}
  | Neg_int (fa, fb) ->
      App {head = Const (k_neg_int, ty_ooo) ; spine = [fa ; fb]}
  | Or (fa, fb) ->
      App {head = Const (k_or, ty_ooo) ; spine = [fa ; fb]}
  | Bot -> App {head = Const (k_bot, ty_o) ; spine = []}
  | Imp (fa, fb) ->
      App {head = Const (k_imp, ty_ooo) ; spine = [fa ; fb]}
  | Pos_int (fa, fb) ->
      App {head = Const (k_pos_int, ty_ooo) ; spine = [fa ; fb]}
  | Forall (var, ty, body) ->
      App {head = Const (k_all, Arrow (Arrow (ty, ty_o), ty_o)) ;
           spine = [Abs {var ; body}]}
  | Exists (var, ty, body) ->
      App {head = Const (k_ex, Arrow (Arrow (ty, ty_o), ty_o)) ;
           spine = [Abs {var ; body}]}

(******************************************************************************)
(* paths *)

type dir = [`l | `r | `i of ident]
type path = dir list

type parity = [`l | `r]

let flip (p : parity) =
  match p with `l -> `r | `r -> `l

exception Bad_direction of {tycx : tycx ; form : form ; dir : dir}

let rec get_at : ?par:parity -> tycx -> form -> path -> (tycx -> form -> parity -> 'a) -> 'a =
  fun ?(par = `r) tycx form path k ->
  match path with
  | [] -> k tycx form par
  | dir :: path -> begin
      match expose form, dir with
      | And (form, _), `l
      | Or (form, _), `l ->
          get_at ~par tycx form path k
      | Imp (form, _), `l ->
          get_at ~par:(flip par) tycx form path k
      | And (_, form), `r
      | Or (_, form), `r
      | Imp (_, form), `r ->
          get_at ~par tycx form path k
      | Forall (_, ty, form), `i x
      | Exists (_, ty, form), `i x ->
          get_at ~par ({var = x ; ty : ty} :: tycx) form path k
      | _ ->
          raise @@ Bad_direction {tycx ; form ; dir}
    end

let formx_at ?par (formx : formx) path : formx =
  get_at ?par formx.tycx formx.data path (fun tycx form _ -> {tycx ; data = form})

let parity_at ?par tycx form path =
  get_at ?par tycx form path (fun _ _ par -> par)

let tycx_at ?par tycx form path =
  get_at ?par tycx form path (fun tycx _ _ -> tycx)

(******************************************************************************)
(* Formatting *)



(*

type indiq =
  | Basic of form
  | Link_form of {fcx : fcx ; src : fcx * form ; dest : fcx * form}
  | Link_eq of {fcx : fcx ;
                left : term ; right : term ; ty : ty ; which : [`l | `r] ;
                dest : fcx * form}
  | Point_form of {fcx : fcx ; form : form}
  | Point_eq of {fcx : fcx ; left : term ; right : term ; ty : ty ;
                 which : [`l | `r]}

type derivation = {
  current : indiq ;
  history : indiq list ;
  future  : indiq list ;
}

type history_failure =
  | Cannot_undo of derivation
  | Cannot_redo of derivation

exception History of history_failure

let start f = {current = Basic f ; history = [] ; future = []}

let undo der =
  match der.history with
  | f :: history ->
      {current = f ; history ; future = der.current :: der.future}
  | _ ->
      raise @@ History (Cannot_undo der)

let redo der =
  match der.future with
  | f :: future ->
      {current = f ; future ; history = der.current :: der.history}
  | _ ->
      raise @@ History (Cannot_redo der)

*)
