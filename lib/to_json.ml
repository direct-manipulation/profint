(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2024  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** output JSON *)

open! Base

open! Types
open! Form4

module Json = Yojson.Safe
let json_to_exp js = Doc.(Atom (string (Json.to_string js)))

module External = struct
  open Ppx_yojson_conv_lib.Yojson_conv.Primitives

  module Position = struct
    type t = Z.t

    let t_of_yojson js = Json.Util.to_string js |> Z.of_string
    let yojson_of_t t : Json.t = `String (Z.to_string t)

    open struct
      let _max = 4
      let __max = Z.of_int _max
    end

    let top = Z.one

    open struct
      let _is_top p = Stdlib.(p == top)
    end

    let cons k p =
      if k < 0 || k >= _max then invalid_arg "Position.down" ;
      Z.(p * __max + of_int k)

    exception Top

    open struct
      let unsafe_up p = Z.(p / __max)
      let unsafe_child p = Z.(to_int @@ p mod __max)
    end

    let up p = if _is_top p then raise Top ; unsafe_up p

    let child p = if _is_top p then raise Top ; unsafe_child p

    let snoc p = if _is_top p then raise Top ; (unsafe_child p, unsafe_up p)

    let snoc_opt p = if _is_top p then None else Some (unsafe_child p, unsafe_up p)

    let of_list l = Stdlib.List.fold_right cons l top

    let rec to_list p =
      if _is_top p then []
      else unsafe_child p :: to_list (unsafe_up p)
  end

  type id = string
  [@@deriving yojson]

  type ty =
    | Basic of id
    | Arrow of ty * ty
  [@@deriving yojson]

  type term =
    | Const  of id
    | Bvar   of int               (** De Bruijn indexed bound variables *)
    | Lam    of binding * term
    | App    of term * term
  and binding = id * ty
  [@@deriving yojson]

  let eq : id = "###EQ###"

  type form =
    | Atom   of id * term list
    | And    of form * form
    | True
    | Or     of form * form
    | False
    | Imp    of form * form
    | Forall of binding * form
    | Exists of binding * form
  [@@deriving yojson]

  type path =
    | Hole
    | Left  of path * [`And | `Or | `Imp] * form
    | Right of form * [`And | `Or | `Imp] * path
    | Body  of [`Forall | `Exists] * binding * path
  [@@deriving yojson]

  type 'a formx = {
    path : path ;
    ctx  : binding list ;
    right : bool ;
    repl : 'a ;
  } [@@deriving yojson]

  type rule =
    | Cos_goal_ts_and_l               (* ((a -> b) /\ c) -> (a -> (b /\ c)) *)
    | Cos_goal_ts_and_r               (* (c /\ (a -> b)) -> (a -> (c /\ b)) *)
    | Cos_goal_and_ts_l               (* (a -> b) -> (a /\ c -> b) *)
    | Cos_goal_and_ts_r               (* (a -> b) -> (c /\ a -> b) *)
    | Cos_goal_ts_or_l                (* (a -> b) -> (a -> b \/ c) *)
    | Cos_goal_ts_or_r                (* (a -> b) -> (a -> c \/ b) *)
    | Cos_goal_or_ts                  (* ((a -> c) /\ (b -> c)) -> (a \/ b -> c) *)
    | Cos_goal_ts_imp_l               (* (a /\ b -> c) -> (a -> b -> c) *)
    | Cos_goal_ts_imp_r               (* (c -> a -> b) -> (a -> c -> b) *)
    | Cos_goal_imp_ts                 (* (c /\ (a -> b)) -> ((c -> a) -> b) *)
    | Cos_goal_ts_all                 (* (forall x, a -> p x) -> (a -> forall x, p x) *)
    | Cos_goal_all_ts                 (* (exists x, p x -> b) -> (forall x, p x) -> b *)
    | Cos_goal_ts_ex                  (* (exists x, a -> p x) -> (a -> exists x, p x) *)
    | Cos_goal_ex_ts                  (* (forall x, p x -> a) -> (exists x, p x) -> a *)
    | Cos_asms_and_l_l                (* (a /\ (b /\ c)) -> (a /\ b) *)
    | Cos_asms_and_l_r                (* (a /\ (c /\ b)) -> (a /\ b) *)
    | Cos_asms_and_r_l                (* ((a /\ c) /\ b) -> (a /\ b) *)
    | Cos_asms_and_r_r                (* ((c /\ a) /\ b) -> (a /\ b) *)
    | Cos_asms_or_l_l                 (* (a /\ (b \/ c)) -> ((a /\ b) \/ c) *)
    | Cos_asms_or_l_r                 (* (a /\ (c \/ b)) -> (c \/ (a /\ b)) *)
    | Cos_asms_or_r_l                 (* ((a \/ c) /\ b) -> ((a /\ b) \/ c) *)
    | Cos_asms_or_r_r                 (* ((c \/ a) /\ b) -> (c \/ (a /\ b)) *)
    | Cos_asms_imp_l_l                (* (a /\ (b -> c)) -> ((a -> b) -> c) *)
    | Cos_asms_imp_l_r                (* (a /\ (c -> b)) -> (c -> (a /\ b)) *)
    | Cos_asms_imp_r_l                (* ((a -> c) /\ b) -> ((b -> a) -> c) *)
    | Cos_asms_imp_r_r                (* ((c -> a) /\ b) -> (c -> (a /\ b)) *)
    | Cos_asms_all_l                  (* (a /\ forall x, p x) -> forall x, (a /\ p x) *)
    | Cos_asms_all_r                  (* ((forall x, p x) /\ a) -> forall x, (p x /\ a) *)
    | Cos_asms_ex_l                   (* (a /\ exists x, p x) -> exists x, (a /\ p x) *)
    | Cos_asms_ex_r                   (* ((exists x, p x) /\ a) -> exists x, (p x /\ a) *)
    | Cos_contract                    (* (a -> a -> b) -> (a -> b) *)
    | Cos_weaken                      (* b -> (a -> b) *)
    | Cos_inst_r of term              (* p t -> (exists x, p x) *)
    | Cos_inst_l of term              (* (forall x, p x) -> p t *)
    | Cos_rewrite_rtl                 (* p s -> s = t -> p t *)
    | Cos_rewrite_ltr                 (* p t -> s = t -> p s *)
    | Cos_simp_goal_and_top           (* a -> (a /\ True) *)
    | Cos_simp_goal_top_and           (* a -> (True /\ a) *)
    | Cos_simp_asms_and_top           (* (a /\ True) -> a *)
    | Cos_simp_asms_top_and           (* (True /\ a) -> a *)
    | Cos_simp_goal_or_top            (* True -> (a \/ True) *)
    | Cos_simp_goal_top_or            (* True -> (True \/ a) *)
    | Cos_simp_asms_or_top            (* (a \/ True) -> True *)
    | Cos_simp_asms_top_or            (* (True \/ a) -> True *)
    | Cos_simp_goal_imp_top           (* True -> (a -> True) *)
    | Cos_simp_goal_top_imp           (* a -> (True -> a) *)
    | Cos_simp_asms_imp_top           (* (a -> True) -> True *)
    | Cos_simp_asms_top_imp           (* (True -> a) -> a *)
    | Cos_simp_goal_and_bot           (* False -> (a /\ False) *)
    | Cos_simp_goal_bot_and           (* False -> (False /\ a) *)
    | Cos_simp_asms_and_bot           (* (a /\ False) -> False *)
    | Cos_simp_asms_bot_and           (* (False /\ a) -> False *)
    | Cos_simp_goal_or_bot            (* a -> (a \/ False) *)
    | Cos_simp_goal_bot_or            (* a -> (False \/ a) *)
    | Cos_simp_asms_or_bot            (* (a \/ False) -> a *)
    | Cos_simp_asms_bot_or            (* (False \/ a) -> a *)
    | Cos_simp_goal_bot_imp           (* True -> (False -> a) *)
    | Cos_simp_asms_bot_imp           (* (False -> a) -> True *)
    | Cos_simp_goal_all_top           (* True -> forall (_ : T), True *)
    | Cos_simp_asms_all_top           (* (forall (_ : T), True) -> True *)
    | Cos_simp_goal_ex_bot            (* False -> exists (_ : T), False *)
    | Cos_simp_asms_ex_bot            (* (exists (_ : T), False) -> False *)
    | Cos_init                        (* True -> p -> p *)
    | Cos_congr                       (* True -> t = t *)
  [@@deriving yojson]

  type scheme = {
    pos    : Position.t ;
    rule   : rule ;
  } [@@deriving yojson]

  type rewrite = {
    above  : form ;
    below  : form ;
  } [@@deriving yojson]

  type instance = {
    scheme : scheme ;
    change : rewrite formx ;
  } [@@deriving yojson]
end

exception Conversion

let ty_to_exp (ty : Ty.t) =
  let rec map ty =
    match Ty.norm_exn ty with
    | Ty.Basic a -> External.Basic (Ident.to_string a)
    | Ty.Arrow (a, b) -> External.Arrow (map a, map b)
    | Ty.Var _ -> assert false
  in
  map ty |> [%yojson_of: _] |> json_to_exp

(*
let termx_to_exp (tx : T.term incx) =
  let[@ocaml.warning "-27-39"] rec map t =
    match t with
    | T.Abs abs ->
        External.Lam ((Ident.to_string abs.var, _), map abs.body)
    | T.App app -> failwith "termx_to_exp: app"
  in
  map tx.data |> [%yojson_of: _] |> json_to_exp
*)
