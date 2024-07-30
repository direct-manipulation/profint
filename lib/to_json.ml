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
    | Eq     of term * term * ty
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

  type derivation = {
    endf : form ;
    rules : scheme list ;
  } [@@deriving yojson]
end

exception Conversion

let of_ty (ty : Ty.t) : External.ty =
  let rec map ty =
    match Ty.norm_exn ty with
    | Ty.Basic a -> External.Basic (Ident.to_string a)
    | Ty.Arrow (a, b) -> External.Arrow (map a, map b)
    | Ty.Var _ -> assert false
  in
  map ty

let yojson_of_ty ty = of_ty ty |> [%yojson_of: External.ty]

let pp_ty ppf (ty : Ty.t) = yojson_of_ty ty |> Json.pretty_print ppf

let of_termx ty (tx : T.term incx) : External.term =
  let rec map tycx t ty =
    match t, Ty.norm_exn ty with
    | T.Abs abs, Ty.Arrow (tya, tyb) ->
        let vty = Types.{ var= abs.var ; ty = tya } in
        with_var tycx vty begin fun vty tycx ->
          External.Lam ((Ident.to_string vty.var, of_ty vty.ty), map tycx abs.body tyb)
        end
    | T.App app, _ -> begin
        let hty = map_head tycx app.head in
        let (t, _) = Stdlib.List.fold_left begin fun (h, tyh) a ->
            match Ty.norm_exn tyh with
            | Ty.Arrow (tya, tyh) ->
                (External.App (h, map tycx a tya), tyh)
            | _ -> raise Conversion
          end hty app.spine
        in
        t
      end
    | _ -> raise Conversion
  and map_head tycx h =
    match h with
    | T.Const (k, ty) -> (External.Const (Ident.to_string k), ty)
    | T.Index n -> begin
        let ty = match List.nth tycx.linear n with
          | Some { ty ; _ } -> ty
          | None -> raise Conversion
        in
        (External.Bvar n, ty)
      end
  in
  map tx.tycx tx.data ty

let yojson_of_termx ty tx = of_termx ty tx |> [%yojson_of: External.term]

let pp_termx ty ppf (tx : T.term incx) = yojson_of_termx ty tx |> Json.pretty_print ppf

let of_formx (fx : Form4.formx) : External.form =
  let rec map fx =
    match Form4.expose fx.data with
    | Form4.Atom (T.App { head = T.Const (p, ty) ; spine }) -> begin
        let (args, _) = Stdlib.List.fold_left begin fun (args, ty) arg ->
            match Ty.norm_exn ty with
            | Ty.Arrow (tya, ty) ->
                let arg = of_termx tya (arg |@ fx) in
                (arg :: args, ty)
            | _ -> raise Conversion
          end ([], ty) spine in
        let args = List.rev args in
        External.Atom (Ident.to_string p, args)
      end
    | Form4.Eq (s, t, ty) ->
        let s = of_termx ty (s |@ fx) in
        let t = of_termx ty (t |@ fx) in
        let ty = of_ty ty in
        External.Eq (s, t, ty)
    | Form4.And (f, g) ->
        let f = map (f |@ fx) in
        let g = map (g |@ fx) in
        External.And (f, g)
    | Form4.Top -> External.True
    | Form4.Or (f, g) ->
        let f = map (f |@ fx) in
        let g = map (g |@ fx) in
        External.Or (f, g)
    | Form4.Bot -> External.False
    | Form4.Imp (f, g) ->
        let f = map (f |@ fx) in
        let g = map (g |@ fx) in
        External.Imp (f, g)
    | Form4.Forall (vty, f) ->
        with_var fx.tycx vty begin fun vty tycx ->
          let f = map { tycx ; data = f } in
          let ty = of_ty vty.ty in
          External.Forall ((Ident.to_string vty.var, ty), f)
        end
    | Form4.Exists (vty, f) ->
        with_var fx.tycx vty begin fun vty tycx ->
          let f = map { tycx ; data = f } in
          let ty = of_ty vty.ty in
          External.Exists ((Ident.to_string vty.var, ty), f)
        end
    | Form4.Atom _ | Form4.Mdata _ ->
        failwith "unfinished"
  in
  map fx

let yojson_of_formx fx = of_formx fx |> [%yojson_of: External.form]
let pp_formx ppf fx = yojson_of_formx fx |> Json.pretty_print ppf

let of_path (p : Path.t) : External.Position.t =
  Path.to_list p |>
  Stdlib.List.map begin function
  | Path.Dir.L -> 0
  | _ -> 1
  end |>
  External.Position.of_list

let of_deriv (_sigma, (cd : Form4.Cos.deriv)) =
  let endf = of_formx cd.bottom in
  let rules =
    List.rev cd.middle |>
    Stdlib.List.map begin fun (_, (rule : Form4.Cos.rule), _) ->
      let pos = of_path rule.path in
      (* let ({ tycx ; _ }, _) = Form4.Paths.formx_at concl rule.path in *)
      let rule : External.rule = match rule.name with
        | Goal_ts_imp { pick = L }                -> Cos_goal_ts_imp_l
        | Goal_ts_imp { pick = R }                -> Cos_goal_ts_imp_r
        | Goal_imp_ts                             -> Cos_goal_imp_ts
        | Goal_ts_and { pick = L }                -> Cos_goal_ts_and_l
        | Goal_ts_and { pick = R }                -> Cos_goal_ts_and_r
        | Goal_and_ts { pick = L }                -> Cos_goal_and_ts_l
        | Goal_and_ts { pick = R }                -> Cos_goal_and_ts_r
        | Goal_ts_or { pick = L }                 -> Cos_goal_ts_or_l
        | Goal_ts_or { pick = R }                 -> Cos_goal_ts_or_r
        | Goal_or_ts                              -> Cos_goal_or_ts
        | Goal_ts_all                             -> Cos_goal_ts_all
        | Goal_all_ts                             -> Cos_goal_all_ts
        | Goal_ts_ex                              -> Cos_goal_ts_ex
        | Goal_ex_ts                              -> Cos_goal_ex_ts
        | Init                                    -> Cos_init
        | Rewrite { from = L }                    -> Cos_rewrite_ltr
        | Rewrite { from = R }                    -> Cos_rewrite_rtl
        | Asms_and { minor = L ; pick = L }       -> Cos_asms_and_l_l
        | Asms_and { minor = L ; pick = R }       -> Cos_asms_and_l_r
        | Asms_and { minor = R ; pick = L }       -> Cos_asms_and_r_l
        | Asms_and { minor = R ; pick = R }       -> Cos_asms_and_r_r
        | Asms_or { minor = L ; pick = L }        -> Cos_asms_or_l_l
        | Asms_or { minor = L ; pick = R }        -> Cos_asms_or_l_r
        | Asms_or { minor = R ; pick = L }        -> Cos_asms_or_r_l
        | Asms_or { minor = R ; pick = R }        -> Cos_asms_or_r_r
        | Asms_imp { minor = L ; pick = L }       -> Cos_asms_imp_l_l
        | Asms_imp { minor = L ; pick = R }       -> Cos_asms_imp_l_r
        | Asms_imp { minor = R ; pick = L }       -> Cos_asms_imp_r_l
        | Asms_imp { minor = R ; pick = R }       -> Cos_asms_imp_r_r
        | Asms_all { minor = L }                  -> Cos_asms_all_l
        | Asms_all { minor = R }                  -> Cos_asms_all_r
        | Asms_ex { minor = L }                   -> Cos_asms_ex_l
        | Asms_ex { minor = R }                   -> Cos_asms_ex_r
        | Simp_and_top { cxkind = L ; minor = L } -> Cos_simp_asms_and_top
        | Simp_and_top { cxkind = L ; minor = R } -> Cos_simp_asms_top_and
        | Simp_and_top { cxkind = R ; minor = L } -> Cos_simp_goal_and_top
        | Simp_and_top { cxkind = R ; minor = R } -> Cos_simp_goal_top_and
        | Simp_or_top { cxkind = L ; minor = L }  -> Cos_simp_asms_or_top
        | Simp_or_top { cxkind = L ; minor = R }  -> Cos_simp_asms_top_or
        | Simp_or_top { cxkind = R ; minor = L }  -> Cos_simp_goal_or_top
        | Simp_or_top { cxkind = R ; minor = R }  -> Cos_simp_goal_top_or
        | Simp_imp_top { cxkind = L ; minor = L } -> Cos_simp_asms_imp_top
        | Simp_imp_top { cxkind = L ; minor = R } -> Cos_simp_asms_top_imp
        | Simp_imp_top { cxkind = R ; minor = L } -> Cos_simp_goal_imp_top
        | Simp_imp_top { cxkind = R ; minor = R } -> Cos_simp_goal_top_imp
        | Simp_all_top { cxkind = L }             -> Cos_simp_asms_all_top
        | Simp_all_top { cxkind = R }             -> Cos_simp_goal_all_top
        | Simp_and_bot { cxkind = L ; minor = L } -> Cos_simp_asms_and_bot
        | Simp_and_bot { cxkind = L ; minor = R } -> Cos_simp_asms_bot_and
        | Simp_and_bot { cxkind = R ; minor = L } -> Cos_simp_goal_and_bot
        | Simp_and_bot { cxkind = R ; minor = R } -> Cos_simp_goal_bot_and
        | Simp_or_bot { cxkind = L ; minor = L }  -> Cos_simp_asms_or_bot
        | Simp_or_bot { cxkind = L ; minor = R }  -> Cos_simp_asms_bot_or
        | Simp_or_bot { cxkind = R ; minor = L }  -> Cos_simp_goal_or_bot
        | Simp_or_bot { cxkind = R ; minor = R }  -> Cos_simp_goal_bot_or
        | Simp_bot_imp { cxkind = L }             -> Cos_simp_asms_bot_imp
        | Simp_bot_imp { cxkind = R }             -> Cos_simp_goal_bot_imp
        | Simp_ex_bot { cxkind = L }              -> Cos_simp_asms_ex_bot
        | Simp_ex_bot { cxkind = R }              -> Cos_simp_goal_ex_bot
        | Congr                                   -> Cos_congr
        | Contract                                -> Cos_contract
        | Weaken                                  -> Cos_weaken
        | Inst { side = L ; term ; ty }           -> Cos_inst_l (of_termx ty term)
        | Inst { side = R ; term ; ty }           -> Cos_inst_r (of_termx ty term)
        | Rename _ -> raise Conversion
      in
      External.{ pos ; rule }
    end in
  External.{ endf ; rules }

let yojson_of_deriv sd = of_deriv sd |> [%yojson_of: External.derivation]
let pp_deriv ppf sd = yojson_of_deriv sd |> Json.pretty_print ppf

let pp_sigma _ppf _sigm = ()

let pp_header _ppf () = ()
let pp_footer _ppf () = ()
let pp_comment _ppf _com = ()

let name = "json"
let files pf = [
  File { fname = "proof.json" ; contents = pf } ;
]
let build () = "echo Run: tond -t proof.tex proof.json"
