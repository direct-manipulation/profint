(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Untyped terms and types with free variables *)

open! Util
open! Types
open! U

(* The constructors of uty need to be in the same order as in Term.ty;
   otherwise we will not get the O(1) transformations. *)

let fresh_tyvar =
  let count = ref 0 in
  fun () ->
    incr count ;
    Tyvar {id = !count ; subst = None}

let rec map_on_tyvars tab uty =
  match uty with
  | Arrow (utya, utyb) ->
      Arrow (map_on_tyvars tab utya, map_on_tyvars tab utyb)
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
  map_on_tyvars tab pty.ty

exception TypeError of {ty : ty option ; msg : string}

let ty_error ?ty fmt =
  Printf.ksprintf (fun msg -> raise (TypeError {ty ; msg})) fmt

let local_sig : poly_ty IdMap.t ref = ref IdMap.empty

let rec tygen ~emit (cx : cx) tm ty_expected =
  match tm with
  | Idx n ->
      emit (snd (List.nth cx n)) ty_expected ;
      Idx n
  | Var x -> begin
      match tyget cx x with
      | (n, ty) ->
          emit ty ty_expected ;
          Idx n
      | exception Not_found ->
          tygen ~emit cx (Kon (x, None)) ty_expected
    end
  | Kon (k, Some ty) ->
      emit ty ty_expected ;
      Kon (k, Some ty)
  | Kon (k, None) -> begin
      match lookup k !local_sig with
      | pty ->
          emit (freshen pty) ty_expected ;
          Kon (k, Some ty_expected)
      | exception Not_found ->
          (* ty_error "unknown constant %s" k *)
          let ty = fresh_tyvar () in
          emit ty ty_expected ;
          Kon (k, Some ty)
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
  | [] -> raise Not_found

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

let rec norm_ty ty =
  match ty with
  | Basic a -> Basic a
  | Arrow (tya, tyb) -> Arrow (norm_ty tya, norm_ty tyb)
  | Tyvar v -> begin
      match v.subst with
      | None -> raise Not_found
      | Some ty -> norm_ty ty
    end

let rec norm_term tm =
  match tm with
  | Idx n ->
      T.(App {head = Index n ; spine = []})
  | Kon (k, Some ty) -> begin
      match norm_ty ty with
      | ty -> T.(App {head = Const (k, ty) ; spine = []})
      | exception Not_found ->
          ty_error "inferred non-monomorphic type for %s: %s"
            k (ty_to_string ty)
    end
  | App (tm, tn) ->
      Term.(do_app (norm_term tm) [norm_term tn])
  | Abs (x, _, tm) ->
      T.(Abs {var = x ; body = norm_term tm})
  | Var _ | Kon (_, None) ->
      assert false

let ty_check cx term =
  let ty = fresh_tyvar () in
  let eqns = ref [] in
  let emit tya tyb = eqns := (tya, tyb) :: !eqns in
  let term = tygen ~emit cx term ty in
  solve !eqns ;
  match norm_ty ty with
    | ty -> (norm_term term, ty)
    | exception Not_found ->
        ty_error "inferred non-monomorphic type: %s"
          (ty_to_string ty)

exception Parsing of string

let thing_of_string prs str =
  let lb = Lexing.from_string str in
  try
    let t = prs Prolex.token lb in
    t
  with
  | Proprs.Error -> raise (Parsing "")

let ty_of_string str =
  thing_of_string Proprs.one_ty str
  |> norm_ty

let term_of_string ?(cx = []) str =
  thing_of_string Proprs.one_term str
  |> ty_check cx

let form_of_string ?(cx = []) str =
  let t = thing_of_string Proprs.one_form str in
  let f, ty = ty_check cx t in
  if ty <> ty_o then
    ty_error "form must have type \\o" ;
  f

let declare_const k str =
  let pty = {nvars = 0 ; ty = ty_of_string str} in
  local_sig := IdMap.add k pty !local_sig

(* module Test = struct
 *   let () = declare_const "p" {| \i -> \i -> \o |} ;;
 *   let () = declare_const "f" {| \i -> \i -> \i |} ;;
 *   let t1 = term_of_string {| [x] f x x |}
 *   let t2 = term_of_string {| [x, y] f x y |}
 *   let t3 = term_of_string {| [x, y] [z:\o] f x (f y x) |}
 *   let f1 = form_of_string {| \A [x, y, z] p x (f y z) |}
 *   let () = local_sig := IdMap.empty
 * end *)
