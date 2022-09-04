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

exception TypeError of {ty : ty option ; msg : string}

let ty_error ?ty fmt =
  Printf.ksprintf (fun msg -> raise (TypeError {ty ; msg})) fmt

let rec tygen ~emit (cx : tycx) tm ty_expected =
  match tm with
  | Idx n -> begin
      match List.nth cx.linear n with
      | { ty ; _ } ->
          emit ty ty_expected ; Idx n
      | exception Failure _ ->
          raise @@ TypeError { ty = Some ty_expected ;
                               msg = "Invalid index " ^ string_of_int n }
    end
  | Var x -> begin
      match tyget cx.linear x with
      | (n, ty) ->
          emit ty ty_expected ;
          Idx n
      | exception Not_found ->
          tygen ~emit cx (Kon (x, None)) ty_expected
    end
  | Kon (k, ty) -> begin
      match lookup_ty k with
      | ty_a ->
          emit ty_a ty_expected ;
          Option.iter (emit ty_a) ty ;
          Kon (k, Some ty_a)
      | exception Not_found ->
          raise @@ TypeError { ty = Some ty_expected ;
                               msg = "Unknown contstant or variable " ^ k }
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
      with_var cx { var = x ; ty = tyarg } begin fun vty cx ->
        let bod = tygen ~emit cx bod tyres in
        emit (Arrow (tyarg, tyres)) ty_expected ;
        Abs (vty.var, xty, bod)
      end

and tyget ?(depth = 0) cx x =
  match cx with
  | tvar :: _ when x = tvar.var -> (depth, tvar.ty)
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

exception Free_tyvar of { id : int }

let rec norm_ty ty =
  match ty with
  | Basic a -> Basic a
  | Arrow (tya, tyb) -> Arrow (norm_ty tya, norm_ty tyb)
  | Tyvar v -> begin
      match v.subst with
      | None -> raise @@ Free_tyvar { id = v.id }
      | Some ty -> norm_ty ty
    end

let rec norm_term tm =
  match tm with
  | Idx n ->
      T.(App {head = Index n ; spine = []})
  | Kon (k, Some ty) -> begin
      match norm_ty ty with
      | ty -> T.(App {head = Const (k, ty) ; spine = []})
      | exception Free_tyvar _ ->
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
    | exception Free_tyvar _ ->
        ty_error "inferred non-monomorphic type: %s"
          (ty_to_string ty)

exception Parsing of string

let thing_of_string prs str =
  let lb = Lexing.from_string str in
  try prs Prolex.token lb with
  | Proprs.Error -> raise (Parsing "")

let ty_of_string str =
  thing_of_string Proprs.one_ty str
  |> norm_ty

let term_of_string ?(cx = empty) str =
  thing_of_string Proprs.one_term str
  |> ty_check cx

let form_of_string ?(cx = empty) str =
  let t = thing_of_string Proprs.one_form str in
  let f, ty = ty_check cx t in
  if ty <> K.ty_o then
    ty_error "form must have type \\o" ;
  f

let declare_basic k =
  sigma := add_basic !sigma k

let declare_const k str =
  let pty = {nvars = 0 ; ty = ty_of_string str} in
  sigma := add_const !sigma k pty

let rec uterm_to_exp ~cx ut =
  match ut with
  | Idx n -> begin
      match List.nth cx.linear n with
      | { var ; _ } -> Doc.(Atom (String var))
      | exception Failure _ ->
          Doc.(Atom (Fmt (fun out -> Format.fprintf out "`%d" n)))
    end
  | Var v
  | Kon (v, None) -> Doc.(Atom (String v))
  | Kon (v, Some ty) ->
      Doc.(Atom (Fmt (fun out ->
          Format.fprintf out "@[<hv1>(%s:@,%a)@]" v pp_ty ty)))
  | App (t1, t2) ->
      Doc.(Appl (100, Infix (String " ", Left, [
          uterm_to_exp ~cx t1 ;
          uterm_to_exp ~cx t2
        ])))
  | Abs (var, ty, body) ->
      let ty = Option.value ty ~default:K.ty_any in
      with_var cx { var ; ty } begin fun { var ; ty } cx ->
        let rep = Doc.(Fmt (fun out ->
            Format.fprintf out "@[<hv1>[%s:@,%a]@]@ " var pp_ty ty)) in
        Doc.(Appl (1, Prefix (rep, uterm_to_exp ~cx body)))
      end

let pp_uterm cx out ut =
  uterm_to_exp ~cx ut |> Doc.bracket |> Doc.pp_doc out
let uterm_to_string cx ut =
  uterm_to_exp ~cx ut |> Doc.bracket |> Doc.lin_doc

let rec pp_uterm_ out ut =
  match ut with
  | Idx n -> Format.fprintf out "Idx(%d)" n
  | Var v -> Format.fprintf out "Var(%s)" v
  | Kon (v, None) -> Format.fprintf out "Kon(%s)" v
  | Kon (v, Some ty) -> Format.fprintf out "Kon(%s,%a)" v pp_ty ty
  | App (t1, t2) -> Format.fprintf out "App(%a,%a)" pp_uterm_ t1 pp_uterm_ t2
  | Abs (v, None, b) -> Format.fprintf out "Lam(%s,%a)" v pp_uterm_ b
  | Abs (v, Some ty, b) -> Format.fprintf out "Lam(%s:%a,%a)" v pp_ty ty pp_uterm_ b

(* module Test () = struct *)
(*   let () = declare_basic "i" *)
(*   let () = declare_const "p" {| i -> i -> \o |} *)
(*   let () = declare_const "f" {| i -> i -> i |} *)
(*   let t1 = term_of_string {| [x] f x x |} *)
(*   let t2 = term_of_string {| [x, y] f x y |} *)
(*   let t3 = term_of_string {| [x, y] [z:\o] f x (f y x) |} *)
(*   let f1 = form_of_string {| \A [x, y, z] p x (f y z) |} *)
(*   let () = reset_sigma () *)
(* end *)
