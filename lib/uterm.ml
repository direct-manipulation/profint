(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Untyped terms and types with free variables *)

open Types
open U

exception TypeError of {
    ty : Ty.t option ;
    msg : string ;
  }

let ty_error ?ty fmt =
  Printf.ksprintf (fun msg -> raise (TypeError {ty ; msg})) fmt

let rec tygen ~emit (cx : tycx) tm ty_expected =
  match tm with
  | Idx n -> begin
      match List.nth_opt cx.linear n with
      | Some { ty ; _ } ->
          emit ty ty_expected ; Idx n
      | None ->
          raise @@ TypeError { ty = Some ty_expected ;
                               msg = "Invalid index " ^ Int.to_string n }
    end
  | Var x -> begin
      match tyget cx.linear x with
      | Some (n, ty) ->
          emit ty ty_expected ;
          Idx n
      | None ->
          tygen ~emit cx (Kon (x, None)) ty_expected
    end
  | Kon (k, ty) -> begin
      match lookup_ty k with
      | Some ty_a ->
          emit ty_a ty_expected ;
          Option.iter (emit ty_a) ty ;
          Kon (k, Some ty_a)
      | None ->
          raise @@ TypeError {
            ty = Some ty_expected ;
            msg = "Unknown contstant or variable " ^ (Ident.to_string k)
          }
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
  | tvar :: _ when Ident.equal x tvar.var -> Some (depth, tvar.ty)
  | _ :: cx -> tyget ~depth:(depth + 1) cx x
  | [] -> None

let rec occurs x ty =
  match ty with
  | Ty.Var y -> x = y.id || begin
      match y.subst with
      | None -> false
      | Some ty -> occurs x ty
    end
  | Ty.Basic _ -> false
  | Ty.Arrow (tya, tyb) -> occurs x tya || occurs x tyb

let solve1 ~emit l r =
  match l, r with
  | Ty.Var ({subst = None ; _} as v), ty
  | ty, Ty.Var ({subst = None ; _} as v) ->
      if occurs v.id ty then ty_error "circularity" ;
      v.subst <- Some ty
  | Ty.Var {subst = Some l ; _}, r
  | l, Ty.Var {subst = Some r ; _} ->
      emit (l, r)
  | Ty.Basic a, Ty.Basic b when Ident.equal a b ->
      ()
  | Ty.Arrow (la, lb), Ty.Arrow (ra, rb) ->
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
  | Ty.Basic a -> Ty.Basic a
  | Ty.Arrow (tya, tyb) -> Ty.Arrow (norm_ty tya, norm_ty tyb)
  | Ty.Var v -> begin
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
            (Ident.to_string k) (Ty.to_string ty)
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
          (Ty.to_string ty)

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
  if not @@ Ty.equal ty Ty.o then
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
      match List.nth_opt cx.linear n with
      | Some { var ; _ } -> Doc.(Atom (string (Ident.to_string var)))
      | None ->
          Doc.(Atom (Stdlib.Format.dprintf "`%d" n))
    end
  | Var v
  | Kon (v, None) -> Doc.(Atom (string (Ident.to_string v)))
  | Kon (v, Some ty) ->
      Doc.(Atom (Stdlib.Format.dprintf "@[<hv1>(%s:@,%a)@]"
                   (Ident.to_string v) Ty.pp ty))
  | App (t1, t2) ->
      Doc.(Appl (100, Infix (string " ", Left, [
          uterm_to_exp ~cx t1 ;
          uterm_to_exp ~cx t2
        ])))
  | Abs (var, ty, body) ->
      let ty = Option.value ty ~default:K.ty_any in
      with_var cx { var ; ty } begin fun { var ; ty } cx ->
        let rep =
          Stdlib.Format.dprintf "@[<hv1>[%s:@,%a]@]@ "
            (Ident.to_string var) Ty.pp ty
        in
        Doc.(Appl (1, Prefix (rep, uterm_to_exp ~cx body)))
      end

let pp_uterm cx out ut =
  uterm_to_exp ~cx ut |> Doc.bracket |> Doc.pp out
let uterm_to_string cx ut =
  uterm_to_exp ~cx ut |> Doc.bracket |> Doc.to_string

let rec pp_uterm_ out ut =
  match ut with
  | Idx n -> Stdlib.Format.fprintf out "Idx(%d)" n
  | Var v -> Stdlib.Format.fprintf out "Var(%s)" (Ident.to_string v)
  | Kon (v, None) -> Stdlib.Format.fprintf out "Kon(%s)" (Ident.to_string v)
  | Kon (v, Some ty) -> Stdlib.Format.fprintf out "Kon(%s,%a)" (Ident.to_string v) Ty.pp ty
  | App (t1, t2) -> Stdlib.Format.fprintf out "App(%a,%a)" pp_uterm_ t1 pp_uterm_ t2
  | Abs (v, None, b) -> Stdlib.Format.fprintf out "Lam(%s,%a)" (Ident.to_string v) pp_uterm_ b
  | Abs (v, Some ty, b) -> Stdlib.Format.fprintf out "Lam(%s:%a,%a)" (Ident.to_string v) Ty.pp ty pp_uterm_ b
