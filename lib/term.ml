(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util

type ty = {args : ty list ; result : ident}

let arrow ty1 ty2 = {ty2 with args = ty1 :: ty2.args}

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
  | Index n -> ty_lookup cx n
  | Const (_, ty) -> ty

and ty_lookup cx n =
  match cx, n with
  | ty :: _, 0 -> ty
  | _ :: cx, n -> ty_lookup cx (n - 1)
  | [], _ -> type_error "invalid variable"

module GroundTypechcker = struct

let rec ty_check cx term ty =
  match term, ty with
  | Abs f, {args = ty :: args ; result} ->
      let cx = ty :: cx in
      ty_check cx f.body {args ; result}
  | Abs _, _ ->
      type_error "ty_check: abs"
  | App u, _ ->
      let hty = ty_infer cx u.head in
      let rty = ty_check_spine cx u.spine hty.args hty.result in
      if ty <> rty then
        type_error "ty_check: app"

and ty_check_spine cx spine argtys result =
  match spine, argtys with
  | [], _ -> {args = argtys ; result}
  | (term :: spine), (ty :: argtys) ->
      ty_check cx term ty ;
      ty_check_spine cx spine argtys result
  | _ ->
      type_error "ty_check_spine"

end

module LiftedTypechecker = struct

  let prefix = "'"

  let fresh_tyvar =
    let count = ref 0 in
    fun () ->
      incr count ;
      {args = [] ; result = prefix ^ string_of_int !count}

  let rec ty_gen cx term ty =
    match term with
    | Abs f ->
        let tyarg = fresh_tyvar () in
        let tyres = fresh_tyvar () in
        let cx = tyarg :: cx in
        (arrow tyarg tyres, ty) :: ty_gen cx f.body tyres
    | App u ->
        let tyargs = List.map (fun _ -> fresh_tyvar ()) u.spine in
        let tyres = fresh_tyvar () in
        let tyhead = ty_infer cx u.head in
        ({tyres with args = tyargs}, tyhead) :: (tyres, ty) ::
        ty_gen_spine cx u.spine tyargs

  and ty_gen_spine cx spine tyargs =
    match spine, tyargs with
    | [], _ -> []
    | (term :: spine), (ty :: tyargs) ->
        ty_gen cx term ty @
        ty_gen_spine cx spine tyargs
    | _ -> assert false

  (* let solve eqns =
   *   let tab = Hashtbl.create 19 in *)

  let rec occurs x ty =
    x == ty.result || List.exists (occurs x) ty.args

  type ty_ =
    | Arrow of ty * ty
    | Basic of string
    | Var   of string

  let ty_expose ty =
    match ty.args with
    | [] -> begin
        if ty.result.[0] = '\'' then Var ty.result
        else Basic ty.result
      end
    | arg :: args ->
        Arrow (arg, {ty with args})

  let rec ty_to_string ty =
    match ty_expose ty with
    | Basic x | Var x -> x
    | Arrow (tya, tyb) ->
        Printf.sprintf "(%s -> %s)"
          (ty_to_string tya) (ty_to_string tyb)

  let ty_hide ty_ =
    match ty_ with
    | Basic x | Var x -> {args = [] ; result = x}
    | Arrow (ty1, ty2) -> {ty2 with args = ty1 :: ty2.args}

  let rec subst ~tab ty =
    let args = List.map (subst ~tab) ty.args in
    let result =
      match Hashtbl.find tab ty.result with
      | ty -> ty
      | exception Not_found -> {args = [] ; result = ty.result}
    in
    {result with args = args @ result.args}

  let solve1 ~emit ~tab l r =
    match ty_expose l, ty_expose r with
    | Var x, ty_
    | ty_, Var x -> begin
        match Hashtbl.find tab x with
        | other -> emit (ty_hide ty_, other)
        | exception Not_found ->
            let ty = ty_hide ty_ in
            if occurs x ty then type_error "circularity" ;
            Hashtbl.replace tab x ty ;
            Hashtbl.filter_map_inplace (fun _ ty -> Some (subst ~tab ty)) tab
      end
    | Basic a, Basic b when a = b ->
        ()
    | Arrow (la, lb), Arrow (ra, rb) ->
        emit (la, ra) ;
        emit (lb, rb)
    | _ ->
        type_error "tycon mismatch"

  let subst_solved ~tab (l, r) = (subst ~tab l, subst ~tab r)

  let solve eqns =
    let eqns = ref eqns in
    let emit eqn = eqns := eqn :: !eqns in
    let tab = Hashtbl.create 19 in
    let rec spin () =
      match !eqns with
      | [] -> ()
      | (l, r) :: rest ->
          eqns := rest ;
          solve1 ~emit ~tab l r ;
          spin ()
    in
    spin () ;
    tab

  let ty_check cx term =
    let ty = fresh_tyvar () in
    let eqns = ty_gen cx term ty in
    let tab = solve eqns in
    let cx = List.map (subst ~tab) cx in
    let ty = subst ~tab ty in
    (cx, term, ty)
end

module Types = struct
  let basic a = {args = [] ; result = a}
  let arrow ty1 ty2 = {ty2 with args = ty1 :: ty2.args}
end

module Terms = struct
  let ti = Abs {var = "x" ; body = index 0}
  let tk = Abs {var = "x" ;
                body = Abs {var = "y" ;
                            body = index 1}}
  let ts = Abs {var = "x" ;
                body = Abs {var = "y" ;
                            body = Abs {var = "z" ;
                                        body = App {head = Index 2 ;
                                                    spine = [index 0 ;
                                                             App {head = Index 1 ;
                                                                  spine = [index 0]}]}}}}
  let tdelta = Abs {var = "x" ;
                    body = App {head = Index 0 ;
                                spine = [index 0]}}
end


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
