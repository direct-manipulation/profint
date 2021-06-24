open Syntax

type ty = {args : ty list ; result : ident}

type term =
  | Abs of {var : ident ; body : term}
  | App of {head : head ; spine : term list}

and head =
  | Const of ident * ty
  | Index of int

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
  | _ :: cx, n -> ty_lookup cx n
  | [], _ -> type_error "invalid variable"

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

module Test = struct
  let basic a = {args = [] ; result = a}
  let arrow ty1 ty2 = {ty2 with args = ty1 :: ty2.args}
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
