(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

type bincon = And | Or | Impl
type nulcon = Top | Bot

type form_ =
  | Atom of Idt.t
  | Bin  of form * bincon * form
  | Nul  of nulcon

and form = {
  skel : form_ ;
  id   : int ;
  hkey : int ;
}

module FormHashEq = struct
  type t = form
  let equal_ f1 f2 =
    match f1, f2 with
    | Atom a, Atom b ->
        a == b
    | Bin (f1, op1, f2), Bin (g1, op2, g2) ->
        op1 == op2 && f1 == g1 && f2 == g2
    | Nul op1, Nul op2 ->
        op1 == op2
    | _ -> false
  let equal f1 f2 = equal_ f1.skel f2.skel
  let hash_ f =
    match f with
    | Atom a -> a.idx
    | Bin (f1, op, f2) ->
        let h = Stdlib.Hashtbl.hash op in
        let h = 19 * f1.hkey + h in
        let h = 19 * f2.hkey + h in
        Stdlib.abs (h + 1)
    | Nul op ->
        Stdlib.abs (19 * Stdlib.Hashtbl.hash op + 2)
  let hash f = f.hkey
  let compare f1 f2 = Stdlib.Int.compare f1.id f2.id
end

let make_form =
  let module FormHC = Stdlib.Weak.Make(FormHashEq) in
  let tab = FormHC.create 251 in
  let count = ref 0 in
  fun skel ->
    let hkey = FormHashEq.hash_ skel in
    incr count ;
    let id = !count in
    let f = FormHC.merge tab { skel ; hkey ; id } in
    if f.id != id then decr count ;
    f

module FormSet : Stdlib.Set.S with type elt := form =
  Stdlib.Set.Make(FormHashEq)
module FormTab : Stdlib.Hashtbl.S with type key := form =
  Stdlib.Hashtbl.Make(FormHashEq)

let f_atom a     = make_form @@ Atom a
let f_and f g    = make_form @@ Bin (f, And, g)
let f_top ()     = make_form @@ Nul Top
let f_or f g     = make_form @@ Bin (f, Or, g)
let f_bot ()     = make_form @@ Nul Bot
let f_impl f g   = make_form @@ Bin (f, Impl, g)
let f_bin f op g = make_form @@ Bin (f, op, g)

type slice =
  | BinL of bincon * form
  | BinR of form * bincon

type parity = Even | Odd

let flip = function Even -> Odd | Odd -> Even

type fpath = {
  context : slice list ;
  form : form ;
  flips : int ;
}

let fpath form = {context = [] ; form ; flips = 0}

let down step fp =
  match step, fp.form.skel with
  | 1, Bin (fl, op, form) ->
      {fp with
       form ;
       context = BinR (fl, op) :: fp.context}
  | 0, Bin (form, op, fr) ->
      let flips = match op with
        | Impl -> fp.flips + 1
        | _ -> fp.flips
      in
      {form ; flips ;
       context = BinL (op, fr) :: fp.context}
  | n, _ ->
      Printf.ksprintf failwith "invalid operand %d" n

let up fp =
  match fp.context with
  | BinL (op, fr) :: context ->
      let flips = match op with
        | Impl -> fp.flips + 1
        | _ -> fp.flips
      in
      let form = f_bin fp.form op fr in
      {form ; flips ; context}
  | BinR (fl, op) :: context ->
      let form = f_bin fl op fp.form in
      {fp with form ; context}
  | [] ->
      failwith "cannot go up"

let rec unfpath fp =
  match fp.context with
  | [] -> begin
      match fp.flips with
      | 0 -> fp.form
      | _ -> failwith "invalid parity"
    end
  | _ -> unfpath (up fp)

(*

type parity = Even | Odd

let flip = function Even -> Odd | Odd -> Even

type path = int list

exception Invalid_path of {
    parity : parity ;
    form : form ;
    step : int ;
    msg : string
  }

let invalid_pathf ~parity ~form ~step fmt =
  Format.ksprintf begin fun msg ->
    raise @@ Invalid_path { parity ; form ; step ; msg }
  end fmt

let down ?(parity=Even) step form =
  match step, form.skel with
  | 1, (And (_, form) | Or (_, form) | Impl (_, form)) ->
      (parity, form)
  | 0, (And (form, _) | Or (form, _)) ->
      (parity, form)
  | 0, Impl (form, _) ->
      (flip parity, form)
  | n, _ ->
      invalid_pathf ~parity ~step ~form
        "invalid operand number %d" n

let rec at ?(parity=Even) ~path form =
  match path with
  | [] -> (form, parity)
  | step :: path ->
      let (parity, form) = down ~parity step form in
      at ~parity ~path form

type fpath = {
  form : form ;
  path : path ;
}

let fpath form path = {form ; path}

exception Resolution_failure of {
    lfp : fpath ;
    rfp : fpath ;
    parity : parity ;
    msg : string ;
  }

let resolution_failure ~parity ~lfp ~rfp fmt =
  Printf.ksprintf begin fun msg ->
    raise @@ Resolution_failure { parity ; lfp ; rfp ; msg }
  end fmt

let rec resolve_cx lfp rfp =
  match lfp.form.skel, rfp.form.skel with
  | Atom a, Atom b when a = b ->
      assert (lfp.path = [] && rfp.path = []) ;
      f_top ()
  | _ when lfp.path = [] && rfp.path = [] ->
      f_impl lfp.form rfp.form
  | Or (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          f_and
            (resolve_cx (fpath f1 lpath) rfp)
            (f_impl f2 rfp.form)
      | 1 :: lpath ->
          f_and
            (f_impl f1 rfp.form)
            (resolve_cx (fpath f2 lpath) rfp)
      | _ -> assert false
    end
  | Bot, _ -> f_top ()
  | _, Impl (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_impl
            (resolve_ax lfp (fpath g1 rpath))
            g2
      | 1 :: rpath ->
          f_impl g1 (resolve_cx lfp (fpath g2 rpath))
      | _ -> assert false
    end
  | _, And (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_and g1 (resolve_cx lfp (fpath g2 rpath))
      | 1 :: rpath ->
          f_and (resolve_cx lfp (fpath g1 rpath)) g2
      | _ -> assert false
    end
  | _, Top -> f_top ()
  | _, Or (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          resolve_cx lfp (fpath g2 rpath)
      | 1 :: rpath ->
          resolve_cx lfp (fpath g1 rpath)
      | _ -> assert false
    end
  | And (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          resolve_cx (fpath f1 lpath) rfp
      | 1 :: lpath ->
          resolve_cx (fpath f2 lpath) rfp
      | _ -> assert false
    end
  | Impl (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 1 :: lpath ->
          f_and f1 (resolve_cx (fpath f2 lpath) rfp)
      | _ -> assert false
    end
  | _ -> assert false

and resolve_ax lfp rfp =
  match lfp.form.skel, rfp.form.skel with
  | _, Top -> lfp.form
  | _, And (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_and (resolve_ax lfp (fpath g1 rpath)) g2
      | 1 :: rpath ->
          f_and g1 (resolve_ax lfp (fpath g2 rpath))
      | _ -> assert false
    end
  | Top, _ -> rfp.form
  | And (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          f_and (resolve_ax (fpath f1 lpath) rfp) f2
      | 1 :: lpath ->
          f_and f1 (resolve_ax (fpath f2 lpath) rfp)
      | _ -> assert false
    end
  | _, Or (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_or (resolve_ax lfp (fpath g1 rpath)) g2
      | 1 :: rpath ->
          f_or g1 (resolve_ax lfp (fpath g2 rpath))
      | _ -> assert false
    end
  | Or (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          f_or (resolve_ax (fpath f1 lpath) rfp) f2
      | 1 :: lpath ->
          f_or f1 (resolve_ax (fpath f2 lpath) rfp)
      | _ -> assert false
    end
  | _, Impl (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_impl (resolve_ax lfp (fpath g1 rpath)) g2
      | 1 :: rpath ->
          f_impl g1 (resolve_cx lfp (fpath g2 rpath))
      | _ -> assert false
    end
  | Impl (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          f_impl (resolve_ax (fpath f1 lpath) rfp) f2
      | 1 :: lpath ->
          f_impl f1 (resolve_cx rfp (fpath f2 lpath))
      | _ -> assert false
    end
  | _ -> assert false

*)
