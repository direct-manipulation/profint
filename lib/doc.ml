(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

type box =
  | NOBOX
  | H | V of int | HV of int | HOV of int

type doc =
  | String of string
  | StringAs of int * string
  | Fmt of (Caml.Format.formatter -> unit)
  | Break of int * int
  | Group of box * doc list
  | Newline

let space n = Break (n, 0)
let cut = Break (0, 0)

let rec doc_map_strings fn = function
  | String s -> fn ~elen:(String.length s) s
  | StringAs (elen, s) -> fn ~elen s
  | Group (b, ds) -> Group (b, List.map ~f:(doc_map_strings fn) ds)
  | (Fmt _ | Break _ | Newline) as d -> d

let rec pp_doc ff = function
  | String s ->
      Caml.Format.pp_print_string ff s
  | StringAs (n, s) ->
      Caml.Format.pp_print_as ff n s
  | Fmt fmt -> fmt ff
  | Break (nsp, offs) ->
      Caml.Format.pp_print_break ff nsp offs
  | Group (b, ds) ->
      begin match b with
      | NOBOX -> ()
      | H -> Caml.Format.pp_open_hbox ff ()
      | V ind -> Caml.Format.pp_open_vbox ff ind
      | HV ind -> Caml.Format.pp_open_hvbox ff ind
      | HOV ind -> Caml.Format.pp_open_hovbox ff ind
      end ;
      List.iter ~f:(pp_doc ff) ds ;
      begin match b with
      | NOBOX -> ()
      | _ -> Caml.Format.pp_close_box ff ()
      end
  | Newline ->
      Caml.Format.pp_force_newline ff ()

let lin_doc_buffer buf d =
  let out = Caml.Format.formatter_of_buffer buf in
  let rec output = function
    | String s | StringAs (_, s) ->
        Caml.Format.pp_print_string out s
    | Fmt fmt ->
        Caml.Format.fprintf out "%t" fmt
    | Group (_, ds) ->
        List.iter ~f:output ds
    | Break (0, _) -> ()
    | Break _ | Newline ->
        Caml.Format.pp_print_char out ' '
  in
  output d ;
  Caml.Format.pp_print_flush out ()

let lin_doc d =
  let buf = Buffer.create 10 in
  lin_doc_buffer buf d ;
  Buffer.contents buf

let pp_lin_doc out d =
  lin_doc d |> Caml.Format.pp_print_string out

type wrapping = Transparent | Opaque

type exp =
  | Atom of doc
  | Wrap of wrapping * doc * exp * doc
  | Appl of int * bappl

and bappl =
  | Prefix of doc * exp
  | Postfix of doc * exp
  | Infix of doc * assoc * exp list

and assoc = Left | Right | Non

let rec ( >=? ) prec be = match be with
  | Appl (subprec, _) when prec >= subprec -> true
  | Wrap (Transparent, _, be, _) -> prec >=? be
  | _ -> false

(* let rec ( >? ) prec be = match be with
 *   | Atom _ -> false
 *   | Wrap (_, _, be, _) -> prec >? be
 *   | _ -> true *)

let rec ( >? ) prec be = match be with
  | Appl (subprec, _) when prec > subprec -> true
  | Wrap (Transparent, _, be, _) -> prec >? be
  | _ -> false

let rec is_prefix = function
  | Appl (_, Prefix _) -> true
  | Wrap (Transparent, _, be, _) -> is_prefix be
  | _ -> false

let rec is_postfix = function
  | Appl (_, Postfix _) -> true
  | Wrap (Transparent, _, be, _) -> is_postfix be
  | _ -> false

let rec infix_incompat_for tasc pr asc = function
  | Appl (spr, (Prefix _ | Postfix _))
    when pr >= spr -> true
  | Appl (spr, Infix (_, sasc, _))
    when pr = spr && not (Poly.(asc = tasc) && Poly.(sasc = tasc)) -> true
  | Wrap (Transparent, _, be, _) ->
      infix_incompat_for tasc pr asc be
  | _ -> false

type dinfo = PRE of int | POST of int | NVM

let rec reprec e =
  begin match e with
  | Atom _ -> (e, NVM)
  | Appl (p, Infix (d, asc, es)) ->
      let es = List.map ~f:(fun e -> fst (reprec e)) es in
      (Appl (p, Infix (d, asc, es)), NVM)
  | Appl (p, Prefix (d, e)) ->
      begin
        let (e, di) = reprec e in
        let p = begin match di with
          | PRE q -> min p q
          | _ -> p
        end in
        (Appl (p, Prefix (d, e)), PRE p)
      end
  | Appl (p, Postfix (d, e)) ->
      begin
        let (e, di) = reprec e in
        let p = begin
          match di with
          | POST q -> min p q
          | _ -> p
        end in
        (Appl (p, Postfix (d, e)), POST p)
      end
  | Wrap (wt, b, e, a) ->
      let (e, di) = reprec e in
      let di = begin match wt with
        | Transparent -> di
        | Opaque -> NVM
      end in
      (Wrap (wt, b, e, a), di)
  end

let delimit ?(cond=true) ~ld ~rd d =
  if not cond then d else Group (H, [ld ; d ; rd])

let rec bracket ~ld ~rd = function
  | Atom d -> d
  | Wrap (_, ld1, be, rd1) ->
      delimit ~ld:ld1 ~rd:rd1 (bracket ~ld ~rd be)
  | Appl (prec, appl) -> begin
      match appl with
      | Prefix (oprep, be) ->
          let opd = bracket ~ld ~rd be in
          Group begin HOV 2, [
              oprep ;
              delimit opd ~ld ~rd
                ~cond:(prec >? be && not (is_prefix be)) ;
            ] end
      | Postfix (oprep, be) ->
          let opd = bracket ~ld ~rd be in
          Group begin H, [
              delimit opd ~ld ~rd
                ~cond:(prec >? be && not (is_postfix be)) ;
              oprep
            ] end
      | Infix (oprep, asc, l :: es) ->
          let ms, r = match List.rev es with
            | r :: rms -> List.rev rms, r
            | [] -> invalid_arg "bracket"
          in
          let l = delimit (bracket ~ld ~rd l) ~ld ~rd
              ~cond:(prec >? l
                     || infix_incompat_for Left prec asc l) in
          let r = delimit (bracket ~ld ~rd r) ~ld ~rd
              ~cond:(prec >? r
                     || infix_incompat_for Right prec asc r) in
          let ms = List.map
              ~f:begin fun e ->
                [oprep ; delimit (bracket ~ld ~rd e) ~ld ~rd ~cond:(prec >=? e)]
              end ms in
          let ms = List.concat ms in
          Group (HOV 0, l :: ms @ [oprep ; r])
      | Infix (_, _, []) -> invalid_arg "bracket"
    end

let bracket ?(ld = String "(") ?(rd = String ")") e =
  let (e, _) = reprec e in
  bracket ~ld ~rd e
