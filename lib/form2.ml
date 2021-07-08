(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util

type bincon = And | Or | Impl
type nulcon = Top | Bot

type 'f skel =
  | Atom of ident
  | Bin  of 'f * bincon * 'f
  | Nul  of nulcon

type form = F of form skel [@@unboxed]

type parity = Even | Odd

let flip = function Even -> Odd | _ -> Even

type ftab = {
  skels : int skel ITab.t ;
  parities : parity ITab.t ;
  parents : int ITab.t ;
}

let next_id =
  let cur_id = ref 0 in
  fun () -> incr cur_id ; !cur_id

let tabulate ?ftab f =
  let ftab = match ftab with
    | None -> { skels = ITab.create 19 ;
                parities = ITab.create 19 ;
                parents = ITab.create 19 }
    | Some ftab -> ftab
  in
  let rec scan (F f) parity =
    let f_id = next_id () in
    ITab.replace ftab.parities f_id parity ;
    let skel = match f with
      | Bin (f1, op, f2) ->
          let f1_id = scan f1 (if op = Impl then flip parity else parity) in
          let f2_id = scan f2 parity in
          ITab.replace ftab.parents f1_id f_id ;
          ITab.replace ftab.parents f2_id f_id ;
          Bin (f1_id, op, f2_id)
      | Nul op ->
          Nul op
      | Atom a ->
          Atom a
    in
    ITab.replace ftab.skels f_id skel ;
    f_id
  in
  (ftab, scan f Even)

let rec untabulate ftab fid =
  let skel = match ITab.find ftab.skels fid with
    | Bin (fid1, op, fid2) ->
        Bin (untabulate ftab fid1, op, untabulate ftab fid2)
    | Nul op ->
        Nul op
    | Atom a ->
        Atom a
  in
  F skel

let pp out (ftab, f_id) =
  let open Format in
  let rec pp_skel out skel =
    match skel with
    | Atom a ->
        pp_print_string out a
    | Nul Top ->
        pp_print_string out "true"
    | Nul Bot ->
        pp_print_string out "false"
    | Bin (f1_id, op, f2_id) -> begin
        let f1 = ITab.find ftab.skels f1_id in
        let f2 = ITab.find ftab.skels f2_id in
        let op_str = match op with
          | And -> " /\\ "
          | Or -> " \\/ "
          | Impl -> " -> "
        in
        fprintf out "@[<b3>(%a %s@ %a)@]"
          pp_skel f1 op_str pp_skel f2
      end
  in
  pp_skel out (ITab.find ftab.skels f_id)

let to_doc_exp prefix ftab root =
  let rec aux id =
    let str = match ITab.find ftab.skels id with
      | Atom a ->
          let a_str = Printf.sprintf "\\mathsf{%s}" a in
          Doc.(Atom (StringAs (String.length a, a_str)))
      | Nul op ->
          let op_str = match op with
            | Top -> Doc.StringAs (1, "\\top")
            | Bot -> Doc.StringAs (1, "\\bot")
          in
          Doc.(Atom op_str)
      | Bin (f1, op, f2) ->
          let op_str, op_prec, op_assoc = match op with
            | And -> Doc.StringAs (1, "\\wedge"), 30, Doc.Left
            | Or -> Doc.StringAs (1, "\\vee"), 20, Doc.Left
            | Impl -> Doc.StringAs (1, "\\supset"), 10, Doc.Right
          in
          Doc.(Appl (op_prec, Infix (op_str, op_assoc, [aux f1 ; aux f2])))
    in
    let id_left = Doc.StringAs (0, Printf.sprintf "\\htmlId{%s%d}{" prefix id) in
    let id_right = Doc.StringAs (0, "}") in
    Doc.(Wrap (Transparent, id_left, str, id_right))
  in
  aux root

type fdiv =
  | Struct of {ident : int ; contents : fdiv list}
  | Text of string

let rec fdiv_to_string prefix = function
  | Struct s ->
      Printf.sprintf "<div id=\"%s-%d\">%s</div>"
        prefix s.ident
        (fdivs_to_string prefix s.contents)
  | Text s -> s
and fdivs_to_string prefix = function
  | [] -> ""
  | fdiv :: fdivs ->
      fdiv_to_string prefix fdiv ^
      fdivs_to_string prefix fdivs

let make_div ftab root =
  let rec make id =
    match ITab.find ftab.skels id with
    | Atom a ->
        Struct {ident = id ; contents = [Text a]}
    | Nul op ->
        let op_str = match op with
          | Top -> "\\top"
          | Bot -> "\\bot"
        in
        Struct {ident = id ; contents = [Text op_str]}
    | Bin (f1_id, op, f2_id) ->
        let op_str = match op with
          | And -> "\\,{\\wedge}\\,"
          | Or -> "\\,{\\vee}\\,"
          | Impl -> "\\,{\\supset}\\,"
        in
        Struct {ident = id ;
                contents = [
                  Text "(" ;
                  make f1_id ;
                  Text op_str ;
                  make f2_id ;
                  Text ")" ;
                ]}
  in
  make root

let f_bin op f g = F (Bin (f, op, g))
let f_impl = f_bin Impl
let f_and = f_bin And
let f_or = f_bin Or
let f_atom a = F (Atom a)
let f_top = F (Nul Top)
let f_bot = F (Nul Bot)

let f = f_impl (f_or (f_and (f_atom "a")
                        (f_impl (f_atom "b") (f_atom "c")))
                  f_bot)
    (f_atom "f")
let (f_tab, f_root) = tabulate f
let show () =
  (f_tab.skels |> ITab.to_seq |> List.of_seq,
   f_tab.parities |> ITab.to_seq |> List.of_seq,
   f_tab.parents |> ITab.to_seq |> List.of_seq)
