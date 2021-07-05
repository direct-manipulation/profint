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
