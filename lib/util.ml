(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

module Q = CCFQueue
type 'a q = 'a Q.t

let pp_to_string pp thing =
  let buf = Buffer.create 19 in
  let out = Caml.Format.formatter_of_buffer buf in
  pp out thing ;
  Caml.Format.pp_print_flush out () ;
  Buffer.contents buf

let setoff prefix str =
  String.split ~on:'\n' str |>
  List.map ~f:(fun line -> prefix ^ line) |>
  String.concat ~sep:"\n"

let read_all ic =
  let len = 64 in
  let byte_buf = Bytes.create len in
  let buf = Buffer.create 19 in
  let rec spin () =
    match Stdlib.input ic byte_buf 0 len with
    | 0 -> ()                   (* EOF reached *)
    | n ->
        Buffer.add_subbytes buf byte_buf ~pos:0 ~len:n ;
        spin ()
  in
  spin () ; Buffer.contents buf
