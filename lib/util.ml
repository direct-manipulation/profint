(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

let pp_to_string pp thing =
  let buf = Buffer.create 19 in
  let out = Stdlib.Format.formatter_of_buffer buf in
  pp out thing ;
  Stdlib.Format.pp_print_flush out () ;
  Buffer.contents buf

let setoff prefix str =
  String.split ~on:'\n' str |>
  List.map ~f:(fun line -> prefix ^ line) |>
  String.concat ~sep:"\n"
