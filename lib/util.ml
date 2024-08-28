(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let pp_to_string pp thing =
  let buf = Buffer.create 19 in
  let out = Stdlib.Format.formatter_of_buffer buf in
  pp out thing ;
  Stdlib.Format.pp_print_flush out () ;
  Buffer.contents buf

let setoff prefix str =
  String.split_on_char '\n' str |>
  List.map (fun line -> prefix ^ line) |>
  String.concat "\n"

module Char = struct
  include Char
  let is_digit c = '0' <= c && c <= '9'
  let is_nondigit c = c < '0' || c > '9'
end

module StringMap = Map.Make(String)

module String = struct
  include String

  let find_left_index ?(pos = 0) str selfn =
    if pos >= length str then None else
    if selfn str.[pos] then Some pos else None

  let drop_prefix str pos = sub str pos (length str - pos)
end

module List = struct
  include List

  let rec last = function
    | [] -> raise Not_found
    | [x] -> x
    | _ :: l -> last l

  let take n l =
    let rec spin h n l =
      match l with
      | x :: l when n > 0 ->
          spin (x :: h) (n - 1) l
      | _ ->
          (List.rev h, l)
    in
    spin [] n l

  let chunks_of len l =
    let rec spin chs n l =
      if n <= len then List.rev @@ l :: chs else
      let (ch, l) = take len l in
      spin (ch :: chs) (n - len) l
    in
    spin [] (length l) l
end
