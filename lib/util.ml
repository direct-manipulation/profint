(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

let panic___REMOVE =
  (* hiding the exception in a local module to make it impossible to
   * handle except with a catchall handler *)
  let module P = struct
    exception Panic of string
  end in
  fun msg -> raise @@ P.Panic msg

let failwith_s___REMOVE fmt = Printf.ksprintf failwith fmt
let failwith_fmt___REMOVE fmt =
  let buf = Buffer.create 19 in
  let out = Caml.Format.formatter_of_buffer buf in
  Caml.Format.kfprintf (fun _ -> failwith (Buffer.contents buf)) out fmt

let range___REMOVE ~step ~lo ~hi =
  let open Sequence in
  if step > 0 then begin
    let f cur =
      if cur < hi then Step.Yield (cur, cur + step) else Step.Done
    in unfold_step ~init:lo ~f
  end else if step < 0 then begin
    let f cur =
      if cur >= lo then Step.Yield (cur, cur + step) else Step.Done
    in unfold_step ~init:hi ~f
  end else begin
    if lo < hi then Sequence.repeat lo else Sequence.empty
  end

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
