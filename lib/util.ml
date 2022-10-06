(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

module Q = struct
  type 'a t = {
    front : 'a list ;
    back : 'a list ;
    length : int ;
  }
  (* [@@deriving sexp_of] *)
  let empty = { front = [] ; back = [] ; length = 0 }
  let singleton x = { front = [x] ; back = [] ; length = 1 }
  let to_list q = List.append q.front @@ List.rev q.back
  let of_list l =
    let length = List.length l in
    if length < 2 then { front = l ; back = [] ; length } else
    let front, rback = List.split_n l (length / 2) in
    { front ; back = List.rev rback ; length }
  (* let%expect_test "to/of_list" = *)
  (*   let q = of_list [1 ; 2 ; 3] in *)
  (*   to_list q |> List.iter ~f:(Caml.Printf.printf "%d ") ; *)
  (*   [%expect{| 1 2 3 |}] *)
  let equal cmp q1 q2 = List.equal cmp (to_list q1) (to_list q2)
  let length q = q.length
  let size = length
  let cons x q =
    match q.front, q.back with
    | [], [] -> { front = [x] ; back = [] ; length = 1 }
    | [y], [] -> { front = [x] ; back = [y] ; length = 2 }
    | _ -> { q with front = x :: q.front ; length = q.length + 1 }
  (* let%expect_test "cons(1,[2,3])" = *)
  (*   let q = cons 1 @@ of_list [2; 3] in *)
  (*   to_list q |> List.iter ~f:(Caml.Printf.printf "%d ") ; *)
  (*   [%expect{| 1 2 3 |}] *)
  let snoc q x =
    match q.front, q.back with
    | [], [] -> { front = [] ; back = [x] ; length = 1 }
    | [], [y] -> { front = [y] ; back = [x] ; length = 2 }
    | _ -> { q with back = x :: q.back ; length = q.length + 1 }
  (* let%expect_test "snoc([1,2],3)" = *)
  (*   let q = snoc (of_list [1; 2]) 3 in *)
  (*   to_list q |> List.iter ~f:(Caml.Printf.printf "%d ") ; *)
  (*   [%expect{| 1 2 3 |}] *)
  let rev q = { q with front = q.back ; back = q.front }
  let map ~f q = { q with front = List.map ~f q.front ;
                          back = List.map ~f q.back }
  exception Empty
  let take_front_exn q =
    match q.front with
    | x :: front -> begin
        let length = q.length - 1 in
        let q = match front, q.back with
          | _ :: _, _
          | [], ([] | [_]) ->
              { q with front ; length }
          | [], _ ->
              let back, rfront = List.split_n q.back (length / 2) in
              { front = List.rev rfront ; back ; length }
        in x, q
      end
    | [] -> begin
        match q.back with
        | [] -> raise Empty
        | [x] -> x, empty
        | _ -> assert false
      end
  let take_front q =
    try Some (take_front_exn q) with Empty -> None
  let take_back_exn q =
    match q.back with
    | x :: back -> begin
        let length = q.length - 1 in
        let q = match q.front, back with
          | _, (_ :: _)
          | ([] | [_]), [] ->
              { q with back ; length }
          | _, [] ->
              let front, rback = List.split_n q.front (length / 2) in
              { front ; back = List.rev rback ; length }
        in q, x
      end
    | [] -> begin
        match q.front with
        | [] -> raise Empty
        | [x] -> empty, x
        | _ -> assert false
      end
  let take_back q =
    try Some (take_back_exn q) with Empty -> None
  let append q1 q2 =
    List.fold_left ~f:snoc ~init:q1 (to_list q2)
end
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
