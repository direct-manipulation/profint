(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Profint
open! Util
module YS = Yojson.Safe
module M = Map.Make(String)
module S = Set.Make(String)

type mode = Lean3 | Lean4 | Coq | Coq_reflect

let failwithf fmt = Format.kasprintf failwith fmt

let bad_json () = failwithf "Bad JSON"

let rec maybe_concat (json : YS.t) =
  match json with
  | `String str -> str
  | `List jsons -> String.concat " " (List.map maybe_concat jsons)
  | _ -> bad_json ()

include struct
  open Types
  let with_app tm k =
    let rec find_head tm args =
      match tm with
      | U.App (tm, arg) -> find_head tm (arg :: args)
      | U.Kon (id, _) | Var id -> k id args
      | _ -> bad_json ()
    in
    find_head tm []
  let parse_dir dir : Form4.dir =
    with_app dir begin fun k args ->
      match k, args with
      | "l", [] -> `l
      | "r", [] -> `r
      | "d", [] -> `d
      | "i", [Var x] -> `i x
      | _ -> bad_json ()
    end
  let parse_path path : Form4.path =
    with_app path begin fun k args ->
      match k, args with
      | "go", dirs ->
          Q.of_list @@ List.map parse_dir dirs
      | _ -> bad_json ()
    end
  let parse_termx tx =
    let (t, ty) = Uterm.ty_check empty tx in
    let rec abs_to_cx cx t ty =
      match t, ty with
      | T.Abs { var ; body }, Arrow (vty, ty) ->
          with_var cx { var ; ty = vty } (fun _ cx -> abs_to_cx cx body ty)
      | _ -> { tycx = cx ; data = t }
    in
    abs_to_cx empty t ty
  let parse_bool copy =
    with_app copy begin fun k args ->
      match k, args with
      | "t", [] -> true
      | "f", [] -> false
      | _ -> bad_json ()
    end
  let parse_mstep tm =
    with_app tm begin fun k args ->
      match k, args with
      | "P", [] -> Form4.Pristine
      | "C", [path] ->
          let path = parse_path path in
          Form4.Contract { path }
      | "W", [path] ->
          let path = parse_path path in
          Form4.Weaken { path }
      | "I", [path ; term] ->
          let path = parse_path path in
          Form4.Inst { path ; term }
      | "L", [src ; dest ; copy] ->
          let src = parse_path src in
          let dest = parse_path dest in
          let copy = parse_bool copy in
          Form4.Link { src ; dest ; copy }
      | _ -> bad_json ()
    end
end

let process_problem out ~mode ~fname no prob =
  Types.sigma := YS.Util.(prob |> member "sig" |> maybe_concat)
                 |> Uterm.thing_of_string Proprs.signature ;
  let goal = YS.Util.(prob |> member "goal" |> maybe_concat)
             |> Uterm.form_of_string |> Types.triv in
  let msteps = YS.Util.(prob |> member "msteps" |> to_list)
               |> List.map maybe_concat
               |> List.map (Uterm.thing_of_string Proprs.one_term)
               |> List.map parse_mstep in
  let deriv = Form4.compute_derivation goal msteps in
  let module O = (val mode : To.TO) in
  Printf.ksprintf (O.pp_comment out) "problem #%d in %s" (no + 1) fname ;
  O.pp_deriv out (!Types.sigma, deriv)

let process_file out ~mode fname =
  let module O = (val mode : To.TO) in
  O.pp_comment out fname ;
  match Yojson.Safe.from_file fname with
  | `List probs ->
      List.iteri (process_problem out ~mode ~fname) probs
  | _ -> bad_json ()

let main () =
  let sysname = ref "lean4" in
  let mode = ref (module To.Lean4 : To.TO) in
  let system = ref Systems.lean4 in
  let set_mode str =
    begin match str with
    | "lean3" -> system := Systems.lean3
    | "lean4" -> system := Systems.lean4
    | "coq" -> system := Systems.coq
    | "coq_reflect" -> system := Systems.coq_reflect
    | _ -> failwithf "Unknown output format %S" str
    end ;
    sysname := str ;
    mode := To.select str
  in
  let outdir = ref @@ FilePath.concat (Filename.get_temp_dir_name ()) "batch" in
  let set_outdir dir = outdir := FilePath.reduce dir in
  let doit = ref false in
  let opts = Arg.[
      "-format", String set_mode, "FMT Set output format to FMT (coq, coq_reflect, lean3, lean4)" ;
      "-d", String set_outdir, "DIR Set output direcory to DIR" ;
      "-run", Set doit, " ALso run the generated build" ;
    ] |> Arg.align in
  let input_files : string list ref = ref [] in
  let add_input_file fname =
    if List.exists (String.equal fname) !input_files then
      failwithf "Repeated input file %S" fname ;
    input_files := fname :: !input_files
  in
  Arg.parse opts add_input_file @@
  Printf.sprintf "Usage: %s [OPTIONS] file1.json ...\n\nWhere OPTIONS are:"
    (Filename.basename Sys.executable_name) ;
  let buf = Buffer.create 19 in
  let out = Format.formatter_of_buffer buf in
  List.iter (process_file out ~mode:!mode) @@ List.rev !input_files ;
  Format.pp_print_flush out () ;
  let proofs = Buffer.contents buf in
  Systems.serialize_into !outdir !system proofs ;
  if !doit then begin
    let sysdir = Filename.concat !outdir !sysname in
    Printf.eprintf "[DEBUG] CHDIR %s\n%!" sysdir ;
    Sys.chdir sysdir ;
    Printf.eprintf "[DEBUG] CMD %s\n%!" (!system).buildcmd ;
    assert (Sys.command (!system).buildcmd = 0)
  end

let () = main ()
