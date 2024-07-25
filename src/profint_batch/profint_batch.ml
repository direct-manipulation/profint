(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Base

open! Profint
open! Util
open! Types
module YS = Yojson.Safe

let failwithf fmt = Stdlib.Format.kasprintf failwith fmt

let bad_json () = failwithf "Bad JSON"

let rec maybe_concat (json : YS.t) =
  match json with
  | `String str -> str
  | `List jsons ->
      String.concat ~sep:" "
        (List.map ~f:maybe_concat jsons)
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
      match Ident.to_string k, args with
      | "l", [] -> Path.Dir.L
      | "r", [] -> R
      | _ -> bad_json ()
    end
  let parse_path path : Form4.path =
    with_app path begin fun k args ->
      match Ident.to_string k, args with
      | "go", dirs ->
          Path.of_list @@ List.map ~f:parse_dir dirs
      | _ -> bad_json ()
    end
  let parse_bool copy =
    with_app copy begin fun k args ->
      match Ident.to_string k, args with
      | "t", [] -> true
      | "f", [] -> false
      | _ -> bad_json ()
    end
  let parse_mstep tm =
    with_app tm begin fun k args ->
      match Ident.to_string k, args with
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


let serialize_into outdir system thing =
  let module T = (val system : Profint.To.TO) in
  let rec aux cwd t =
    match t with
    | File { fname ; contents } ->
        let fname = Stdlib.Filename.concat cwd fname in
        let oc = Stdlib.open_out_bin fname in
        Stdlib.output_string oc contents ;
        Stdlib.close_out oc
    | Dir { dname ; contents } ->
        let cwd = Stdlib.Filename.concat cwd dname in
        FileUtil.mkdir ~parent:true cwd ;
        List.iter ~f:(aux cwd) contents
  in
  let outdir = Stdlib.Filename.concat outdir T.name in
  FileUtil.mkdir ~parent:true outdir ;
  let dirtree = T.files thing in
  List.iter ~f:(aux outdir) dirtree ;
  outdir

let process_problem out ~mode ~fname no prob =
  Types.sigma := YS.Util.(prob |> member "sig" |> maybe_concat)
                 |> Uterm.thing_of_string Proprs.signature ;
  let goal = YS.Util.(prob |> member "goal" |> maybe_concat)
             |> Uterm.form_of_string |> Types.triv in
  let msteps = YS.Util.(prob |> member "msteps" |> to_list)
               |> List.map ~f:maybe_concat
               |> List.map ~f:(Uterm.thing_of_string Proprs.one_term)
               |> List.map ~f:parse_mstep in
  let deriv = Form4.compute_derivation goal msteps in
  let module O = (val mode : To.TO) in
  Printf.ksprintf (O.pp_comment out) "problem #%d in %s" (no + 1) fname ;
  O.pp_deriv out (!Types.sigma, deriv)

let process_file out ~mode fname =
  let module O = (val mode : To.TO) in
  O.pp_comment out fname ;
  match Yojson.Safe.from_file fname with
  | `List probs ->
      List.iteri ~f:(process_problem out ~mode ~fname) probs
  | _ -> bad_json ()

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

let run_command ?(print : unit option) cmd =
  let cmd = cmd ^ " 2>&1" in
  Stdlib.Printf.printf "Running [CWD=%s]: %s\n%!"
    (Unix.getcwd ()) cmd ;
  let ic = Unix.open_process_in cmd in
  match Unix.waitpid [] (Unix.process_in_pid ic) with
  | (_, Unix.WEXITED 0) ->
      let output = read_all ic in
      if Option.is_some print then
        Stdlib.Printf.printf "%s\n%!" (setoff "> " output) ;
  | _ | exception _ ->
      Stdlib.Printf.eprintf "Error in subprocess:\n%s\n%!"
        (setoff "> " (read_all ic)) ;
      failwith "Error in subprocess"

let main () =
  let sysname = ref "lean4" in
  let mode = ref (module To.Lean4 : To.TO) in
  let set_mode str =
    sysname := str ;
    mode := To.select str
  in
  let outdir = ref @@ FilePath.concat (Stdlib.Filename.get_temp_dir_name ()) "batch" in
  let set_outdir dir = outdir := FilePath.reduce dir in
  let doit = ref false in
  let opts = Stdlib.Arg.[
      "-format", String set_mode, "FMT Set output format to FMT (coq, coq_reflect, lean3, lean4, isahol)" ;
      "-d", String set_outdir, "DIR Set output direcory to DIR" ;
      "-run", Set doit, " ALso run the generated build" ;
    ] |> Stdlib.Arg.align in
  let input_files : string list ref = ref [] in
  let add_input_file fname =
    if List.exists ~f:(String.equal fname) !input_files then
      failwithf "Repeated input file %S" fname ;
    input_files := fname :: !input_files
  in
  Stdlib.Arg.parse opts add_input_file @@
  Printf.sprintf "Usage: %s [OPTIONS] file1.json ...\n\nWhere OPTIONS are:"
    (Stdlib.Filename.basename Stdlib.Sys.executable_name) ;
  let module T = (val !mode : To.TO) in
  let buf = Buffer.create 19 in
  let out = Stdlib.Format.formatter_of_buffer buf in
  List.iter ~f:(process_file out ~mode:!mode) @@ List.rev !input_files ;
  Stdlib.Format.pp_print_flush out () ;
  let proofs = Buffer.contents buf in
  let outdir = serialize_into !outdir !mode proofs in
  if !doit then begin
    Unix.chdir outdir ;
    run_command ~print:() (T.build ()) ;
    Stdlib.Printf.printf "Build complete.\n"
  end

let () = main ()
