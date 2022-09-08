(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

type dirtree =
  | File of { fname : string ; contents : string }
  | Dir of { dname : string ; contents : dirtree list }

let file fname contents = File { fname ; contents }
let dir dname contents = Dir { dname ; contents }

type system_info = {
  dirtree : dirtree ;
  mainfile : string ;
  cookie : string ;
  buildcmd : string ;
}

let serialize_into outdir system thing =
  let mainfile = Filename.concat outdir system.mainfile in
  let rec aux cwd t =
    match t with
    | File { fname ; contents } ->
        let fname = Filename.concat cwd fname in
        let contents =
          if fname <> mainfile then contents else
            CCString.replace contents
              ~which:`All ~sub:system.cookie ~by:thing
        in
        let oc = open_out_bin fname in
        output_string oc contents ;
        close_out oc
    | Dir { dname ; contents } ->
        let cwd = Filename.concat cwd dname in
        FileUtil.mkdir ~parent:true cwd ;
        List.iter (aux cwd) contents
  in
  FileUtil.mkdir ~parent:true outdir ;
  aux outdir system.dirtree

let lean4 : system_info = {
  dirtree =
    dir "lean4" [
      file "lakefile.lean"  [%blob "../../demo/lean4/lakefile.lean"] ;
        file "lean-toolchain" [%blob "../../demo/lean4/lean-toolchain"] ;
        dir  "Profint" [
          file "Basic.lean"   [%blob "../../demo/lean4/Profint/Basic.lean"] ;
        ] ;
        file "Profint.lean"   [%blob "../../demo/lean4/Profint.lean"] ;
        file "Proof.lean"     [%blob "../../demo/lean4/Proof.lean"] ;
      ] ;
  mainfile = "lean4/Proof.lean" ;
  cookie = "/-PROOF-/\n" ;
  buildcmd = "lake build" ;
}

let lean3 : system_info = {
  dirtree =
    dir "lean3" [
      file "lean-toolchain" [%blob "../../demo/lean3/lean-toolchain"] ;
      file "leanpkg.toml"   [%blob "../../demo/lean3/leanpkg.toml"] ;
      dir "src" [
        file "Proof.lean"   [%blob "../../demo/lean3/src/Proof.lean"] ;
        file "Profint.lean" [%blob "../../demo/lean3/src/Profint.lean"] ;
      ] ;
    ] ;
  mainfile = "lean3/Proof.lean" ;
  cookie = "/-PROOF-/\n" ;
  buildcmd = "leanpkg build" ;
}

let coq : system_info = {
  dirtree =
    dir "coq" [
      file "Proof.v"     [%blob "../../demo/coq/Proof.v"] ;
      file "Profint.v"   [%blob "../../demo/coq/Profint.v"] ;
      file "_CoqProject" [%blob "../../demo/coq/_CoqProject"] ;
      file "Makefile"    [%blob "../../demo/coq/Makefile"] ;
    ] ;
  mainfile = "coq/Proof.v" ;
  cookie = "(*PROOF*)\n" ;
  buildcmd = "make" ;
}

let coq_reflect : system_info = {
  dirtree =
    dir "coq_reflect" [
      file "Proof.v"     [%blob "../../demo/coq_reflect/Proof.v"] ;
      file "Profint.v"   [%blob "../../demo/coq_reflect/Profint.v"] ;
      file "_CoqProject" [%blob "../../demo/coq_reflect/_CoqProject"] ;
      file "Makefile"    [%blob "../../demo/coq_reflect/Makefile"] ;
    ] ;
  mainfile = "coq/Proof.v" ;
  cookie = "(*PROOF*)\n" ;
  buildcmd = "make" ;
}
