(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** output PDF *)

open Base

open Types
open Form4

let ty_to_exp = To_katex.ty_to_exp
let pp_ty = To_katex.pp_ty

let termx_to_exp_ ~cx t = To_katex.termx_to_exp_ ~cx t
let termx_to_exp tx = termx_to_exp_ ~cx:tx.tycx tx.data
let pp_termx out tx = termx_to_exp tx |> Doc.bracket |> Doc.pp_linear out

let rec formx_to_exp_ ~cx (path : path) f =
  match expose f with
  | Atom a -> termx_to_exp_ ~cx a
  | Eq (s, t, _) ->
      let s = termx_to_exp_ ~cx s in
      let t = termx_to_exp_ ~cx t in
      Doc.(Appl (40, Infix (To_katex.rep_eq, Non, [s ; t])))
  | And (a, b) ->
      let a = formx_to_exp_ ~cx (Path.snoc path L) a in
      let b = formx_to_exp_ ~cx (Path.snoc path R) b in
      Doc.(Appl (30, Infix (To_katex.rep_and, Right, [a ; b])))
  | Top -> Doc.(Atom To_katex.rep_top)
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx (Path.snoc path L) a in
      let b = formx_to_exp_ ~cx (Path.snoc path R) b in
      Doc.(Appl (20, Infix (To_katex.rep_or, Right, [a ; b])))
  | Bot -> Doc.(Atom To_katex.rep_bot)
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx (Path.snoc path L) a in
      let b = formx_to_exp_ ~cx (Path.snoc path R) b in
      Doc.(Appl (10, Infix (To_katex.rep_imp, Right, [a ; b])))
  | Forall (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let b = formx_to_exp_ ~cx (Path.snoc path L) b in
        Doc.(Appl (5, Prefix (To_katex.rep_forall vty, b)))
      end
  | Exists (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let b = formx_to_exp_ ~cx (Path.snoc path L) b in
        Doc.(Appl (5, Prefix (To_katex.rep_exists vty, b)))
      end
  | Mdata (md, _, f) -> begin
      let doc = formx_to_exp_ ~cx path f in
      match md with
      | T.App { head = Const ({base = "hl" ; _}, _) ; _ } ->
          Doc.(Wrap (Transparent,
                     string_as 0 "\\hl{",
                     doc, string_as 0 "}"))
      | _ -> assert false
    end
let formx_to_exp fx = formx_to_exp_ ~cx:fx.tycx Path.empty fx.data
let pp_formx out fx = formx_to_exp fx |> Doc.bracket |> Doc.pp_linear out

let mk_hl f =
  Mk.mk_mdata (T.App { head = Const (Ident.of_string "hl", K.ty_any) ; spine = [] }) K.ty_any f
let mark_location fx rule =
  { fx with data = Paths.transform_at fx.data rule.Cos.path mk_hl }

let pp_sigma out sg =
  Caml.Format.pp_print_string out {|\begin{align*}|} ;
  Caml.Format.pp_open_vbox out 0 ; begin
    Set.iter ~f:begin fun i ->
      if Set.mem sigma0.basics i then () else
        Caml.Format.fprintf out {|%t &: \mathsf{type}.\\@,|}
          (To_katex.ident_to_doc ~font:"sf" i)
    end sg.basics ;
    Map.iteri ~f:begin fun ~key:k ~data:ty ->
      if Map.mem sigma0.consts k then () else
        Caml.Format.fprintf out {|%t &: %a.\\@,|}
          (To_katex.ident_to_doc ~font:"sf" k) pp_ty (thaw_ty ty)
    end sg.consts
  end ; Caml.Format.pp_close_box out () ;
  Caml.Format.pp_print_string out {|\end{align*}
|}

let pp_path out (path : path) =
  Path.to_list path |>
  Caml.Format.pp_print_list
    ~pp_sep:(fun out () -> Caml.Format.pp_print_string out ", ")
    (fun out -> function
       | Path.Dir.L -> Caml.Format.pp_print_string out "l"
       | R -> Caml.Format.pp_print_string out "r") out

let pp_header out () =
  Caml.Format.pp_print_string out {|\documentclass[landscape]{article}
\usepackage{proof}
\usepackage{amsmath}
\usepackage[a4paper,margin=1cm]{geometry}
\usepackage{xcolor}
\definecolor{hl}{rgb}{0.5,0,0}
\newcommand\hl[1]{{\color{hl}#1}}
\pagestyle{empty}
\begin{document}
|}

let pp_footer out () =
  Caml.Format.pp_print_string out {|
\end{document}
|}

let pp_deriv out (sg, deriv) =
  pp_header out () ;
  let chunks = List.chunks_of ~length:30 (List.rev deriv.Cos.middle) in
  List.iter ~f:begin fun chunk ->
    let (top, _, _) = List.last_exn chunk in
    (* let chunk = List.rev chunk in *)
    Caml.Format.fprintf out {|\begin{gather*}
|} ;
    List.iter ~f:begin fun (_, rule, concl) ->
      Caml.Format.fprintf out {|\infer{\mathstrut
%a
}{|} pp_formx (mark_location concl rule)
    end chunk ;
    Caml.Format.fprintf out {|\mathstrut %a%s
\end{gather*}
\clearpage
|} pp_formx top (String.make (List.length chunk) '}') ;
  end chunks ; (* (List.rev chunks) ; *)
  pp_sigma out sg ;
  pp_footer out ()

let pp_comment out str =
  Caml.Format.( pp_print_string out "% " ;
           pp_print_string out str ;
           pp_print_newline out () )

let makefile = {|
.DEFAULT_GOAL := proof.pdf

%.pdf: %.tex
	pdflatex -interaction batchmode $(<)
|} |> String.strip

let name = "pdf"
let files pf = [
  File { fname = "proof.tex" ; contents = pf } ;
  File { fname = "Makefile" ; contents = makefile } ;
]
let build () = "make -k"
