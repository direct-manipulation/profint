(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* output PDF *)

open! Util
open! Types
open! Term
open! Form4

let ty_to_exp = To_katex.ty_to_exp
let pp_ty = To_katex.pp_ty

let termx_to_exp_ ~cx t = To_katex.termx_to_exp_ ~cx t
let termx_to_exp tx = termx_to_exp_ ~cx:tx.tycx tx.data
let pp_termx out tx = termx_to_exp tx |> Doc.bracket |> Doc.pp_lin_doc out

let rec formx_to_exp_ ~cx (path : path) f =
  match expose f with
  | Atom a -> termx_to_exp_ ~cx a
  | Eq (s, t, _) ->
      let s = termx_to_exp_ ~cx s in
      let t = termx_to_exp_ ~cx t in
      Doc.(Appl (40, Infix (To_katex.rep_eq, Non, [s ; t])))
  | And (a, b) ->
      let a = formx_to_exp_ ~cx (Q.snoc path `l) a in
      let b = formx_to_exp_ ~cx (Q.snoc path `r) b in
      Doc.(Appl (30, Infix (To_katex.rep_and, Right, [a ; b])))
  | Top -> Doc.(Atom To_katex.rep_top)
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx (Q.snoc path `l) a in
      let b = formx_to_exp_ ~cx (Q.snoc path `r) b in
      Doc.(Appl (20, Infix (To_katex.rep_or, Right, [a ; b])))
  | Bot -> Doc.(Atom To_katex.rep_bot)
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx (Q.snoc path `l) a in
      let b = formx_to_exp_ ~cx (Q.snoc path `r) b in
      Doc.(Appl (10, Infix (To_katex.rep_imp, Right, [a ; b])))
  | Forall (vty, b) ->
      with_var ~fresh:true cx vty begin fun vty cx ->
        let b = formx_to_exp_ ~cx (Q.snoc path (`i vty.var)) b in
        Doc.(Appl (5, Prefix (To_katex.rep_forall vty, b)))
      end
  | Exists (vty, b) ->
      with_var ~fresh:true cx vty begin fun vty cx ->
        let b = formx_to_exp_ ~cx (Q.snoc path (`i vty.var)) b in
        Doc.(Appl (5, Prefix (To_katex.rep_exists vty, b)))
      end
  | Mdata (md, _, f) -> begin
      let doc = formx_to_exp_ ~cx path f in
      match md with
      | T.App { head = Const ("hl", _) ; _ } ->
          Doc.(Wrap (Transparent,
                     StringAs (0, "\\hl{"),
                     doc, StringAs (0, "}")))
      | _ -> assert false
    end
let formx_to_exp fx = formx_to_exp_ ~cx:fx.tycx Q.empty fx.data
let pp_formx out fx = formx_to_exp fx |> Doc.bracket |> Doc.pp_lin_doc out

let mk_hl f =
  Mk.mk_mdata (T.App { head = Const ("hl", K.ty_any) ; spine = [] }) K.ty_any f
let mark_location fx rule =
  { fx with data = Paths.transform_at fx.data rule.Cos.path mk_hl }

let pp_sigma out sg =
  Format.pp_print_string out {|\begin{align*}|} ;
  Format.pp_open_vbox out 0 ; begin
    IdSet.iter begin fun i ->
      if IdSet.mem i sigma0.basics then () else
        Format.fprintf out {|%s &: \mathsf{type}.\\@,|} i
    end sg.basics ;
    IdMap.iter begin fun k ty ->
      if IdMap.mem k sigma0.consts then () else
        Format.fprintf out {|%s &: %a.\\@,|} k pp_ty (thaw_ty ty)
    end sg.consts
  end ; Format.pp_close_box out () ;
  Format.pp_print_string out {|\end{align*}
|}

let pp_path out (path : path) =
  Q.to_seq path |>
  Format.pp_print_seq
    ~pp_sep:(fun out () -> Format.pp_print_string out ", ")
    (fun out -> function
       | `l -> Format.pp_print_string out "l"
       | `r -> Format.pp_print_string out "r"
       | `d -> Format.pp_print_string out "d"
       | `i x ->
           Format.pp_print_string out "i " ;
           Format.pp_print_string out x) out

let pp_header out () =
  Format.pp_print_string out {|\documentclass[landscape]{article}
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
  Format.pp_print_string out {|
\end{document}
|}

let pp_deriv out (sg, deriv) =
  pp_header out () ;
  let chunks = CCList.chunks 30 (deriv.Cos.middle) in
  List.iter begin fun chunk ->
    let (top, _, _) = List.hd chunk in
    let chunk = List.rev chunk in
    Format.fprintf out {|\begin{gather*}
|} ;
    List.iter begin fun (_, rule, concl) ->
      Format.fprintf out {|\infer{\mathstrut
%a
}{|} pp_formx (mark_location concl rule)
    end chunk ;
    Format.fprintf out {|\mathstrut %a%s
\end{gather*}
\clearpage
|} pp_formx top (String.make (List.length chunk) '}') ;
  end (List.rev chunks) ;
  pp_sigma out sg ;
  pp_footer out ()

let pp_comment out str =
  Format.( pp_print_string out "% " ;
           pp_print_string out str ;
           pp_print_newline out () )

let name = "pdf"
let files pf = [
  File { fname = "proof.tex" ; contents = pf }
]
let build () = "latexmk -pdfxe proof.tex"
