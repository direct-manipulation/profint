(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Types
open Form4_core

(******************************************************************************)
(* Pretty Printing of Skeletons *)

type skelpp = fskel -> Doc.doc

let to_lean : skelpp = function
  | And _ -> String " ∧ "
  | Top   -> String "⊤"
  | Or _  -> String " ∨ "
  | Bot   -> String "⊥"
  | Imp _ -> String " → "
  | Eq _ ->  String " ≐ "
  | Forall (vty, _) ->
      String (Printf.sprintf "∀ (%s : %s), " vty.var (ty_to_string vty.ty))
  | Exists (vty, _) ->
      String (Printf.sprintf "∃ (%s : %s), " vty.var (ty_to_string vty.ty))
  | Atom _ -> assert false

(******************************************************************************)
(* Pretty Printing *)

let rec formx_to_exp (skelpp : skelpp) (fx : formx) =
  let open Doc in
  let fex = expose fx.data in
  match fex with
  | Atom T.(App { head = Const (p, _) ; spine = spine }) ->
      let rec aux f xs =
        match xs with
        | [] -> f
        | x :: xs ->
            let f = Appl (40, Infix (String " ", Left,
                                     [f ; Term.term_to_exp ~cx:fx.tycx x])) in
            aux f xs
      in
      aux (Atom (String p)) spine
  | Atom a ->
      Term.term_to_exp ~cx:fx.tycx a
  | And (a, b) ->
      Appl (30, Infix (skelpp fex, Right,
                       [formx_to_exp skelpp (a |@ fx) ;
                        formx_to_exp skelpp (b |@ fx)]))
  | Or (a, b) ->
      Appl (20, Infix (String " ∨ ", Right,
                       [formx_to_exp skelpp (a |@ fx) ;
                        formx_to_exp skelpp (b |@ fx)]))
  | Eq (s, t, _) ->
      Appl (20, Infix (skelpp fex, Non,
                       [Term.term_to_exp ~cx:fx.tycx s ;
                        Term.term_to_exp ~cx:fx.tycx t]))
  | Top | Bot -> Atom (skelpp fex)
  | Imp (a, b) ->
      Appl (10, Infix (skelpp fex, Right,
                       [formx_to_exp skelpp (a |@ fx) ;
                        formx_to_exp skelpp (b |@ fx)]))
  | Forall (vty, b) ->
      with_var ~fresh:true fx.tycx vty begin fun vty tycx ->
        let qstr = skelpp @@ Forall (vty, b) in
        Appl (5, Prefix (qstr, formx_to_exp skelpp { data = b ; tycx }))
      end
  | Exists (vty, b) ->
      with_var ~fresh:true fx.tycx vty begin fun vty tycx ->
        let qstr = skelpp @@ Exists (vty, b) in
        Appl (5, Prefix (qstr, formx_to_exp skelpp { data = b ; tycx }))
      end

let pp_formx ?(skelpp = to_lean) out fx = formx_to_exp skelpp fx |> Doc.bracket |> Doc.pp_doc out
let formx_to_string ?(skelpp = to_lean) fx = formx_to_exp skelpp fx |> Doc.bracket |> Doc.lin_doc
