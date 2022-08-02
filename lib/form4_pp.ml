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

exception Unprintable

module type SKEL_PARAMS = sig
  val rep_atom : termx -> Doc.exp
  val rep_eq : termx -> termx -> ty -> Doc.exp
  val rep_and : Doc.doc
  val rep_top : Doc.doc
  val rep_or : Doc.doc
  val rep_bot : Doc.doc
  val rep_imp : Doc.doc
  val rep_all : typed_var -> Doc.doc
  val rep_ex : typed_var -> Doc.doc
  val wrap : Doc.exp -> Doc.exp
end

module SkelPP (Params : SKEL_PARAMS) = struct
  let skel_to_exp (f2e : formx -> Doc.exp) (skel : fskel incx) =
    Params.wrap begin
      match skel.data with
      | Atom a -> Params.rep_atom (a |@ skel)
      | Eq (s, t, ty) -> Params.rep_eq (s |@ skel) (t |@ skel) ty
      | And (a, b) ->
          let a = f2e (a |@ skel) in
          let b = f2e (b |@ skel) in
          Doc.(Appl (30, Infix (Params.rep_and, Right, [a ; b])))
      | Top -> Doc.(Atom Params.rep_top)
      | Or (a, b) ->
          let a = f2e (a |@ skel) in
          let b = f2e (b |@ skel) in
          Doc.(Appl (20, Infix (Params.rep_or, Right, [a ; b])))
      | Bot -> Doc.(Atom Params.rep_bot)
      | Imp (a, b) ->
          let a = f2e (a |@ skel) in
          let b = f2e (b |@ skel) in
          Doc.(Appl (10, Infix (Params.rep_imp, Right, [a ; b])))
      | Forall (vty, b) ->
          with_var ~fresh:true skel.tycx vty begin fun vty tycx ->
            let q = Params.rep_all vty in
            let b = f2e { data = b ; tycx } in
            Doc.(Appl (5, Prefix (q, b)))
          end
      | Exists (vty, b) ->
          with_var ~fresh:true skel.tycx vty begin fun vty tycx ->
            let q = Params.rep_ex vty in
            let b = f2e { data = b ; tycx } in
            Doc.(Appl (5, Prefix (q, b)))
          end
    end
  let rec to_exp (fx : formx) =
    skel_to_exp to_exp (expose fx.data |@ fx)
  let pp out fx = to_exp fx |> Doc.bracket |> Doc.pp_doc out
  let to_string fx = to_exp fx |> Doc.bracket |> Doc.lin_doc
end

(******************************************************************************)
(* Lean Pretty-Printing *)

module LeanPP = SkelPP (
  struct
    let rep_atom t =
      match t.data with
      | T.(App { head = Const (p, _) ; spine }) ->
          List.fold_left begin fun f x ->
            let x = Term.term_to_exp ~cx:t.tycx x in
            Doc.(Appl (50, Infix (String " ", Left, [f ; x])))
          end Doc.(Atom (String p)) spine
      | _ -> raise Unprintable
    let rep_eq s t _ =
      let s = Term.term_to_exp ~cx:s.tycx s.data in
      let t = Term.term_to_exp ~cx:t.tycx t.data in
      Doc.(Appl (40, Infix (String " ≐ ", Non, [s ; t])))
    let rep_and = Doc.String " ∧ "
    let rep_top = Doc.String "⊤"
    let rep_or  = Doc.String " ∨ "
    let rep_bot = Doc.String "⊥"
    let rep_imp = Doc.String " → "
    let rep_all vty =
      Doc.String (Printf.sprintf "∀ (%s : %s), "
                    vty.var (ty_to_string vty.ty))
    let rep_ex vty =
      Doc.String (Printf.sprintf "∃ (%s : %s), "
                    vty.var (ty_to_string vty.ty))
    let wrap e = e
  end)
