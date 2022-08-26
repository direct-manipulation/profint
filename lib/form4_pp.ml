(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Util
open Types
open Form4_core
open Form4_paths

(******************************************************************************)
(* Pretty Printing of Skeletons *)

module type SKEL_PARAMS = sig
  val ty_to_exp : ty -> Doc.exp
  val term_to_exp : T.term incx -> Doc.exp

  val rep_app : Doc.doc
  val rep_eq  : ty -> Doc.doc
  val rep_and : Doc.doc
  val rep_top : Doc.doc
  val rep_or  : Doc.doc
  val rep_bot : Doc.doc
  val rep_imp : Doc.doc
  val rep_all : typed_var -> Doc.doc
  val rep_ex  : typed_var -> Doc.doc

  val wrap      : path -> Doc.exp -> Doc.exp
  val wrap_src  : Doc.exp -> Doc.exp
  val wrap_dest : Doc.exp -> Doc.exp
end

exception Unprintable of fskel incx

module SkelPP (Params : SKEL_PARAMS) = struct
  let skel_to_exp (f2e : formx -> path -> Doc.exp) (skel : fskel incx) (path : path) =
    let fail () = raise @@ Unprintable skel in
    Params.wrap path begin
      match skel.data with
      | Atom a -> begin
          match a with
          | T.(App { head = Const (p, _) ; spine }) ->
              List.fold_left begin fun f x ->
                let x = Params.term_to_exp (x |@ skel) in
                Doc.(Appl (50, Infix (Params.rep_app, Left, [f ; x])))
              end Doc.(Atom (String p)) spine
          | _ -> fail ()
        end
      | Eq (s, t, ty) ->
          let s = Params.term_to_exp (s |@ skel) in
          let t = Params.term_to_exp (t |@ skel) in
          Doc.(Appl (40, Infix (Params.rep_eq ty, Non, [s ; t])))
      | And (a, b) ->
          let a = f2e (a |@ skel) (Q.snoc path `l) in
          let b = f2e (b |@ skel) (Q.snoc path `r) in
          Doc.(Appl (30, Infix (Params.rep_and, Right, [a ; b])))
      | Top -> Doc.(Atom Params.rep_top)
      | Or (a, b) ->
          let a = f2e (a |@ skel) (Q.snoc path `l) in
          let b = f2e (b |@ skel) (Q.snoc path `r) in
          Doc.(Appl (20, Infix (Params.rep_or, Right, [a ; b])))
      | Bot -> Doc.(Atom Params.rep_bot)
      | Imp (a, b) ->
          let a = f2e (a |@ skel) (Q.snoc path `l) in
          let b = f2e (b |@ skel) (Q.snoc path `r) in
          Doc.(Appl (10, Infix (Params.rep_imp, Right, [a ; b])))
      | Forall (vty, b) ->
          with_var ~fresh:true skel.tycx vty begin fun vty tycx ->
            let q = Params.rep_all vty in
            let b = f2e { data = b ; tycx } (Q.snoc path (`i vty.var)) in
            Doc.(Appl (5, Prefix (q, b)))
          end
      | Exists (vty, b) ->
          with_var ~fresh:true skel.tycx vty begin fun vty tycx ->
            let q = Params.rep_ex vty in
            let b = f2e { data = b ; tycx } (Q.snoc path (`i vty.var)) in
            Doc.(Appl (5, Prefix (q, b)))
          end
      | Mdata (md, _, f) -> begin
          let fe = f2e { skel with data = f } path in
          match md with
          | T.App { head = Const ("src", _) ; _ } ->
              Params.wrap_src fe
          | T.App { head = Const ("dest", _) ; _ } ->
              Params.wrap_dest fe
          | _ -> fail ()
        end
    end
  let rec to_exp_ (fx : formx) path = skel_to_exp to_exp_ (expose fx.data |@ fx) path
  let to_exp (fx : formx) = to_exp_ fx Q.empty
  let pp out fx = to_exp fx |> Doc.bracket |> Doc.pp_doc out
  let to_string fx = to_exp fx |> Doc.bracket |> Doc.lin_doc
end

(******************************************************************************)
(* Lean Pretty-Printing *)

module LeanPP = SkelPP (
  struct
    let ty_to_exp ty = Doc.(Atom (String (ty_to_string ty)))
    let term_to_exp tx = Term.term_to_exp ~cx:tx.tycx tx.data
    let rep_app = Doc.String " "
    let rep_eq _ = Doc.String " ≐ "
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
    let wrap _ e = e
    let wrap_src e =
      Doc.(Wrap (Opaque, String "〚", e, String "〛"))
    let wrap_dest e =
      Doc.(Wrap (Opaque, String "⟨", e, String "⟩"))
  end)

(******************************************************************************)
(* KaTeX Pretty Printing *)

module TexPP = SkelPP (
  struct
    let fresh_id =
      let count = ref 0 in
      fun () -> incr count ; !count
    let rec ty_to_exp ty =
      match ty with
      | Basic a ->
          let a =
            if ty = K.ty_o then Doc.StringAs (1, {|\omicron|}) else
            if ty = K.ty_i then Doc.StringAs (1, {|\iota|}) else
            Doc.StringAs (String.length a, {|\mathsf{|} ^ a ^ {|}|}) in
          Doc.Atom a
      | Arrow (ta, tb) ->
          Doc.(Appl (1, Infix (StringAs (1, {|\to|}), Right,
                               [ty_to_exp ta ; ty_to_exp tb])))
      | Tyvar v -> begin
          match v.subst with
          | None -> Doc.(Atom (StringAs (1, {|\_|})))
          | Some ty -> ty_to_exp ty
        end
    let ty_to_string ty = ty_to_exp ty |> Doc.bracket |> Doc.lin_doc
    let rec term_to_exp_ ~cx t =
      let open Doc in
      match t with
      | T.Abs { var ; body } ->
          with_var ~fresh:true cx { var ; ty = K.ty_i } begin fun vty cx ->
            let rep = StringAs (3 + String.length vty.var,
                                Printf.sprintf "\\lambda{%s}.\\," vty.var) in
            Appl (5, Prefix (rep, term_to_exp_ ~cx body))
          end
      | T.App {head ; spine = []} ->
          Term.head_to_exp ~cx head
      | T.App {head ; spine} ->
          let left = Term.head_to_exp ~cx head in
          let right = match spine with
            | [t] ->
                Wrap (Opaque, String "(",
                      term_to_exp_ ~cx t,
                      String ")")
            | _ ->
                Wrap (Opaque,
                      String "(",
                      Appl (0, Infix (String ",", Left,
                                      List.map (term_to_exp_ ~cx) spine)),
                      String ")")
          in
          Appl (200, Infix (StringAs (0, ""), Non, [left ; right]))
    let term_to_exp tx =
      Doc.(Wrap (Transparent,
                 StringAs (0, Printf.sprintf {|\htmlId{t%d}{|} @@ fresh_id ()),
                 term_to_exp_ ~cx:tx.tycx tx.data,
                 StringAs (0, {|}|})))
    let rep_app  = Doc.StringAs (1, {|\,|})
    let rep_eq _ = Doc.StringAs (1, {|\mathbin{\doteq}|})
    let rep_and  = Doc.StringAs (1, {|\mathbin{\land}|})
    let rep_top  = Doc.StringAs (1, {|{\top}|})
    let rep_or   = Doc.StringAs (1, {|\mathbin{\lor}|})
    let rep_bot  = Doc.StringAs (1, {|{\bot}|})
    let rep_imp  = Doc.StringAs (1, {|\mathbin{\Rightarrow}|})
    let rep_all vty =
      Doc.String (Printf.sprintf {|{\forall}{%s{:}%s}.\,|}
                    vty.var (ty_to_string vty.ty))
    let rep_ex vty =
      Doc.String (Printf.sprintf {|{\exists}{%s{:}%s}.\,|}
                    vty.var (ty_to_string vty.ty))
    let dir_to_string (d : dir) =
      match d with
      | `l -> "l"
      | `r -> "r"
      | `d -> "d"
      | `i x -> "i(" ^ x ^ ")"
    let path_to_string path =
      path
      |> Q.to_list
      |> List.map dir_to_string
      |> String.concat ";"
    let wrap path e =
      let lbra = Printf.sprintf {|\htmlId{f%d}{\htmlData{path=%s}{|}
          (fresh_id ())
          (path_to_string path)
      in
      Doc.(Wrap (Transparent, StringAs (0, lbra), e, StringAs (0, {|}}|})))
    let wrap_src e =
      Doc.(Wrap (Transparent, StringAs (0, {|\lnsrc{|}), e, StringAs (0, "}")))
    let wrap_dest e =
      Doc.(Wrap (Transparent, StringAs (0, {|\lndest{|}), e, StringAs (0, "}")))
  end)
