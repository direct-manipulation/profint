(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util
open! Types
open! T

type form = term                (* of type \\o *)

type fskel =
  | Atom of term
  | Eq of term * term * ty
  | And of form * form | Top
  | Or of form * form | Bot
  | Imp of form * form
  | Forall of ident * ty * form
  | Exists of ident * ty * form
  | Pos_int of form * form
  | Neg_int of form * form

let expose form =
  match form with
  | App {head = Const (k, _) ; spine = []} when k = k_top ->
      Top
  | App {head = Const (k, _) ; spine = []} when k = k_bot ->
      Bot
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_and ->
      And (fa, fb)
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_or ->
      Or (fa, fb)
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_imp ->
      Imp (fa, fb)
  | App {head = Const (k, Arrow (ty, _)) ; spine = [t1 ; t2]} when k = k_eq ->
      Eq (t1, t2, ty)
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_neg_int ->
      Neg_int (fa, fb)
  | App {head = Const (k, _) ; spine = [fa ; fb]} when k = k_pos_int ->
      Pos_int (fa, fb)
  | App {head = Const (k, Arrow (Arrow (ty, _), _)) ;
         spine = [Abs {var ; body}]} when k = k_all ->
      Forall (var, ty, body)
  | App {head = Const (k, Arrow (Arrow (ty, _), _)) ;
         spine = [Abs {var ; body}]} when k = k_ex ->
      Exists (var, ty, body)
  | _ ->
      Atom form

let ty_ooo = Arrow (ty_o, Arrow (ty_o, ty_o))

let reform0 fsk =
  match fsk with
  | Atom f -> f
  | Eq (t1, t2, ty) ->
      App {head = Const (k_eq, Arrow (ty, Arrow (ty, ty_o))) ;
           spine = [t1 ; t2]}
  | And (fa, fb) ->
      App {head = Const (k_and, ty_ooo) ; spine = [fa ; fb]}
  | Top -> App {head = Const (k_top, ty_o) ; spine = []}
  | Neg_int (fa, fb) ->
      App {head = Const (k_neg_int, ty_ooo) ; spine = [fa ; fb]}
  | Or (fa, fb) ->
      App {head = Const (k_or, ty_ooo) ; spine = [fa ; fb]}
  | Bot -> App {head = Const (k_bot, ty_o) ; spine = []}
  | Imp (fa, fb) ->
      App {head = Const (k_imp, ty_ooo) ; spine = [fa ; fb]}
  | Pos_int (fa, fb) ->
      App {head = Const (k_pos_int, ty_ooo) ; spine = [fa ; fb]}
  | Forall (var, ty, body) ->
      App {head = Const (k_all, Arrow (Arrow (ty, ty_o), ty_o)) ;
           spine = [Abs {var ; body}]}
  | Exists (var, ty, body) ->
      App {head = Const (k_ex, Arrow (Arrow (ty, ty_o), ty_o)) ;
           spine = [Abs {var ; body}]}

let reform fsk pol =
  match fsk with
  | And (fa, fb) -> begin
      match expose fa, expose fb, pol with
      | ( Bot, _, false | _, Bot, false ) ->
          reform0 Bot
      | Top, _, true -> fb
      | _, Top, true -> fa
      | _ -> reform0 fsk
    end
  | Or (fa, fb) -> begin
      match expose fa, expose fb, pol with
      | ( Top, _, true | _, Top, true ) ->
          reform0 Top
      | Bot, _, false -> fb
      | _, Bot, false -> fa
      | _ -> reform0 fsk
    end
  | Imp (fa, fb) -> begin
      match expose fa, expose fb, pol with
      | ( _, Top, true | Bot, _, true ) ->
          reform0 Top
      | Top, _, _ -> fb
      | _ -> reform0 fsk
    end
  | Forall (_, _, body) -> begin
      match expose body, pol with
      | Top, true -> reform0 Top
      | _ -> reform0 fsk
    end
  | Eq (ta, tb, _) -> begin
      if Term.eq_term ta tb
      then reform0 Top
      else reform0 fsk
    end
  | _ -> reform0 fsk

type frame =
  | Left of {conn : head ; right : form}
  | Right of {left : form ; conn : head}
  | Down of {quant : head ; var : ident}

type context = {
  frames : frame list ;
  form : form ;
  pos : bool ;
}

exception Traversal of {context : context option ; msg : string}

let traversal_failure ?context fmt =
  Printf.ksprintf (fun msg -> Traversal {context ; msg} |> raise) fmt

let enter form = {frames = [] ; form ; pos = true}

let go_left context =
  match context.form with
  | App {head = Const (k, _) as conn ; spine = [lform ; rform]} ->
      let pos = if k = Types.k_imp then not context.pos else context.pos in
      { frames = Left {conn ; right = rform} :: context.frames ;
        form = lform ;
        pos }
  | _ ->
      traversal_failure ~context
        "Cannot descend to the left"

let go_right context =
  match context.form with
  | App {head = conn ; spine = [lform ; rform]} ->
      { context with
        frames = Right {conn ; left = lform} :: context.frames ;
        form = rform }
  | _ ->
      traversal_failure ~context
        "Cannot descend to the right"

let go_down context =
  match context.form with
  | App {head = quant ; spine = [Abs {var ; body}]} ->
      { context with
        frames = Down {quant ; var} :: context.frames ;
        form = body }
  | _ ->
      traversal_failure ~context
        "Cannot descend"

let go_up context =
  match context.frames with
  | Right ff :: frames ->
      let form = App {head = ff.conn ; spine = [ff.left ; context.form]} in
      let form = reform (expose form) context.pos in
      {context with frames ; form}
  | Left ff :: frames ->
      let pos = match ff.conn with
        | Const (k, _) when k = Types.k_imp -> not context.pos
        | _ -> context.pos
      in
      let form = App {head = ff.conn ; spine = [context.form ; ff.right]} in
      let form = reform (expose form) pos in
      { frames ; pos ; form }
  | Down ff :: frames ->
      let form = App {head = ff.quant ;
                      spine = [Abs {var = ff.var ;
                                    body = context.form}]} in
      let form = reform (expose form) context.pos in
      {context with frames ; form}
  | [] ->
      traversal_failure ~context
        "Cannot go up"

let rec leave context =
  match context.frames with
  | [] ->
      if not context.pos then
        traversal_failure ~context "parity mismatch" ;
      context.form
  | _ ->
      go_up context |> leave

let get_cx context : cx =
  let rec spin cx frames =
    match frames with
    | [] -> List.rev cx
    | ( Left _ | Right _ ) :: frames ->
        spin cx frames
    | Down ff :: frames ->
        let ty = match ff.quant with
          | Const (_, Arrow (Arrow (ty, _), _)) -> ty
          | _ -> traversal_failure ~context "recovering typing context"
        in
        let cx = (ff.var, ty) :: cx in
        spin cx frames
  in
  spin [] context.frames

let k_cx = "\\cx"

let rec form_to_exp ?(cx = []) form =
  let open Doc in
  match expose form with
  | Top ->
      Atom (String "#T")
  | Bot ->
      Atom (String "#B")
  | And (fa, fb) ->
      Appl (30, Infix (String " & ", Left,
                       [form_to_exp ~cx fa ; form_to_exp ~cx fb]))
  | Or (fa, fb) ->
      Appl (20, Infix (String " | ", Left,
                       [form_to_exp ~cx fa ; form_to_exp ~cx fb]))
  | Imp (fa, fb) ->
      Appl (10, Infix (String " => ", Right,
                       [form_to_exp ~cx fa ; form_to_exp ~cx fb]))
  | Eq (t1, t2, _) ->
      Appl (10, Infix (String " == ", Non,
                       [Term.term_to_exp ~cx t1 ; Term.term_to_exp ~cx t2]))
  | Neg_int (fa, fb) ->
      Appl (30, Infix (String " @ ", Non,
                       [form_to_exp ~cx fa ; form_to_exp ~cx fb]))
  | Pos_int (fa, fb) ->
      Appl (10, Infix (String " |> ", Non,
                       [form_to_exp ~cx fa ; form_to_exp ~cx fb]))
  | Forall (var, ty, body) ->
      let qstr = Printf.sprintf "\\A [%s:%s] " var (ty_to_string ty) in
      Appl (5, Prefix (String qstr,
                       form_to_exp ~cx:((var, ty) :: cx) body))
  | Exists (var, ty, body) ->
      let qstr = Printf.sprintf "\\E [%s:%s] " var (ty_to_string ty) in
      Appl (5, Prefix (String qstr,
                       form_to_exp ~cx:((var, ty) :: cx) body))
  | Atom f -> begin
      match f with
      | App {head = Const (k, _) ; spine = [f]} when k = k_cx ->
          let fe = form_to_exp ~cx f in
          Wrap (Opaque, String "{ ", fe, String " }")
      | _ ->
          Term.term_to_exp ~cx form
    end

let pp_form ?cx out form =
  form_to_exp ?cx form
  |> Doc.bracket
  |> Doc.pp_doc out

let form_to_string ?cx form =
  form_to_exp ?cx form
  |> Doc.bracket
  |> Doc.lin_doc

let fresh_id =
  let count = ref 0 in
  fun () -> incr count ; string_of_int !count

let rec form_to_exp_html ?(cx = []) form =
  let open Doc in
  let e = match expose form with
    | Top ->
        Atom (StringAs (1, "{\\top}"))
    | Bot ->
        Atom (StringAs (1, "{\\bot}"))
    | And (fa, fb) ->
        Appl (30, Infix (StringAs (1, " \\wedge "), Left,
                         [form_to_exp_html ~cx fa ; form_to_exp_html ~cx fb]))
    | Or (fa, fb) ->
        Appl (20, Infix (StringAs (1, " \\vee "), Left,
                         [form_to_exp_html ~cx fa ; form_to_exp_html ~cx fb]))
    | Imp (fa, fb) ->
        Appl (10, Infix (StringAs (1, " \\supset "), Right,
                         [form_to_exp_html ~cx fa ; form_to_exp_html ~cx fb]))
    | Eq (t1, t2, _) ->
        Appl (10, Infix (StringAs (1, " \\doteq "), Non,
                         [Term.term_to_exp_html ~cx t1 ;
                          Term.term_to_exp_html ~cx t2]))
    | Neg_int (fa, fb) ->
        Appl (30, Infix (StringAs (1, " \\circ "), Non,
                         [form_to_exp_html ~cx fa ; form_to_exp_html ~cx fb]))
    | Pos_int (fa, fb) ->
        Appl (10, Infix (StringAs (1, " \\rhd "), Non,
                         [form_to_exp_html ~cx fa ; form_to_exp_html ~cx fb]))
    | Forall (var, ty, body) ->
        let qstr = Printf.sprintf "\\forall{%s{:}%s}.\\," var (ty_to_string ty) in
        Appl (5, Prefix (StringAs (1, qstr),
                         form_to_exp_html ~cx:((var, ty) :: cx) body))
    | Exists (var, ty, body) ->
        let qstr = Printf.sprintf "\\exists{%s{:}%s}.\\," var (ty_to_string ty) in
        Appl (5, Prefix (StringAs (1, qstr),
                         form_to_exp_html ~cx:((var, ty) :: cx) body))
    | Atom f -> begin
        match f with
        | App {head = Const (k, _) ; spine = [f]} when k = k_cx ->
            let fe = form_to_exp_html ~cx f in
            Wrap (Opaque,
                  StringAs (1, "\\bigl\\{"),
                  fe,
                  StringAs (1, "\\bigr\\}"))
        | _ ->
            Term.term_to_exp_html ~cx form
      end
  in
  Wrap (Transparent,
        StringAs (0, "\\htmlId{" ^ fresh_id () ^ "}{"),
        e,
        StringAs (0, "}"))

let form_to_html ?cx form =
  form_to_exp_html ?cx form
  |> Doc.bracket
  |> Doc.lin_doc

let marked_leave context =
  let form = App {head = Const (k_cx, Arrow (ty_o, ty_o)) ;
                  spine = [context.form]} in
  leave {context with form}

let pp_context out context = pp_form out (marked_leave context)
let context_to_string context = form_to_string (marked_leave context)

let with_context ~(fn: ?cx:cx -> _) context arg =
  let cx = get_cx context in
  fn ~cx arg

let accept_term = with_context ~fn:Uterm.term_of_string
let accept_form = with_context ~fn:Uterm.form_of_string

type crumb = L | R | D
type trail = crumb list

type position = {
  trail : crumb list ;
  has_src : bool ;
}

let trail_to_string trail =
  let trail = List.map begin function
    | L -> "L" | R -> "R" | D -> "D"
    end trail in
  String.concat " " trail

let position_to_string pos =
  Printf.sprintf "{%s ; %s}"
    (trail_to_string pos.trail)
    (if pos.has_src then "src" else "dest")

let go form trail =
  let rec follow context trail =
    match trail with
    | [] -> context
    | cr :: trail ->
        let context = match cr with
          | L -> go_left context
          | R -> go_right context
          | D -> go_down context
        in
        follow context trail
  in
  follow (enter form) trail

let rec prefix_split3 ?(common = []) src dest =
  match src, dest with
  | (cs :: src), (cd :: dest) when cs = cd ->
      let common = cs :: common in
      prefix_split3 ~common src dest
  | _ ->
      let src = { trail = src ; has_src = true } in
      let dest = { trail = dest ; has_src = false } in
      let lf, rt = match src.trail, dest.trail with
        | (L :: _), _ -> (src, dest)
        | _ -> (dest, src)
      in
      (List.rev common, lf, rt)

exception Inapplicable
let abort_if cond : unit = if cond then raise Inapplicable
let abort_unless cond : unit = abort_if (not cond)
let abort () = raise Inapplicable

let rec make_eqs ts1 ts2 ty =
  match ts1, ts2, ty with
  | [], [], _ ->
      App {head = Const (k_top, ty_o) ; spine = []}
  | [t1], [t2], Arrow (ty, _) ->
      App {head = Const (k_eq, Arrow (ty, Arrow (ty, ty_o))) ;
           spine = [t1 ; t2]}
  | (t1 :: ts1), (t2 :: ts2), Arrow (ty, tys) ->
      let eq1 = App {head = Const (k_eq, Arrow (ty, Arrow (ty, ty_o))) ;
                     spine = [t1 ; t2]} in
      let eq2 = make_eqs ts1 ts2 tys in
      App {head = Const (k_and, Arrow (ty_o, Arrow (ty_o, ty_o))) ;
           spine = [eq1 ; eq2]}
  | _ -> assert false

type rule_finish =
  | Ordinary of context
  | Continue of conclusion

and conclusion = {
  context : context ;
  lf : position ;
  rt : position
}

let dprintf0 msg fin =
  let () = match fin with
    | Ordinary context ->
        Format.printf "%s:@.  %a@."
          msg pp_context context
    | Continue concl ->
        Format.printf "%s: %s -- %s@.  %a@."
          msg (position_to_string concl.lf) (position_to_string concl.rt)
          pp_context concl.context
  in
  fin

let dprintf _msg fin = fin

let r_pos_init concl =
  abort_unless concl.context.pos ;
  abort_unless (concl.lf.trail = [L]) ;
  abort_unless (concl.rt.trail = [R]) ;
  match expose concl.context.form with
  | Pos_int (App {head = Const (a1, ty) ; spine = ts1},
             App {head = Const (a2, _)  ; spine = ts2})
      when a1 = a2 && not (IdMap.mem a1 global_sig) ->
        Ordinary {concl.context with form = make_eqs ts1 ts2 ty}
        |> dprintf "pos_init"
  | _ -> abort()

let r_pos_rel concl =
  abort_unless concl.context.pos ;
  (* abort_unless (concl.lf.trail = [L]) ;
   * abort_unless (concl.rt.trail = [R]) ; *)
  match expose concl.context.form with
  | Pos_int (fa, fb) ->
      let form = Imp (fa, fb) |> reform0 in
      Ordinary {concl.context with form}
      |> dprintf "pos_rel"
  | _ -> abort()

let r_pos_andr concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.rt.trail with
  | Pos_int (fa, fb), (R :: trail) -> begin
      match expose fb, trail with
      | And (fb, ff), (L :: trail) ->
          let f_int = Pos_int (fa, fb) |> reform0 in
          let form = And (f_int, ff) |> reform0 in
          let context = go_left {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "pos_andr_1"
      | And (ff, fb), (R :: trail) ->
          let f_int = Pos_int (fa, fb) |> reform0 in
          let form = And (ff, f_int) |> reform0 in
          let context = go_right {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "pos_andr_2"
      | _ -> abort()
    end
  | _ -> abort ()

let r_pos_orl concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.lf.trail with
  | Pos_int (fa, fb), (L :: trail) -> begin
      match expose fa, trail with
      | Or (fa, ff), (L :: trail) ->
          let f_int = Pos_int (fa, fb) |> reform0 in
          let f_imp = Imp (ff, fb) |> reform0 in
          let form = And (f_int, f_imp) |> reform0 in
          let context = go_left {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "pos_orl_1"
      | Or (ff, fa), (R :: trail) ->
          let f_int = Pos_int (fa, fb) |> reform0 in
          let f_imp = Imp (ff, fb) |> reform0 in
          let form = And (f_imp, f_int) |> reform0 in
          let context = go_right {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "pos_orl_2"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_pos_impr concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.rt.trail with
  | Pos_int (fa, fb), (R :: trail) -> begin
      match expose fb, trail with
      | Imp (fb, ff), (L :: trail) ->
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Imp (f_int, ff) |> reform0 in
          let context = go_left {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "pos_impr_1"
      | Imp (ff, fb), (R :: trail) ->
          let f_int = Pos_int (fa, fb) |> reform0 in
          let form = Imp (ff, f_int) |> reform0 in
          let context = go_right {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "pos_impr_2"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_pos_orr concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.rt.trail with
  | Pos_int (fa, fb), (R :: trail) -> begin
      match expose fb, trail with
      | Or (fb, _), (L :: trail)
      | Or (_, fb), (R :: trail) ->
          let form = Pos_int (fa, fb) |> reform0 in
          let context = {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "pos_orr"
      (* | Or (_ff, fb), (R :: trail) ->
       *     let form = Pos_int (fa, fb) |> reform0 in
       *     let context = {concl.context with form} in
       *     let rt = {concl.rt with trail = R :: trail} in
       *     Continue {concl with context ; rt}
       *     |> dprintf "pos_orr_2" *)
      | _ -> abort ()
    end
  | _ -> abort ()

let r_pos_andl concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.lf.trail with
  | Pos_int (fa, fb), (L :: trail) -> begin
      match expose fa, trail with
      | And (fa, _), (L :: trail)
      | And (_, fa), (R :: trail) ->
          let form = Pos_int (fa, fb) |> reform0 in
          let context = {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "pos_andl"
      (* | And (_, fa), (R :: trail) ->
       *     let form = Pos_int (fa, fb) |> reform0 in
       *     let context = {concl.context with form} in
       *     let lf = {concl.lf with trail = L :: trail} in
       *     Continue {concl with context ; lf}
       *     |> dprintf "pos_andl_2" *)
      | _ -> abort ()
    end
  | _ -> abort ()

let r_pos_impl concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.lf.trail with
  | Pos_int (fa, fb), (L :: trail) -> begin
      match expose fa, trail with
      | Imp (ff, fa), (R :: trail) ->
          let f_int = Pos_int (fa, fb) |> reform0 in
          let form = And (ff, f_int) |> reform0 in
          let context = go_right {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "pos_impl"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_pos_allr concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.rt.trail with
  | Pos_int (fa, fb), (R :: trail) -> begin
      match expose fb, trail with
      | Forall (var, ty, fb), (D :: trail) ->
          (* C{ \A [x] (fa |> fb) }
           * ----
           * C{ fa |> \A [x] fb } *)
          let fa = Term.sub_term (Shift 1) fa in
          let f_int = Pos_int (fa, fb) |> reform0 in
          let form = Forall (var, ty, f_int) |> reform0 in
          let context = go_down {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "pos_allr"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_pos_alll concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.lf.trail with
  | Pos_int (fa, fb), (L :: trail) -> begin
      match expose fa, trail with
      | Forall (var, ty, fa), (D :: trail) ->
          (* C{ \E [x] (fa |> fb) }
           * ----
           * C{ (\A [x] fa) |> fb } *)
          let fb = Term.sub_term (Shift 1) fb in
          let f_int = Pos_int (fa, fb) |> reform0 in
          let form = Exists (var, ty, f_int) |> reform0 in
          let context = go_down {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "pos_alll"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_pos_exl concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.lf.trail with
  | Pos_int (fa, fb), (L :: trail) -> begin
      match expose fa, trail with
      | Exists (var, ty, fa), (D :: trail) ->
          (* C{ \A [x] (fa |> fb) }
           * ----
           * C{ (\E [x] fa) |> fb } *)
          let fb = Term.sub_term (Shift 1) fb in
          let f_int = Pos_int (fa, fb) |> reform0 in
          let form = Forall (var, ty, f_int) |> reform0 in
          let context = go_down {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "pos_exl"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_pos_exr concl =
  abort_unless concl.context.pos ;
  match expose concl.context.form, concl.rt.trail with
  | Pos_int (fa, fb), (R :: trail) -> begin
      match expose fb, trail with
      | Exists (var, ty, fb), (D :: trail) ->
          (* C{ \E [x] (fa |> fb) }
           * ----
           * C{ fa |> \E [x] fb } *)
          let fa = Term.sub_term (Shift 1) fa in
          let f_int = Pos_int (fa, fb) |> reform0 in
          let form = Exists (var, ty, f_int) |> reform0 in
          let context = go_down {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "pos_exr"
      | _ -> abort ()
    end
  | _ -> abort ()

let can_descend lr concl =
  match lr with
  | L ->
      (* - either left is dest and its trail is not [L] *)
      (* - or right is dest and its trail is [R] *)
      if concl.rt.has_src then
        concl.lf.trail <> [L]
      else
        concl.rt.trail = [R]
  | R ->
      if concl.lf.has_src then
        concl.rt.trail <> [R]
      else
        concl.lf.trail = [L]
  | _ ->
      assert false

let r_neg_or concl =
  abort_if concl.context.pos ;
  match expose concl.context.form, concl.lf.trail, concl.rt.trail with
  | Neg_int (fa, fb), (L :: trail), _
    when can_descend L concl -> begin
      match expose fa, trail with
      | Or (fa, ff), (L :: trail) ->
          (* A{ (fa @ fb) | ff }
           * -------------------
           * A{ (fa | ff) @ fb } *)
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Or (f_int, ff) |> reform0 in
          let context = go_left {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "neg_or_l1"
      | Or (ff, fa), (R :: trail) ->
          (* A{ ff | (fa @ fb }
           * -------------------
           * A{ (ff | fa) @ fb } *)
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Or (ff, f_int) |> reform0 in
          let context = go_right {concl.context with form} in
          let lf = {concl.lf with trail = R :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "neg_or_l2"
      | _ -> abort ()
    end
  | Neg_int (fa, fb), _, (R :: trail)
    when can_descend R concl -> begin
      match expose fb, trail with
      | Or (fb, ff), (L :: trail) ->
          (* A{ (fa @ fb) | ff }
           * -------------------
           * A{ fa @ (fb | ff) } *)
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Or (f_int, ff) |> reform0 in
          let context = go_left {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "neg_or_r1"
      | Or (ff, fb), (R :: trail) ->
          (* A{ ff | (fa @ fb) }
           * -------------------
           * A{ fa @ (ff | fb) } *)
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Or (ff, f_int) |> reform0 in
          let context = go_right {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "neg_or_r2"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_neg_and concl =
  abort_if concl.context.pos ;
  match expose concl.context.form, concl.lf.trail, concl.rt.trail with
  | Neg_int (fa, fb), (L :: trail), _
    when can_descend L concl -> begin
      match expose fa, trail with
      | And (fa, _), (L :: trail)
      (* A{ fa @ fb }
       * -------------------
       * A{ (fa & ff) @ fb } *)
      | And (_, fa), (R :: trail) ->
          (* A{ fa @ fb }
           * -------------------
           * A{ (ff & fa) @ fb } *)
          let form = Neg_int (fa, fb) |> reform0 in
          let context = {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "neg_and_l"
      | _ -> abort ()
    end
  | Neg_int (fa, fb), _, (R :: trail)
    when can_descend R concl -> begin
      match expose fb, trail with
      | And (fb, _), (L :: trail)
      (* A{ fa @ fb }
       * -------------------
       * A{ fa @ (fb & ff) } *)
      | And (_, fb), (R :: trail) ->
          (* A{ fa @ fb }
           * -------------------
           * A{ fa @ (ff & fb) } *)
          let form = Neg_int (fa, fb) |> reform0 in
          let context = {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "neg_and_r"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_neg_imp concl =
  abort_if concl.context.pos ;
  match expose concl.context.form, concl.lf.trail, concl.rt.trail with
  | Neg_int (fa, fb), (L :: trail), _
    when can_descend L concl -> begin
      match expose fa, trail with
      | Imp (fa, ff), (L :: trail) ->
          (* A{ (fb |> fa) => ff }
           * ----
           * A{ (fa => ff) @ fb } *)
          let f_int = Pos_int (fb, fa) (* OK *) |> reform0 in
          let form = Imp (f_int, ff) |> reform0 in
          let context = go_left {concl.context with form} in
          (* note: fb, fa switch sides! *)
          let rt = {concl.lf with trail = R :: trail} in
          let lf = {concl.rt with trail = L :: List.tl concl.rt.trail} in
          Continue {context ; lf ; rt}
          |> dprintf "neg_imp_l1"
      | Imp (ff, fa), (R :: trail) ->
          (* A{ ff => (fa @ fb) }
           * ----
           * A{ (ff => fa) @ fb } *)
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Imp (ff, f_int) |> reform0 in
          let context = go_right {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "neg_imp_l2"
      | _ -> abort ()
    end
  | Neg_int (fa, fb), _, (R :: trail)
    when can_descend R concl -> begin
      match expose fb, trail with
      | Imp (fb, ff), (L :: trail) ->
          (* A{ (fa |> fb) => ff }
           * ----
           * A{ fa @ (fb => ff) } *)
          let f_int = Pos_int (fa, fb) |> reform0 in
          let form = Imp (f_int, ff) |> reform0 in
          let context = go_left {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "neg_imp_r1"
      | Imp (ff, fb), (R :: trail) ->
          (* A{ ff => (fa @ fb) }
           * ----
           * A{ fa @ (ff => fb) } *)
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Imp (ff, f_int) |> reform0 in
          let context = go_right {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "neg_imp_r1"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_neg_all concl =
  abort_if concl.context.pos ;
  match expose concl.context.form, concl.lf.trail, concl.rt.trail with
  | Neg_int (fa, fb), (L :: trail), _
    when can_descend L concl -> begin
      match expose fa, trail with
      | Forall (var, ty, fa), (D :: trail) ->
          (* A{ \A [x] (fa @ fb) }
           * ----
           * A{ (\A [x] fa) @ fb } *)
          let fb = Term.sub_term (Shift 1) fb in
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Forall (var, ty, f_int) |> reform0 in
          let context = go_down {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "neg_all_l"
      | _ -> abort ()
    end
  | Neg_int (fa, fb), _, (R :: trail)
    when can_descend R concl -> begin
      match expose fb, trail with
      | Forall (var, ty, fb), (D :: trail) ->
          (* A{ \A [x] (fa @ fb) }
           * ----
           * A{ fa @ (\A [x] fb) } *)
          let fa = Term.sub_term (Shift 1) fa in
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Forall (var, ty, f_int) |> reform0 in
          let context = go_down {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "neg_all_2"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_neg_ex concl =
  (* unusually, this is an asynchronous rule *)
  abort_if concl.context.pos ;
  match expose concl.context.form with
  | Neg_int (fa, fb) -> begin
      match expose fa, expose fb, concl.lf.trail, concl.rt.trail with
      | Exists (var, ty, fa), _, (L :: D :: trail), _ ->
          (* A{ \E [x] (fa @ fb) }
           * ----
           * A{ (\E [x] fa) @ fb } *)
          let fb = Term.sub_term (Shift 1) fb in
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Exists (var, ty, f_int) |> reform0 in
          let context = go_down {concl.context with form} in
          let lf = {concl.lf with trail = L :: trail} in
          Continue {concl with context ; lf}
          |> dprintf "neg_ex_l"
      | _, Exists (var, ty, fb), _, (R :: D :: trail) ->
          (* A{ \E [x] (fa @ fb) }
           * ----
           * A{ fa @ (\E [x] fb) } *)
          let fa = Term.sub_term (Shift 1) fa in
          let f_int = Neg_int (fa, fb) |> reform0 in
          let form = Exists (var, ty, f_int) |> reform0 in
          let context = go_down {concl.context with form} in
          let rt = {concl.rt with trail = R :: trail} in
          Continue {concl with context ; rt}
          |> dprintf "neg_ex_2"
      | _ -> abort ()
    end
  | _ -> abort ()

let r_neg_rel concl =
  abort_if concl.context.pos ;
  (* abort_unless (concl.lf.trail = [L]) ;
   * abort_unless (concl.rt.trail = [R]) ; *)
  match expose concl.context.form with
  | Neg_int (fa, fb) ->
      let form = And (fa, fb) |> reform0 in
      let context = {concl.context with form} in
      Ordinary context
      |> dprintf "neg_rel"
  | _ -> abort ()

let all_rules = [
  (* conclusive context *)
  r_pos_init ;                  (* async *)
  r_pos_andr ;                  (* async *)
  r_pos_orl ;                   (* async *)
  r_pos_impr ;                  (* async *)
  r_pos_allr ;                  (* async *)
  r_pos_exl ;                   (* async *)
  r_neg_ex ;                    (* async *)
  r_pos_orr ;
  r_pos_andl ;
  r_pos_impl ;
  r_pos_alll ;
  r_pos_exr ;
  (* assumptive context *)
  r_neg_or ;
  r_neg_and ;
  r_neg_imp ;
  r_neg_all ;
  (* r_neg_ex ; *)
  r_pos_rel ;
  r_neg_rel ;
]

let rec spin_rules concl =
  let rec try_all concl rules =
    match rules with
    | [] ->
        (* tried all the rules, and now it's stuck *)
        Continue concl |> dprintf "stuck" |> ignore ;
        concl.context
    | rule :: rules -> begin
        match rule concl with
        | Ordinary context -> context
        | Continue concl -> spin_rules concl
        | exception Inapplicable ->
            try_all concl rules
      end
  in
  try_all concl all_rules

let pos_interaction concl =
  match concl.context.form with
  | App {head = Const (k, kty) ; spine}
    when k = Types.k_imp ->
      let concl = {
        concl with
        context = {concl.context with
                   form = App {head = Const (Types.k_pos_int, kty) ;
                               spine}} ;
      } in
      dprintf "pos_int" (Continue concl) |> ignore ;
      spin_rules concl
  | _ ->
      traversal_failure ~context:concl.context
        "not an implication"

let neg_interaction concl =
  match concl.context.form with
  | App {head = Const (k, kty) ; spine}
    when k = Types.k_and ->
      let concl = {
        concl with
        context = {concl.context with
                   form = App {head = Const (Types.k_neg_int, kty) ;
                               spine}} ;
      } in
      dprintf "neg_int" (Continue concl) |> ignore ;
      spin_rules concl
  | _ ->
      traversal_failure ~context:concl.context
        "not a conjunction"

let resolve form src dest =
  let common, lf, rt = prefix_split3 src dest in
  let context = go form common in
  let concl = {context ; lf ; rt} in
  dprintf "start" (Continue concl) |> ignore ;
  let context =
    if context.pos
    then pos_interaction concl
    else neg_interaction concl
  in
  leave context

let contract form src =
  let context = go form src in
  if context.pos then
    traversal_failure ~context "cannot contract on the right" ;
  let context = go_up context in
  match expose context.form with
  | Imp (fa, _) ->
      let form = Imp (fa, context.form) |> reform0 in
      leave {context with form}
  | _ ->
      traversal_failure ~context "cannot contract a non-implication"

let weaken ~prompt form src =
  let context = go form src in
  match expose context.form, context.pos with
  | _, false -> begin
      let context = go_up context in
      match expose context.form, context.pos with
      | Imp (_, form), true ->
          leave {context with form}
      | _ -> leave context
    end
  | Exists (var, vty, body), true ->
      let msg = Printf.sprintf "Enter a witness for %s" var in
      let term_str = prompt msg in
      let term, ty = accept_term context term_str in
      if ty <> vty then failwith "invalid type" ;
      let form = Term.sub_term (Dot (Shift 0, term)) body in
      leave {context with form}
  | Eq (t1, t2, _), _ when Term.eq_term t1 t2 ->
      let form = reform0 Top in
      leave {context with form}
  | _ ->
      traversal_failure ~context "cannot simplify here"

(* let witness form src term =
 *   let context = go form src in
 *   if not context.pos then
 *     traversal_failure ~context "cannot substitute in negative context" ;
 *   match expose context.form with
 *   | Exists (_, vty, body) ->
 *       let term, ty = accept_term context term in
 *       if ty <> vty then failwith "invalid type" ;
 *       let form = Term.sub_term (Dot (Shift 0, term)) body in
 *       leave {context with form}
 *   | _ ->
 *       traversal_failure ~context
 *         "not an existential" *)

module TestFn () = struct
  let () = Uterm.declare_const "f" {| \i -> \i |}
  let () = Uterm.declare_const "j" {| \i |}
  let () = Uterm.declare_const "k" {| \i |}

  let () = Uterm.declare_const "p" {| \i -> \o |}
  let () = Uterm.declare_const "q" {| \i -> \o |}

  let () =
    List.iter begin fun p ->
      Uterm.declare_const p {| \o |}
    end ["a" ; "b" ; "c" ; "d" ; "e"]

  let aa1 = Uterm.form_of_string {| a => a |}
  let aa2 = Uterm.form_of_string {| p j => p k |}
  let aa3 = Uterm.form_of_string {| c => a => a |}
  let _aaa = Uterm.form_of_string {| (\A [y:\i] p y) => (\E [x:\i] p x) => c |}
  let aaa = Uterm.form_of_string {| (a => b => c) => (a => b) => a => c |}

  let p1 = Uterm.form_of_string {| a => (b => c) => d |}
  let p1s = form_to_string p1

  let p2 = Uterm.form_of_string {| a & (b => c) => d |}

  let f1 = Uterm.form_of_string {| p j => p k |}
  let f2 = Uterm.form_of_string {| \A [x] p x => \E [y] p y |}

  let (t1, t2, f3) =
    let cx = f2 |> enter |> go_down |> go_right |> go_down in
    (accept_term cx "f x",
     accept_term cx "f (f y)",
     leave {cx with form = accept_form cx "p (f (f y))"})

  let () = Uterm.clear_declarations ()
end
module Test = TestFn ()
