(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util
open Types
open! T

type typed_term = {term : term ; ty : ty}

type context = {
  at : typed_term ;
  tycx : tycx ;
  frames : frame list ;
}

and frame =
  | Abs_frame
  | Func_frame of { spine : term list }
  | Spine_frame of { func : typed_term ;
                     left : typed_term list ;
                     right : typed_term list }

exception Traversal of {context : context ; msg : string}

let traversal_failure ~context fmt =
  Printf.ksprintf (fun msg -> raise @@ Traversal {context ; msg}) fmt

let down n context =
  match context.at.term with
  | Abs {var ; body = term} when n = 0 -> begin
      match context.at.ty with
      | Arrow (var_ty, body_ty) ->
          {tycx = {var ; ty = var_ty} :: context.tycx ;
           at = {term ; ty = body_ty} ;
           frames = Abs_frame :: context.frames}
      | _ ->
          traversal_failure ~context "unknown type"
    end
  | App {head ; spine} when n = 0 && spine <> [] ->
      let hty = Term.ty_infer context.tycx head in
      {context with
       at = {term = App {head ; spine = []} ; ty = hty} ;
       frames = Func_frame {spine} :: context.frames}
  | App {head ; spine} ->
      let head_ty = Term.ty_infer context.tycx head in
      let rec type_spine spine ty =
        match spine, ty with
        | [], _ -> []
        | (t :: spine), Arrow (t_ty, ty) ->
            {term = t ; ty = t_ty} :: type_spine spine ty
        | _ ->
            traversal_failure ~context "type_spine"
      in
      let spine = type_spine spine head_ty in
      let rec get_spine_frame left right k =
        match right with
        | t :: right when k = n ->
            t, Spine_frame {func = {term = App {head ; spine = []} ;
                                    ty = head_ty} ;
                            left ; right}
        | t :: right ->
            get_spine_frame (t :: left) right (k + 1)
        | _ ->
            traversal_failure ~context "down %d" n
      in
      let term, frame = get_spine_frame [] spine 1 in
      {context with
       at = term ;
       frames = frame :: context.frames}
  | _ ->
      traversal_failure ~context "down %d" n

(* let sibling delta context =
 *   match context.frames with
 *   | Spine_frame {func ; left ; right} :: frames ->
 *       let rec move left term right delta =
 *         match left, right with
 *         | _, (r :: right) when delta < 0 ->
 *             move (term :: left) r right (delta + 1)
 *         | (l :: left), _ when delta > 0 ->
 *             move left l (term :: right) (delta - 1)
 *         | _ when delta = 0 ->
 *             let frames = Spine_frame {func ; left ; right}
 *                          :: frames in
 *             {context with at = term ; frames}
 *         | _ ->
 *             traversal_failure ~context "sibling %d" delta
 *       in
 *       move left context.at right delta
 *   | _ ->
 *       traversal_failure ~context "sibling %d" delta
 *
 * let left = sibling (-1)
 * let right = sibling (+1) *)

let up context =
  let rec get_result hty spine =
    match hty, spine with
    | _, [] -> hty
    | Arrow (_, hty), (_ :: spine) ->
        get_result hty spine
    | _ ->
        traversal_failure ~context "up: app_frame"
  in
  match context.frames with
  | Abs_frame :: frames -> begin
      match context.tycx with
      | {var ; ty} :: tycx ->
          let term = Abs {var ; body = context.at.term} in
          let ty = Arrow (ty, context.at.ty) in
          let at = {term ; ty} in
          {at ; tycx ; frames}
      | _ ->
          traversal_failure ~context "up: bas_frame"
    end
  | Func_frame {spine} :: frames ->
      let term = Term.do_app context.at.term spine in
      let ty = get_result context.at.ty spine in
      let at = {term ; ty} in
      {context with frames ; at}
  | Spine_frame { func ; left ; right } :: frames ->
      let hty = func.ty in
      let spine = List.rev_append left (context.at :: right) in
      let ty = get_result hty spine in
      let spine = List.map (fun tty -> tty.term) spine in
      let term = Term.do_app func.term spine in
      let at = {term ; ty} in
      {context with frames ; at}
  | [] ->
      traversal_failure ~context "up"

let enter tterm = { at = tterm ; tycx = [] ; frames = [] }

let rec leave context =
  match context.frames with
  | [] -> context.at
  | _ -> leave (up context)
