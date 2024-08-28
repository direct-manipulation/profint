(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Profint
open Util
open Js_of_ocaml
module F = Form4

type stage = {
  fx : F.formx ;
  mstep : F.mstep ;
  rep : Js.js_string Js.t ;
}

let mk_stage ~fx ~mstep =
  let rep = F.mark_locations fx mstep |>
            To_katex.formx_to_string |>
            Js.string in
  { fx ; mstep ; rep }

let compute_derivation stage =
  F.compute_derivation stage.fx [stage.mstep]

type state = {
  mutable goal : stage ;
  mutable history : stage list ;
  mutable future : stage list ;
}

let state = { goal = mk_stage ~fx:(Types.triv F.Mk.mk_top) ~mstep:F.Pristine ;
              future = [] ;
              history = [] }

let save_uterm () =
  let open Types in
  let stage_to_uterm stg = Form4.mstep_to_uterm stg.mstep in
  let history = U.app (U.var_s "H") @@ List.map stage_to_uterm state.history in
  let future = U.app (U.var_s "F") @@ List.map stage_to_uterm state.future in
  let goal = stage_to_uterm state.goal in
  U.app (U.var_s "T") [goal ; history ; future]

let get_history fx utm =
  match F.un_app utm with
  | Some ("H", utms) ->
      List.fold_right begin fun utm (history, fx) ->
        let mstep = F.uterm_to_mstep utm in
        let stg = mk_stage ~fx ~mstep in
        let history = stg :: history in
        let fx = (compute_derivation stg).top in
        (history, fx)
      end utms ([], fx)
  | _ -> failwith "get_history"

let get_future fx utm =
  match F.un_app utm with
  | Some ("F", utms) ->
      List.fold_left begin fun (future, fx) utm ->
        let mstep = F.uterm_to_mstep utm in
        let stg = mk_stage ~fx ~mstep in
        let future = stg :: future in
        let fx = (compute_derivation stg).top in
        (future, fx)
      end ([], fx) utms
  | _ -> failwith "get_future"

let load_uterm fx utm =
  match F.un_app utm with
  | Some ("T", [ goal_mstep ; history_msteps ; future_msteps ]) ->
      (* Stdlib.Printf.printf "Trying to load history...\n" ; *)
      let (history, fx) = get_history fx history_msteps in
      (* Stdlib.Printf.printf "Loaded history [size=%d]...\n" (List.length history) ; *)
      (* Stdlib.Printf.printf "Trying to load goal...\n" ; *)
      let goal = mk_stage ~fx ~mstep:(F.uterm_to_mstep goal_mstep) in
      let fx = (compute_derivation goal).top in
      (* Stdlib.Printf.printf "Trying to load future...\n" ; *)
      let (future, _) = get_future fx future_msteps in
      (* Stdlib.Printf.printf "Loaded future [size=%d]...\n" (List.length future) ; *)
      state.goal <- goal ;
      state.history <- history ;
      state.future <- List.rev future
  | _ -> failwith "load_uterm"

let push_goal goal =
  state.future <- [] ;
  state.history <- state.goal :: state.history ;
  state.goal <- goal

let sig_change text =
  try begin
    let sigma = Uterm.thing_of_string Proprs.signature text in
    Types.sigma := sigma ;
    true
  end with _e ->
    (* Stdlib.Format.eprintf "sig_change: %s@." (Printexc.to_string e) ; *)
    false

let to_path str : F.path =
  try Js.to_string str |> Path.of_string
  with e ->
    Stdlib.Format.eprintf "to_path: %s@." @@ Printexc.to_string e ;
    raise e

let change_formula text =
  try
    state.goal <- mk_stage
        ~fx:(Types.triv (Uterm.form_of_string text))
        ~mstep:F.Pristine ;
    state.history <- [] ;
    state.future <- [] ;
    true
  with _ -> false

let get_proof kind =
  let fail reason =
    Stdlib.Format.eprintf "get_proof(%s): failure: %s@." kind reason ;
    failwith "get_proof"
  in
  try
    let stages = List.rev_append state.history (state.goal :: state.future) in
    match stages with
    | [] -> assert false    (* impossible! *)
    | last :: _ ->
        let deriv = F.compute_derivation last.fx
            (List.map (fun stg -> stg.mstep) stages) in
        let module O = (val To.select kind) in
        let str = pp_to_string O.pp_deriv (!Types.sigma, deriv) in
        str
  with e -> fail (Printexc.to_string e)

let get_proof_bundle_zip name kind : Js.Unsafe.top Js.t =
  let proof = get_proof kind in
  let module O = (val To.select kind : To.TO) in
  let files = O.files proof in
  let rec dirtree_to_obj obj (tree : Types.dirtree) =
    match tree with
    | File { fname ; contents } ->
        Js.Unsafe.meth_call obj "file" [|
          Js.Unsafe.coerce @@ Js.string fname ;
          Js.Unsafe.coerce @@ Js.string contents ;
        |]
    | Dir { dname ; contents } ->
        let obj = Js.Unsafe.meth_call obj "folder" [|
            Js.Unsafe.coerce @@ Js.string dname ;
          |] in
        List.iter (dirtree_to_obj obj) contents
  in
  let zip = Js.Unsafe.new_obj (Js.Unsafe.pure_js_expr "JSZip") [| |] in
  let obj = Js.Unsafe.meth_call zip "folder" [|
      Js.Unsafe.coerce @@ Js.string name
    |] in
  List.iter (dirtree_to_obj obj) files ;
  zip

exception Cannot_start

let profint_object =
  object%js
    method startup =
      try
        let pmap = StringMap.of_seq @@ List.to_seq Url.Current.arguments in
        Option.iter begin fun sigText ->
          if not @@ sig_change (Url.urldecode sigText) then
            raise Cannot_start;
        end @@ StringMap.find_opt "s" pmap ;
        (* Printf.printf "signature initailized\n%!" ; *)
        Option.iter begin fun formText ->
          if not @@ change_formula (Url.urldecode formText) then
            raise Cannot_start
        end @@ StringMap.find_opt "f" pmap ;
        (* Printf.printf "formula initailized\n%!" ; *)
        Option.iter begin fun permaText ->
          let permaText = Url.urldecode permaText in
          (* Stdlib.Printf.printf "Trying to load perma: %S\n%!" permaText ; *)
          let utm = Uterm.thing_of_string Proprs.one_term permaText in
          load_uterm state.goal.fx utm
        end @@ StringMap.find_opt "p" pmap ;
        Js._true
      with Cannot_start -> Js._false

    method signatureChange text =
      sig_change @@ Js.to_string text

    method getSignatureTeX =
      pp_to_string To.Katex.pp_sigma !Types.sigma |> Js.string

    method getStateTeX = state.goal.rep

    method termToTeX text =
      try
        let (f, _) = Uterm.term_of_string @@ Js.to_string text in
        Js.some @@ Js.string @@ pp_to_string To.Katex.pp_termx @@ Types.triv f
      with _ -> Js.null

    method formulaToTeX text =
      try
        let f = Uterm.form_of_string @@ Js.to_string text in
        Js.some @@ Js.string @@ pp_to_string To.Katex.pp_formx @@ Types.triv f
      with _e ->
        (* Stdlib.Format.eprintf "formulaToTeX: %S: %s@." *)
        (*   (Js.to_string text) *)
        (*   (Printexc.to_string e) ; *)
        Js.null

    method historyTeX =
      match state.history with
      | [] -> Js.array [| |]
      | _ -> state.history
             |> List.map (fun stg -> stg.rep)
             |> Array.of_list
             |> Js.array

    method futureTeX =
      match state.future with
      | [] -> Js.array [| |]
      | _ ->
          state.future
          |> List.rev_map (fun stg -> stg.rep)
          |> Array.of_list
          |> Js.array

    method doUndo =
      match state.history with
      | f :: rest ->
          state.future <- state.goal :: state.future ;
          state.goal <- f ;
          state.history <- rest ;
          true
      | _ -> false

    method doRedo =
      match state.future with
      | f :: rest ->
          state.history <- state.goal :: state.history ;
          state.goal <- f ;
          state.future <- rest ;
          true
      | _ -> false

    method makeLink src dest (copy : bool) =
      let old_goal = state.goal in
      try
        let src = to_path src in
        let dest = to_path dest in
        state.goal <- mk_stage
            ~fx:state.goal.fx
            ~mstep:F.(Link { copy ; src ; dest }) ;
        let deriv = compute_derivation state.goal in
        push_goal @@ mk_stage ~fx:deriv.top ~mstep:F.Pristine ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method doContraction path =
      let old_goal = state.goal in
      try
        let path = to_path path in
        state.goal <- mk_stage ~fx:state.goal.fx ~mstep:F.(Contract { path }) ;
        let deriv = compute_derivation state.goal in
        push_goal @@ mk_stage ~fx:deriv.top ~mstep:F.Pristine ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method doWeakening path =
      let old_goal = state.goal in
      try
        let path = to_path path in
        state.goal <- mk_stage ~fx:state.goal.fx ~mstep:F.(Weaken { path }) ;
        let deriv = compute_derivation state.goal in
        push_goal @@ mk_stage ~fx:deriv.top ~mstep:F.Pristine ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method getItems path =
      let fail () = Js.null in
      try
        let path = to_path path in
        let fx, side = F.Paths.formx_at state.goal.fx path in
        let contract    = ref false in
        let weaken      = ref false in
        let rename      = ref false in
        let instantiate = ref false in
        let () =
          match F.expose fx.data with
          | F.Forall _ ->
              rename := true ;
              instantiate := Path.Dir.equal side L
          | F.Exists _ ->
              rename := true ;
              instantiate := Path.Dir.equal side R
          | F.Imp _ ->
              contract := Path.Dir.equal side R ;
              weaken := Path.Dir.equal side R
          | _ -> ()
        in
        object%js
          val contract    = Js.bool !contract
          val weaken      = Js.bool !weaken
          val instantiate = Js.bool !instantiate
          val rename      = Js.bool !rename
          val show        = Js.bool (!contract || !weaken ||
                                     !instantiate || !rename)
        end |> Js.some
      with _ -> fail ()

    method getBoundIdentifier path =
      let fail () = Js.null in
      try
        let fx, side = F.Paths.formx_at state.goal.fx @@ to_path path in
        let quantifier, vty =
          match F.expose fx.data with
          | F.Forall (vty, _) -> "forall", vty
          | F.Exists (vty, _) -> "exists", vty
          | _ -> failwith "not a binder"
        in
        let ident = Types.with_var fx.tycx vty (fun vty _ -> vty.var) in
        object%js
          val side = Js.string (match side with L -> "L" | _ -> "R")
          val quantifier = Js.string quantifier
          val ident = Ident.to_string ident |> Js.string |> Js.some
        end |> Js.some
      with _ -> fail ()

    method doWitness path text =
      let old_goal = state.goal in
      let fail reason =
        Stdlib.Format.printf "doWitness: failure: %s@." reason ;
        state.goal <- old_goal ;
        false
      in
      try
        let path = to_path path in
        let (ex, side) = F.Paths.formx_at state.goal.fx path in
        let term = Uterm.thing_of_string Proprs.one_term @@ Js.to_string text in
        match F.expose ex.data, side with
        | F.Forall _, L
        | F.Exists _, R ->
            state.goal <- mk_stage ~fx:state.goal.fx
                ~mstep:F.(Inst { path ; term }) ;
            let deriv = compute_derivation state.goal in
            push_goal @@ mk_stage ~fx:deriv.top ~mstep:F.Pristine ;
            true
        | _ -> fail "not instantiable"
      with e -> fail (Printexc.to_string e)

    method doRename path text =
      let old_goal = state.goal in
      let fail reason =
        Stdlib.Format.printf "doRename: failure: %s@." reason ;
        state.goal <- old_goal ;
        false
      in
      try
        let path = to_path path in
        let var = Uterm.thing_of_string Proprs.one_term @@ Js.to_string text in
        match var with
        | Var var ->
            state.goal <- mk_stage
                ~fx:state.goal.fx
                ~mstep:F.(Rename { path ; var }) ;
            let deriv = compute_derivation state.goal in
            push_goal @@ mk_stage ~fx:deriv.top ~mstep:F.Pristine ;
            true
        | _ -> fail "invalid identifier"
      with e -> fail (Printexc.to_string e)

    method getProof kind =
      try Js.some @@ Js.string @@ get_proof (Js.to_string kind)
      with _ -> Js.null

    method getProofBundle name kind =
      try
        get_proof_bundle_zip (Js.to_string name) (Js.to_string kind)
        |> Js.some
      with _ -> Js.null

    method getUITrace =
      let utm = save_uterm () in
      let str = Uterm.uterm_to_string Types.empty utm in
      Js.string str

  end

let () = Js.export "profint" profint_object
