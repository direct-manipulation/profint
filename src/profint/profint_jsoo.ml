open Profint
open Util
open Js_of_ocaml

type state = {
  mutable goal : Form4.mstep ;
  mutable history : Form4.mstep list ;
  mutable future : Form4.mstep list ;
}

let state = { goal = Form4.Pristine { goal = Types.triv Form4.Mk.mk_top } ;
              future = [] ; history = [] }

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
    (* Format.eprintf "sig_change: %s@." (Printexc.to_string e) ; *)
    false

let to_trail str : Form4.path =
  let path = Js.to_string str |> String.split_on_char ';' in
  match path with
  | [""] -> Q.empty
  | dirs ->
      Q.of_list dirs |>
      Q.map begin function
      | "l" -> `l
      | "r" -> `r
      | "d" -> `d
      | dir when dir.[0] = 'i' ->
          `i (String.sub dir 2 (String.length dir - 3))
      | dir -> failwith @@ "invalid direction: " ^ dir
      end

let change_formula text =
  try
    state.goal <- Form4.Pristine { goal = Types.triv (Uterm.form_of_string text) } ;
    state.history <- [] ;
    state.future <- [] ;
    true
  with _ -> false

exception Cannot_start

let profint_object =
  object%js
    method startup =
      try
        let pmap = Url.Current.arguments |> List.to_seq |> IdMap.of_seq in
        Option.iter begin fun sigText ->
          if not @@ sig_change (Url.urldecode sigText) then
            raise Cannot_start;
        end @@ IdMap.find_opt "s" pmap ;
        (* Printf.printf "signature initailized\n%!" ; *)
        Option.iter begin fun formText ->
          if not @@ change_formula (Url.urldecode formText) then
            raise Cannot_start
        end @@ IdMap.find_opt "f" pmap ;
        (* Printf.printf "formula initailized\n%!" ; *)
        Js.some @@ Js.string @@ pp_to_string Types.pp_sigma !Types.sigma
      with Cannot_start -> Js.null

    method signatureChange text =
      sig_change @@ Js.to_string text

    method formulaChange text =
      change_formula @@ Js.to_string text

    method getStateHTML =
      pp_to_string (Form4.pp_mstep ~ppfx:To.Tex.pp_formx) state.goal |> Js.string

    method formulaToHTML text =
      try
        let f = Uterm.form_of_string @@ Js.to_string text in
        Js.some @@ Js.string @@ pp_to_string To.Tex.pp_formx @@ Types.triv f
      with _e ->
        (* Format.eprintf "formulaToHTML: %S: %s@." *)
        (*   (Js.to_string text) *)
        (*   (Printexc.to_string e) ; *)
        Js.null

    method historyHTML =
      let contents =
        state.history
        |> List.map (pp_to_string (Form4.pp_mstep ~ppfx:To.Tex.pp_formx))
        |> String.concat {| \mathstrut \\ \hline |}
      in
      {| \begin{array}{c} \hline |} ^ contents ^ {| \end{array} |}
      |> Js.string

    method countHistory = List.length state.history
    method countFuture = List.length state.future

    method futureHTML =
      let str = match state.future with
        | [] -> ""
        | _ ->
            let contents =
              state.future
              |> List.rev_map (pp_to_string (Form4.pp_mstep ~ppfx:To.Tex.pp_formx))
              |> String.concat {| \mathstrut \\ \hline |}
            in
            {| \begin{array}{c} |} ^ contents ^ {| \\ \hline \end{array} |}
      in
      Js.string str

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
      let goal = Form4.goal_of_mstep old_goal in
      try
        state.goal <- Form4.Link { copy ; goal ;
                                   src = to_trail src ;
                                   dest = to_trail dest } ;
        let deriv = Form4.compute_derivation state.goal in
        push_goal (Form4.Pristine { goal = deriv.top }) ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method doContraction path =
      let old_goal = state.goal in
      let fx = Form4.goal_of_mstep old_goal in
      try
        state.goal <- Form4.Contract { goal = fx ; path = to_trail path } ;
        let deriv = Form4.compute_derivation state.goal in
        push_goal (Form4.Pristine { goal = deriv.top }) ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method doWeakening path =
      let old_goal = state.goal in
      let fx = Form4.goal_of_mstep old_goal in
      try
        state.goal <- Form4.Weaken { goal = fx ; path = to_trail path } ;
        let deriv = Form4.compute_derivation state.goal in
        push_goal (Form4.Pristine { goal = deriv.top }) ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method testWitness src =
      let fail reason =
        Format.eprintf "testWitness: failure: %s@." reason ;
        Js.null in
      try
        let fx = Form4.goal_of_mstep state.goal in
        let ex, side = Form4.Paths.formx_at fx @@ to_trail src in
        match Form4.expose ex.data, side with
        | Form4.Exists ({ var ; ty }, _), `r ->
            Types.with_var ~fresh:true ex.tycx { var ; ty } begin fun { var ; _ } _ ->
              Js.some @@ Js.string var
            end
        | _ -> fail @@ "not an exists: " ^ Form4.formx_to_string ex
      with e -> fail (Printexc.to_string e)

    method doWitness path text =
      let old_goal = state.goal in
      let fx = Form4.goal_of_mstep old_goal in
      let fail reason =
        Format.printf "doWitness: failure: %s@." reason ;
        state.goal <- old_goal ;
        false
      in
      try
        let path = to_trail path in
        let (ex, side) = Form4.Paths.formx_at fx path in
        let term, given_ty = Uterm.term_of_string ~cx:ex.tycx @@ Js.to_string text in
        let termx = { ex with data = term } in
        match Form4.expose ex.data, side with
        | Form4.Exists ({ ty ; _ }, _), `r when ty = given_ty ->
            state.goal <- Form4.Inst { goal = fx ; path ; termx } ;
            let deriv = Form4.compute_derivation state.goal in
            push_goal (Form4.Pristine { goal = deriv.top }) ;
            true
        | _ -> fail "not an exists"
      with e -> fail (Printexc.to_string e)

    method getProof kind =
      let kind = Js.to_string kind in
      let fail reason =
        Format.eprintf "getProof: failure: %s@." reason ;
        Js.null
      in
      try
        match List.rev_append state.history (state.goal :: state.future) with
        | last_mstep :: msteps ->
            let deriv = Form4.compute_derivation last_mstep in
            let deriv = List.fold_left begin fun deriv mstep ->
                Form4.Cos.concat (Form4.compute_derivation mstep) deriv
              end deriv msteps in
            let pp_deriv = match kind with
              | "coq"         -> To.Coq.pp_deriv
              | "coq_reflect" -> To.Coq_reflect.pp_deriv
              | "lean3"       -> To.Lean3.pp_deriv
              | "lean4"       -> To.Lean4.pp_deriv
              | _ -> failwith @@ "unknown formal system " ^ kind
            in
            let str = pp_to_string pp_deriv (!Types.sigma, deriv) in
            Js.some @@ Js.string str
        | _ -> fail "!!missing msteps!!"
      with e -> fail (Printexc.to_string e)
  end

let () = Js.export "profint" profint_object