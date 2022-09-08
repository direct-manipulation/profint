open Profint
open Util
open Js_of_ocaml
module F = Form4

type stage = { fx : F.formx ; mstep : F.mstep }
let pp_stage ?(ppfx = F.pp_formx) out stage =
  ppfx out @@ F.mark_locations stage.fx stage.mstep
let compute_derivation stage =
  F.compute_derivation stage.fx stage.mstep

type state = {
  mutable goal : stage ;
  mutable history : stage list ;
  mutable future : stage list ;
}

let state = { goal = { fx = Types.triv F.Mk.mk_top ; mstep = F.Pristine } ;
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

let to_trail str : F.path =
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
    state.goal <- { fx = Types.triv (Uterm.form_of_string text) ;
                    mstep = F.Pristine } ;
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
      pp_to_string (pp_stage ~ppfx:To.Katex.pp_formx) state.goal |> Js.string

    method formulaToHTML text =
      try
        let f = Uterm.form_of_string @@ Js.to_string text in
        Js.some @@ Js.string @@ pp_to_string To.Katex.pp_formx @@ Types.triv f
      with _e ->
        (* Format.eprintf "formulaToHTML: %S: %s@." *)
        (*   (Js.to_string text) *)
        (*   (Printexc.to_string e) ; *)
        Js.null

    method historyHTML =
      let contents =
        state.history
        |> List.map (pp_to_string (pp_stage ~ppfx:To.Katex.pp_formx))
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
              |> List.rev_map (pp_to_string (pp_stage ~ppfx:To.Katex.pp_formx))
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
      try
        state.goal <- { state.goal with
                        mstep = F.Link { copy ;
                                         src = to_trail src ;
                                         dest = to_trail dest } } ;
        let deriv = compute_derivation state.goal in
        push_goal { fx = deriv.top ; mstep = F.Pristine } ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method doContraction path =
      let old_goal = state.goal in
      try
        state.goal <- { state.goal with
                        mstep = F.Contract { path = to_trail path } } ;
        let deriv = compute_derivation state.goal in
        push_goal { fx = deriv.top ; mstep = F.Pristine } ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method doWeakening path =
      let old_goal = state.goal in
      try
        state.goal <- { state.goal with
                        mstep = F.Weaken { path = to_trail path } } ;
        let deriv = compute_derivation state.goal in
        push_goal { fx = deriv.top ; mstep = F.Pristine } ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method testWitness src =
      let fail reason =
        Format.eprintf "testWitness: failure: %s@." reason ;
        Js.null in
      try
        let ex, side = F.Paths.formx_at state.goal.fx @@ to_trail src in
        match F.expose ex.data, side with
        | F.Exists ({ var ; ty }, _), `r ->
            Types.with_var ~fresh:true ex.tycx { var ; ty } begin fun { var ; _ } _ ->
              Js.some @@ Js.string var
            end
        | _ -> fail @@ "not an exists: " ^ F.formx_to_string ex
      with e -> fail (Printexc.to_string e)

    method doWitness path text =
      let old_goal = state.goal in
      let fail reason =
        Format.printf "doWitness: failure: %s@." reason ;
        state.goal <- old_goal ;
        false
      in
      try
        let path = to_trail path in
        let (ex, side) = F.Paths.formx_at state.goal.fx path in
        let term, given_ty = Uterm.term_of_string ~cx:ex.tycx @@ Js.to_string text in
        let termx = { ex with data = term } in
        match F.expose ex.data, side with
        | F.Exists ({ ty ; _ }, _), `r when ty = given_ty ->
            state.goal <- { state.goal with mstep = F.Inst { path ; termx } } ;
            let deriv = compute_derivation state.goal in
            push_goal { fx = deriv.top ; mstep = F.Pristine } ;
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
        | last :: stages ->
            let deriv = compute_derivation last in
            let deriv = List.fold_left begin fun deriv stage ->
                F.Cos.concat (compute_derivation stage) deriv
              end deriv stages in
            let module O = (val To.select kind) in
            let str = pp_to_string O.pp_deriv (!Types.sigma, deriv) in
            Js.some @@ Js.string str
        | _ -> fail "!!missing stages!!"
      with e -> fail (Printexc.to_string e)
  end

let () = Js.export "profint" profint_object
