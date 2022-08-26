open Profint
open Util
open Js_of_ocaml

type state = {
  mutable goal : Form4.mstep ;
  mutable history : Form4.mstep list ;
  mutable future : Form4.mstep list ;
}

let state = { goal = Form4.Pristine (Types.triv Form4.Core.mk_top) ;
              future = [] ; history = [] }

let push_goal goal =
  state.future <- [] ;
  state.history <- state.goal :: state.history ;
  state.goal <- goal

let sig_change text =
  try begin
    let text = Js.to_string text in
    let sigma = Uterm.thing_of_string Proprs.signature text in
    Types.sigma := sigma ;
    true
  end with _ -> false

let to_trail str : Form4.path =
  let str = Js.to_string str in
  range 0 (String.length str)
  |> Seq.map begin fun i ->
    match str.[i] with
      | 'L' -> `l
      | 'R' -> `r
      | 'D' -> `d
      | _   -> invalid_arg ("to_trail: " ^ str)
  end |> Q.of_seq

let change_formula text =
  try
    state.goal <- Form4.Pristine (Types.triv (Uterm.form_of_string text)) ;
    state.history <- [] ;
    state.future <- [] ;
    (* Format.printf "state: %a@." (Form4.pp_mstep ~ppfx:Form4.Pp.LeanPP.pp) state.goal ; *)
    true
  with _ -> false

let profint_object =
  object%js
    method startup =
      let pmap = Url.Current.arguments |> List.to_seq |> IdMap.of_seq in
      match IdMap.find "f" pmap with
      | str ->
          change_formula @@ Url.urldecode str
      | exception Not_found -> false

    method signatureChange text =
      sig_change text

    method formulaChange text =
      change_formula @@ Js.to_string text

    method formulaOrd =
      pp_to_string (Form4.pp_mstep ~ppfx:Form4_pp.LeanPP.pp) state.goal |> Js.string

    method formulaHTML =
      pp_to_string (Form4.pp_mstep ~ppfx:Form4_pp.TexPP.pp) state.goal |> Js.string

    method convertToHTML text =
      try
        let f = Uterm.form_of_string @@ Js.to_string text in
        Js.string @@ Form3.form_to_html f
      with _ -> Js.string "!!ERROR!!"

    method historyHTML =
      let contents =
        state.history
        |> List.map (pp_to_string (Form4.pp_mstep ~ppfx:Form4_pp.TexPP.pp))
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
              |> List.rev_map (pp_to_string (Form4.pp_mstep ~ppfx:Form4_pp.TexPP.pp))
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

    method makeLink src dest (_contr : bool) =
      let old_goal = state.goal in
      let fx = ref @@ Form4.goal_of_mstep old_goal in
      try
        state.goal <- Form4.Link_form { goal = !fx ;
                                        src = to_trail src ;
                                        dest = to_trail dest } ;
        let emit_cos crule = fx := Form4.Cos.compute_premise !fx crule in
        Form4.compute_derivation ~emit:emit_cos state.goal ;
        let _ = Form4.recursive_simplify ~emit:emit_cos !fx Q.empty `r in
        push_goal (Form4.Pristine !fx) ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method doContraction src =
      let old_goal = state.goal in
      let fx = ref @@ Form4.goal_of_mstep old_goal in
      try
        state.goal <- Form4.Contract (!fx, to_trail src) ;
        let emit crule = fx := Form4.Cos.compute_premise !fx crule in
        Form4.compute_derivation ~emit state.goal ;
        push_goal (Form4.Pristine !fx) ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

    method doWeakening src =
      let old_goal = state.goal in
      let fx = ref @@ Form4.goal_of_mstep old_goal in
      try
        state.goal <- Form4.Weaken (!fx, to_trail src) ;
        let emit crule = fx := Form4.Cos.compute_premise !fx crule in
        Form4.compute_derivation ~emit state.goal ;
        push_goal (Form4.Pristine !fx) ;
        true
      with _ ->
        state.goal <- old_goal ;
        false

(*
    method testWitness trail =
      let trail = to_trail trail in
      let open Form3 in
      match go state.goal trail with
      | context when context.pos -> begin
          match expose context.form with
          | Exists (v, _, _) -> Js.some @@ Js.string v
          | _ -> Js.null
        end
      | _
      | exception _ -> Js.null

    method doWitness trail text =
      try
        let trail = to_trail trail in
        let text = Js.to_string text in
        push_goal @@ Form3.witness state.goal trail text ;
        true
      with _ -> false
*)
  end

let () = Js.export "profint" profint_object
