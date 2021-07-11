open Profint
open Util
open Js_of_ocaml

type state = {
  mutable goal : Form3.form ;
  mutable history : Form3.form list ;
  mutable future : Form3.form list ;
}

let state = { goal = Form3.(reform0 Top) ;
              future = [] ; history = [] }

let push_goal goal =
  state.future <- [] ;
  state.history <- state.goal :: state.history ;
  state.goal <- goal

let sig_change text =
  Uterm.local_sig := IdMap.empty ;
  try begin
    let text = Js.to_string text in
    let vtys = Uterm.thing_of_string Proprs.signature text in
    Uterm.local_sig := IdMap.empty ;
    List.iter begin fun (v, ty) ->
      let pty = Types.{nvars = 0 ; ty} in
      Uterm.(local_sig := IdMap.add v pty !local_sig)
    end vtys ;
    true
  end with _ -> false

let to_trail str =
  range 0 (String.length str)
  |> Seq.map begin fun i ->
    match str.[i] with
      | 'L' -> Form3.L
      | 'R' -> Form3.R
      | 'D' -> Form3.D
      | _   -> invalid_arg ("to_trail: " ^ str)
  end |> List.of_seq

let () =
  Js.export "profint" begin
    object%js
      method signatureChange text =
        sig_change text

      method formulaChange text =
        let text = Js.to_string text in
        try
          state.goal <- Uterm.form_of_string text ;
          state.history <- [] ;
          state.future <- [] ;
          true
        with _ -> false

      method formulaHTML =
        Form3.form_to_html state.goal |> Js.string

      method historyHTML =
        let contents =
          state.history
          |> List.map Form3.form_to_html
          |> String.concat {| \\ \hline |}
        in
        {| \begin{array}{l} \hline |} ^ contents ^ {| \end{array} |}
        |> Js.string

      method countHistory = List.length state.history
      method countFuture = List.length state.future

      method futureHTML =
        let str = match state.future with
          | [] -> ""
          | _ ->
              let contents =
                state.future
                |> List.rev_map Form3.form_to_html
                |> String.concat {| \\ \hline |}
              in
              {| \begin{array}{l} |} ^ contents ^ {| \\ \hline \end{array} |}
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

      method makeLink src dest =
        let src = Js.to_string src |> to_trail in
        let dest = Js.to_string dest |> to_trail in
        try
          Form3.resolve state.goal src dest |> push_goal ;
          true
        with _ -> false

      method doContraction src =
        let src = Js.to_string src |> to_trail in
        try
          Form3.contract state.goal src |> push_goal ;
          true
        with _ -> false

      method doWeakening src =
        let src = Js.to_string src |> to_trail in
        try
          Form3.weaken state.goal src |> push_goal ;
          true
        with _ -> false
    end
  end
