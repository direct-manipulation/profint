open Profint
open Util
open Js_of_ocaml

let form : Form3.form ref = ref Form3.(reform0 Top)

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
        try form := Uterm.form_of_string text ; true
        with _ -> false

      method formulaHTML =
        Form3.form_to_html !form |> Js.string

      method formulaSource =
        Form3.form_to_string !form |> Js.string

      method makeLink src dest =
        let src = Js.to_string src |> to_trail in
        let dest = Js.to_string dest |> to_trail in
        try
          form := Form3.resolve !form src dest ;
          (* Printf.printf "makeLink() worked!\n%!" ; *)
          true
        with _ -> false

      method doContraction src =
        let src = Js.to_string src |> to_trail in
        try
          form := Form3.contract !form src ;
          true
        with _ -> false
    end
  end
