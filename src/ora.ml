open Profint
open Util
open Js_of_ocaml

let form : Form3.form ref = ref Form3.(reform0 Top)

let sig_change new_sig_text =
  Uterm.local_sig := IdMap.empty ;
  try begin
    let vtys = Uterm.thing_of_string Proprs.signature (Js.to_string new_sig_text) in
    List.iter begin fun (v, ty) ->
      let pty = Types.{nvars = 0 ; ty} in
      Uterm.(local_sig := IdMap.add v pty !local_sig)
    end vtys ;
    true
  end with _ -> false

let form_change new_form_text =
  let new_form_text = Js.to_string new_form_text in
  try form := Uterm.form_of_string new_form_text ; true
  with _ -> false

let form_get_html () =
  Form3.form_to_html !form |> Js.string

let () =
  Js.export "profint" begin
    object%js
      method sigChange new_sig_text =
        sig_change new_sig_text

      method formChange new_form_text =
        form_change new_form_text

      method formUpdate =
        form_get_html ()
    end
  end
