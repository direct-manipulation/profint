open OUnit2
open Profint
open! Util

let tests =
  "Pro" >::: [
    "signature_fresh_basic" >:: begin fun _ ->
      let sg = Uterm.thing_of_string Proprs.signature {| i : \type. |} in
      assert_bool "basic type not added" (IdSet.mem "i" sg.basics)
    end ;
    "signature_no_repeated_basics" >:: begin fun _ ->
      assert_raises ~msg:"repeated basic type" Types.Invalid_sigma_extension
        (fun () -> Uterm.thing_of_string Proprs.signature {| i, i : \type. |})
    end ;
    "signature_fresh_const" >:: begin fun _ ->
      let sg = Uterm.thing_of_string Proprs.signature {| i : \o. |} in
      assert_bool "constant not added" (IdMap.mem "i" sg.consts)
    end ;
    "signature_no_repeated_consts" >:: begin fun _ ->
      assert_raises ~msg:"repeated const" Types.Invalid_sigma_extension
        (fun () -> Uterm.thing_of_string Proprs.signature {| i, i : \o. |})
    end ;
    "signature_no_clash" >:: begin fun _ ->
      assert_raises ~msg:"repeated const" Types.Invalid_sigma_extension
        (fun () -> Uterm.thing_of_string Proprs.signature {| i : \type. i : i. |})
    end ;
  ]
