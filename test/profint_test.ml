let () =
  let open OUnit2 in
  "Profint" >::: [
    Pro_test.tests ;
    Term_test.tests ;
    Form4_test.tests ;
  ] |> run_test_tt_main
