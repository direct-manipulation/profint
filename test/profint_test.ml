let () =
  let open OUnit2 in
  "Profint" >::: [
    Idt_test.tests ;
    Term_test.tests ;
    Form_test.tests ;
  ] |> run_test_tt_main
