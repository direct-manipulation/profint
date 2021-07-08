open OUnit2
open Profint
open! Util
open Form2

let f_bin op f g = F (Bin (f, op, g))
let f_impl = f_bin Impl
let f_and = f_bin And
let f_or = f_bin Or
let f_atom a = F (Atom a)
let f_top = F (Nul Top)
let f_bot = F (Nul Bot)

let f = f_impl (f_or (f_and (f_atom "a")
                        (f_impl (f_atom "b") (f_atom "c")))
                  f_bot)
    (f_atom "f")
let (f_tab, f_root) = tabulate f
let show () =
  (f_tab.skels |> ITab.to_seq |> List.of_seq,
   f_tab.parities |> ITab.to_seq |> List.of_seq,
   f_tab.parents |> ITab.to_seq |> List.of_seq)

let round_trip f _cx =
  let ftab, root = tabulate f in
  assert_equal f (untabulate ftab root)

let tests =
  "Form2" >::: [
    "Structure" >::: [
      "atom" >:: round_trip (f_atom "a") ;
      "top" >:: round_trip (f_top) ;
      "bot" >:: round_trip (f_bot) ;
      "and" >:: round_trip (f_and (f_atom "a") (f_atom "b")) ;
      "or" >:: round_trip (f_or (f_atom "a") (f_atom "b")) ;
      "impl" >:: round_trip (f_impl (f_atom "a") (f_atom "b")) ;
    ] ;
  ]
