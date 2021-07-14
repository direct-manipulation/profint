open OUnit2
open Profint
open Types
open T

module Ord = struct
  let index n = App {head = Index n ; spine = []}
  let app1 f t = Term.do_app f [t]
  let app = Term.do_app
  let abs x t = Abs {var = x ; body = t}
end

module Terms = struct
  let ti = Ord.(abs "x" (index 0))
  let tk = Ord.(abs "x"
                  (abs "y"
                     (index 1)))
  let ts = Ord.(abs "x"
                  (abs "y"
                     (abs "z"
                        (app1 (app1 (index 2) (index 0))
                           (app1 (index 1) (index 0))))))

  let tdelta = Ord.(abs "x"
                      (app1 (index 0) (index 0)))
end

let test_type_check term ty _test_cx = assert_equal (Term.ty_check [] term ty) ()

let tests =
  "Term" >::: [
    "type_check(i)" >::
    test_type_check Terms.ti Types.(Arrow (Basic "a", Basic "a")) ;
    "type_check(k)" >::
    test_type_check Terms.tk Types.(Arrow (Basic "a", Arrow (Basic "b", Basic "a"))) ;
    "type_check(s)" >:: begin
      let open Types in
      let a = Basic "a" in
      let b = Basic "b" in
      let c = Basic "c" in
      let tyx = Arrow (a, Arrow (b, c)) in
      let tyy = Arrow (a, b) in
      let ty = Arrow (tyx, Arrow (tyy, Arrow (a, c))) in
      test_type_check Terms.ts ty
    end ;
    "ii = i" >:: Terms.(fun _cx ->
        assert_equal (Term.do_app ti [ti]) ti) ;
    "skk = i" >:: Terms.(fun _cx ->
        assert_equal ~cmp:Term.eq_term
          (Term.do_app ts [tk ; tk]) ti) ;
  ]
