open OUnit2
open Profint
open Term

module Types = struct
  let basic a = {args = [] ; result = a}
  let arrow ty1 ty2 = {ty2 with args = ty1 :: ty2.args}
end

module Terms = struct
  let ti = Abs {var = "x" ; body = index 0}
  let tk = Abs {var = "x" ;
                body = Abs {var = "y" ;
                            body = index 1}}
  let ts = Abs {var = "x" ;
                body = Abs {var = "y" ;
                            body = Abs {var = "z" ;
                                        body = App {head = Index 2 ;
                                                    spine = [index 0 ;
                                                             App {head = Index 1 ;
                                                                  spine = [index 0]}]}}}}
  let tdelta = Abs {var = "x" ;
                    body = App {head = Index 0 ;
                                spine = [index 0]}}
end

let test_type_check term ty _test_cx = assert_equal (ty_check [] term ty) ()

let tests =
  "Term" >::: [
    "type_check(i)" >::
    test_type_check Terms.ti Types.(arrow (basic "a") (basic "a")) ;
    "type_check(k)" >::
    test_type_check Terms.tk Types.(arrow (basic "a") (arrow (basic "b") (basic "a"))) ;
    "type_check(s)" >:: begin
      let open Types in
      let a = basic "a" in
      let b = basic "b" in
      let c = basic "c" in
      let tyx = arrow a (arrow b c) in
      let tyy = arrow a b in
      let ty = arrow tyx (arrow tyy (arrow a c)) in
      test_type_check Terms.ts ty
    end ;
    "ii = i" >:: Terms.(fun _cx ->
        assert_equal (do_app ti [ti]) ti) ;
    "skk = i" >:: Terms.(fun _cx ->
        assert_equal ~cmp:eq_term
          (do_app ts [tk ; tk]) ti) ;
  ]
