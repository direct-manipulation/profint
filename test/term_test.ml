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

let test_type_check term ty : test_fun =
  fun _ -> assert_equal (Term.ty_check empty term ty) ()

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
    "!type_check(a => T)" >:: begin fun _ ->
      Types.reset_sigma () ;
      let fstr = {|a \to \top|} in
      let uf = Uterm.(thing_of_string Proprs.one_form fstr) in
      match Uterm.ty_check empty uf with
      | exception Uterm.TypeError _ -> ()
      | _ -> assert_bool "unexpected type checking success" false
    end ;
    "type_check(a |- a => T)" >:: begin fun _ ->
      Types.reset_sigma () ;
      Types.sigma := Types.add_const !Types.sigma "a" { nvars = 0 ; ty = K.ty_o } ;
      let fstr = {|a \to \top|} in
      let uf = Uterm.(thing_of_string Proprs.one_form fstr) in
      let (f, _ty) = Uterm.ty_check empty uf in
      match Form4.expose f with
      | Imp (a, b) -> begin
          match Form4.expose a, Form4.expose b with
          | Atom T.(App {head = Const (a, ty) ; spine = []}), Top ->
              assert_equal a "a" ;
              assert_equal ty K.ty_o
          | _ -> assert_bool "bad consruction 1" false
        end
      | _ -> assert_bool "bad construction 2" false
    end ;
  ]
