open OUnit2
open Profint
open Util
open Form4
open Types

let formx_to_string fx = pp_to_string To.Lean4.pp_formx fx

let a = T.(App { head = Const ("a", K.ty_o) ; spine = [] })
let b = T.(App { head = Const ("b", K.ty_o) ; spine = [] })
let c = T.(App { head = Const ("c", K.ty_o) ; spine = [] })

let rec compute_forms_simp ?(hist = []) goal deriv =
  match deriv with
  | [] -> (formx_to_string goal :: hist, goal)
  | rule :: deriv ->
      let prem = ref @@ (Cos.compute_premise goal rule).goal in
      let hist = ref @@ Cos.rule_to_string rule ::
                        formx_to_string goal :: hist in
      let emit rule =
        hist := formx_to_string !prem :: !hist ;
        hist := Cos.rule_to_string rule :: !hist ;
        let p = Cos.compute_premise !prem rule in
        prem := p.goal ; p
      in
      let _simp_prem = recursive_simplify ~emit !prem Q.empty `r in
      compute_forms_simp !prem deriv ~hist:!hist

let kcomb = Mk.{ tycx = empty ; data = mk_imp a (mk_imp b a) }

let run_kcomb () =
  let kderiv = [
    Cos.{ name = Goal_ts_imp `r ; path = Q.empty   } ;
    Cos.{ name = Init           ; path = Q.singleton `r } ;
  ] in
  compute_forms_simp kcomb kderiv

let scomb = Mk.{ tycx = empty ;
                 data = mk_imp (mk_imp a (mk_imp b c))
                     (mk_imp (mk_imp a b) (mk_imp a c)) }

let run_scomb () =
  let sderiv = [
    Cos.{ name = Contract ; path = Q.of_list [`r ; `r] } ;
    Cos.{ name = Goal_ts_imp `l ; path = Q.of_list [`r] } ;
    Cos.{ name = Asms_imp { minor = `r ; pick = `l } ;
          path = Q.of_list [`r ; `l] } ;
    Cos.{ name = Init ; path = Q.of_list [`r ; `l ; `l] } ;
    Cos.{ name = Goal_ts_imp `r ; path = Q.of_list [] } ;
    Cos.{ name = Goal_ts_imp `r ; path = Q.of_list [`r] } ;
    Cos.{ name = Goal_imp_ts ; path = Q.of_list [`r ; `r] } ;
    Cos.{ name = Goal_imp_ts ; path = Q.of_list [`r ; `r ; `r] } ;
    Cos.{ name = Init ; path = Q.of_list [`r ; `r ; `r ; `r] } ;
    Cos.{ name = Goal_ts_imp `r ; path = Q.of_list [] } ;
    Cos.{ name = Goal_ts_and `r ; path = Q.of_list [`r] } ;
    Cos.{ name = Goal_ts_and `l ; path = Q.of_list [] } ;
    Cos.{ name = Init ; path = Q.of_list [`l] } ;
    Cos.{ name = Init ; path = Q.of_list [] } ;
  ] in
  compute_forms_simp scomb sderiv

let r x y = T.(App { head = Const ("r", Arrow (K.ty_any, Arrow (K.ty_any, K.ty_o))) ;
                     spine = [x ; y] })
let dbx n = T.(App { head = Index n ; spine = [] })

let qexch = Mk.{
    tycx = empty ;
    data = mk_imp
        (mk_ex { var = "x" ; ty = K.ty_any }
           (mk_all { var = "y" ; ty = K.ty_any } (r (dbx 1) (dbx 0))))
        (mk_all { var = "y" ; ty = K.ty_any }
           (mk_ex { var = "x" ; ty = K.ty_any } (r (dbx 0) (dbx 1)))) }

let run_qexch () =
  let (t0, t1) =
    with_var empty { var = "x" ; ty = K.ty_any } begin fun _ tycx ->
      with_var tycx { var = "y" ; ty = K.ty_any } begin fun _ tycx ->
        ({ tycx ; data = dbx 0 }, { tycx ; data = dbx 1 })
      end
    end in
  let deriv = [
    Cos.{ name = Goal_ts_all ; path = Q.of_list [] } ;
    Cos.{ name = Goal_ex_ts ; path = Q.of_list [`d] } ;
    Cos.{ name = Goal_ts_ex ; path = Q.of_list [`d ; `d] } ;
    Cos.{ name = Goal_all_ts ; path = Q.of_list [`d ; `d ; `d] } ;
    Cos.{ name = Init ; path = Q.of_list [`d ; `d ; `d ; `d] } ;
    Cos.{ name = Inst { side = `r ; term = t0 } ; path = Q.of_list [`d ; `d] } ;
    Cos.{ name = Inst { side = `r ; term = t1 } ; path = Q.of_list [`d ; `d] } ;
  ] in
  compute_forms_simp qexch deriv

let scomb_d () =
  let goal = scomb in
  compute_derivation goal [ Link {
      src = Q.of_list [`l ; `r ; `r] ;
      dest = Q.of_list [`r ; `r ; `r] ;
      copy = false ;
    } ]

let qexch_d () =
  let goal = qexch in
  compute_derivation goal [ Link {
      src = Q.of_list [`l ; `d ; `d] ;
      dest = Q.of_list [`r ; `d ; `d] ;
      copy = false ;
    } ]

let and_ts_l_d () =
  let goal = Types.triv @@ Mk.mk_imp (Mk.mk_and a b) a in
  compute_derivation goal [ Link {
      src = Q.of_list [`l ; `l] ;
      dest = Q.of_list [`r] ;
      copy = false ;
    } ]

let contract_d () =
  let goal = Types.triv @@ Mk.mk_imp a b in
  compute_derivation goal [ Contract { path = Q.empty } ]

let tests =
  "Form4" >::: [
    "K-combinator COS" >:: begin fun _ ->
      let (_, prem) = run_kcomb () in
      assert_equal ~msg:"Premise" ~printer:formx_to_string prem (Mk.mk_top |@ kcomb)
    end ;
    "S-combinator COS" >:: begin fun _ ->
      let (_, prem) = run_scomb () in
      assert_equal ~msg:"Premise" ~printer:formx_to_string prem (Mk.mk_top |@ scomb)
    end ;
    "qexch COS" >:: begin fun _ ->
      let (_, prem) = run_qexch () in
      assert_equal ~msg:"Premise" ~printer:formx_to_string prem (Mk.mk_top |@ qexch)
    end ;
    "S-combinator DManip" >:: begin fun _ ->
      let Cos.{ top = prem ; _ } = scomb_d () in
      let cmp f g = Term.eq_term f.data g.data in
      assert_equal ~printer:formx_to_string ~cmp prem
        Mk.(mk_imp (mk_imp a b) (mk_imp a (mk_and a b)) |@ scomb)
    end ;
    "qexch DManip" >:: begin fun _ ->
      let Cos.{ top = prem ; _ } = qexch_d () in
      let cmp f g = Term.eq_term f.data g.data in
      assert_equal ~printer:formx_to_string ~cmp prem
        Mk.(mk_all { var = "x" ; ty = K.ty_any }
                (mk_all { var = "y" ; ty = K.ty_any }
                   (mk_ex { var = "x_1" ; ty = K.ty_any }
                      (mk_ex { var = "y_1" ; ty = K.ty_any }
                         (mk_and
                           (mk_eq (dbx 2) (dbx 1) K.ty_any)
                           (mk_eq (dbx 0) (dbx 3) K.ty_any))))) |@ qexch)
    end ;
    "and_ts_l" >:: begin fun _ ->
      let Cos.{ top = prem ; _ } = and_ts_l_d () in
      let cmp f g = Term.eq_term f.data g.data in
      assert_equal ~printer:formx_to_string ~cmp prem
        Mk.(Types.triv mk_top)
    end ;
    "contract" >:: begin fun _ ->
      let Cos.{ top = prem ; _ } = contract_d () in
      let cmp f g = Term.eq_term f.data g.data in
      assert_equal ~printer:formx_to_string ~cmp prem
        Mk.(Types.triv @@ mk_imp a (mk_imp a b))
    end ;
  ]
