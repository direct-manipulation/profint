open OUnit2
open Profint
open Util
open Form4
open Types
open Pp

let a = T.(App { head = Const ("a", K.ty_o) ; spine = [] })
let b = T.(App { head = Const ("b", K.ty_o) ; spine = [] })
let c = T.(App { head = Const ("c", K.ty_o) ; spine = [] })

let rec compute_forms_simp ?(hist = []) goal deriv =
  match deriv with
  | [] -> (LeanPP.to_string goal :: hist, goal)
  | rule :: deriv ->
      let prem = ref @@ Cos.compute_premise goal rule in
      let hist = ref @@ Cos.rule_to_string goal rule ::
                        LeanPP.to_string goal :: hist in
      let emit rule =
        hist := LeanPP.to_string !prem :: !hist ;
        hist := Cos.rule_to_string !prem rule :: !hist ;
        prem := Cos.compute_premise !prem rule
      in
      let _simp_prem = recursive_simplify ~emit !prem Q.empty `r in
      compute_forms_simp !prem deriv ~hist:!hist

let kcomb = Core.{ tycx = empty ; data = mk_imp a (mk_imp b a) }

let run_kcomb () =
  let kderiv = [
    Cos.{ name = Goal_ts_imp `r ; path = Q.empty   } ;
    Cos.{ name = Init           ; path = Q.singleton `r } ;
  ] in
  compute_forms_simp kcomb kderiv

let scomb = Core.{ tycx = empty ;
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
    Cos.{ name = Goal_imp_ts ; path = Q.of_list [] } ;
    Cos.{ name = Goal_ts_imp `r ; path = Q.of_list [] } ;
    Cos.{ name = Goal_ts_and `r ; path = Q.of_list [`r] } ;
    Cos.{ name = Goal_ts_and `l ; path = Q.of_list [] } ;
    Cos.{ name = Init ; path = Q.of_list [`l] } ;
    Cos.{ name = Init ; path = Q.of_list [] } ;
  ] in
  compute_forms_simp scomb sderiv

let r x y = T.(App { head = Const ("r", Arrow (K.ty_i, Arrow (K.ty_i, K.ty_o))) ;
                     spine = [x ; y] })
let dbx n = T.(App { head = Index n ; spine = [] })

let qexch = Core.{
    tycx = empty ;
    data = mk_imp
        (mk_ex { var = "x" ; ty = K.ty_i }
           (mk_all { var = "y" ; ty = K.ty_i } (r (dbx 1) (dbx 0))))
        (mk_all { var = "y" ; ty = K.ty_i }
           (mk_ex { var = "x" ; ty = K.ty_i } (r (dbx 0) (dbx 1)))) }

let run_qexch () =
  let deriv = [
    Cos.{ name = Goal_ts_all ; path = Q.of_list [] } ;
    Cos.{ name = Goal_ex_ts ; path = Q.of_list [`d] } ;
    Cos.{ name = Goal_ts_ex ; path = Q.of_list [`d ; `d] } ;
    Cos.{ name = Goal_all_ts ; path = Q.of_list [`d ; `d ; `d] } ;
    Cos.{ name = Init ; path = Q.of_list [`d ; `d ; `d ; `d] } ;
    Cos.{ name = Inst (dbx 0) ; path = Q.of_list [`d ; `d] } ;
    Cos.{ name = Inst (dbx 1) ; path = Q.of_list [`d ; `d] } ;
  ] in
  compute_forms_simp qexch deriv

let scomb_d () =
  let deriv = ref [] in
  let emit rule = deriv := rule :: !deriv in
  compute_derivation ~emit @@ Link_form {
    goal = scomb ;
    src = Q.of_list [`l ; `r ; `r] ;
    dest = Q.of_list [`r ; `r ; `r] ;
  } ;
  compute_forms_simp scomb (List.rev !deriv)

let qexch_d () =
  let deriv = ref [] in
  let emit rule = deriv := rule :: !deriv in
  compute_derivation ~emit @@ Link_form {
    goal = qexch ;
    src = Q.of_list [`l ; `d ; `d] ;
    dest = Q.of_list [`r ; `d ; `d] ;
  } ;
  compute_forms_simp qexch (List.rev !deriv)

let tests =
  "Form4" >::: [
    "K-combinator COS" >:: begin fun _ ->
      let (_, prem) = run_kcomb () in
      assert_equal ~msg:"Premise" ~printer:LeanPP.to_string prem (Core.mk_top |@ kcomb)
    end ;
    "S-combinator COS" >:: begin fun _ ->
      let (_, prem) = run_scomb () in
      assert_equal ~msg:"Premise" ~printer:LeanPP.to_string prem (Core.mk_top |@ scomb)
    end ;
    "qexch COS" >:: begin fun _ ->
      let (_, prem) = run_qexch () in
      assert_equal ~msg:"Premise" ~printer:LeanPP.to_string prem (Core.mk_top |@ qexch)
    end ;
    "S-combinator DManip" >:: begin fun _ ->
      let (_, prem) = scomb_d () in
      let cmp f g = Term.eq_term f.data g.data in
      assert_equal ~printer:LeanPP.to_string ~cmp prem
        Core.(mk_imp (mk_imp a b) (mk_imp a (mk_and a b)) |@ scomb)
    end ;
    "qexch DManip" >:: begin fun _ ->
      let (_, prem) = qexch_d () in
      let cmp f g = Term.eq_term f.data g.data in
      assert_equal ~printer:LeanPP.to_string ~cmp prem
        Core.(mk_all { var = "x" ; ty = K.ty_i }
                (mk_all { var = "y" ; ty = K.ty_i }
                   (mk_ex { var = "x_1" ; ty = K.ty_i }
                      (mk_ex { var = "y_1" ; ty = K.ty_i }
                         (mk_and
                           (mk_eq (dbx 2) (dbx 1) K.ty_i)
                           (mk_eq (dbx 0) (dbx 3) K.ty_i))))) |@ qexch)
    end ;
  ]
