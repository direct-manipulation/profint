open Util
open Form4
open Types

let a = T.(App { head = Const ("a", K.ty_o) ; spine = [] })
let b = T.(App { head = Const ("b", K.ty_o) ; spine = [] })
let c = T.(App { head = Const ("c", K.ty_o) ; spine = [] })

let rec compute_forms_simp ?(hist = []) goal deriv =
  match deriv with
  | [] -> (formx_to_string goal :: hist, goal)
  | rule :: deriv ->
      (* Format.printf "CoS: %a [[ %a ]]@." Cos.pp_rule rule LeanPP.pp goal ; *)
      let prem = ref @@ Cos.compute_premise goal rule in
      let hist = ref @@ Cos.rule_to_string rule ::
                        formx_to_string goal :: hist in
      let emit rule =
        hist := formx_to_string !prem :: !hist ;
        hist := Cos.rule_to_string rule :: !hist ;
        prem := Cos.compute_premise !prem rule
      in
      let _simp_prem = recursive_simplify ~emit !prem Q.empty `r in
      compute_forms_simp !prem deriv ~hist:!hist

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
    Cos.{ name = Goal_ts_imp `r ; path = Q.of_list [] } ;
    Cos.{ name = Goal_ts_and `r ; path = Q.of_list [`r] } ;
    Cos.{ name = Goal_ts_and `l ; path = Q.of_list [] } ;
    Cos.{ name = Init ; path = Q.of_list [`l] } ;
    Cos.{ name = Init ; path = Q.of_list [] } ;
  ] in
  compute_forms_simp scomb sderiv

let and_ts_l_d () =
  let goal = Types.triv @@ mk_imp (mk_and a b) a in
  compute_derivation @@ Link {
    goal ;
    src = Q.of_list [`l ; `l] ;
    dest = Q.of_list [`r] ;
    copy = false ;
  }

let a_to_bot_to_b_or_c () =
  let goal = Types.triv @@
    mk_imp (mk_imp a mk_bot) (mk_or b c) in
  compute_derivation @@ Link {
    goal ;
    src = Q.of_list [`l ; `r] ;
    dest = Q.of_list [`r ; `l] ;
    copy = false ;
  } ;
