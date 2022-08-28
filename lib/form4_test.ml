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
      Format.printf "CoS: %a@." Cos.pp_rule rule ;
      let prem = ref @@ Cos.compute_premise goal rule in
      let hist = ref @@ Cos.rule_to_string rule ::
                        LeanPP.to_string goal :: hist in
      let emit rule =
        hist := LeanPP.to_string !prem :: !hist ;
        hist := Cos.rule_to_string rule :: !hist ;
        prem := Cos.compute_premise !prem rule
      in
      let _simp_prem = recursive_simplify ~emit !prem Q.empty `r in
      compute_forms_simp !prem deriv ~hist:!hist

let and_ts_l_d () =
  let goal = Types.triv @@ mk_imp (mk_and a b) a in
  compute_derivation @@ Link {
    goal ;
    src = Q.of_list [`l ; `l] ;
    dest = Q.of_list [`r]
  }

let a_to_bot_to_b_or_c () =
  let goal = Types.triv @@
    mk_imp (mk_imp a mk_bot) (mk_or b c) in
  compute_derivation @@ Link {
    goal ;
    src = Q.of_list [`l ; `r] ;
    dest = Q.of_list [`r ; `l]
  } ;
