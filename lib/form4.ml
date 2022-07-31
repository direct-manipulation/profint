(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Util
open Types

module Core = Form4_core
module Paths = Form4_paths
module Cos = Form4_cos
module Simplify = Form4_simplify
module Dmanip = Form4_dmanip

(******************************************************************************)
(* Testing *)

module Test = struct
  open T
  open Core

  let a = App { head = Const ("a", ty_o) ; spine = [] }
  let b = App { head = Const ("b", ty_o) ; spine = [] }
  let c = App { head = Const ("c", ty_o) ; spine = [] }

  let formx_to_string fx = Term.term_to_string ~cx:fx.tycx fx.data

  let rec compute_forms ?(hist = []) goal deriv =
    match deriv with
    | [] -> formx_to_string goal :: hist
    | rule :: deriv ->
        let prem = Cos.compute_premise goal rule in
        compute_forms prem deriv
          ~hist:(Cos.rule_to_string goal rule :: formx_to_string goal :: hist)

  let rec compute_forms_simp ?(hist = []) goal deriv =
    match deriv with
    | [] -> formx_to_string goal :: hist
    | rule :: deriv ->
        let prem = ref @@ Cos.compute_premise goal rule in
        let hist = ref @@ Cos.rule_to_string goal rule :: formx_to_string goal :: hist in
        let emit rule =
          hist := formx_to_string !prem :: !hist ;
          hist := Cos.rule_to_string !prem rule :: !hist ;
          prem := Cos.compute_premise !prem rule
        in
        let simp_prem = Simplify.recursive_simplify ~emit !prem Q.empty `r in
        compute_forms_simp simp_prem deriv ~hist:!hist

 let kcomb = { tycx = empty ; data = mk_imp a (mk_imp b a) }

  let t1 () =
    let kderiv = [
      Cos.{ name = Goal_ts_imp `r ; path = Q.empty   } ;
      Cos.{ name = Init           ; path = Q.singleton `r } ;
    ] in
    compute_forms_simp kcomb kderiv

  let scomb = { tycx = empty ;
                data = mk_imp (mk_imp a (mk_imp b c)) (mk_imp (mk_imp a b) (mk_imp a c)) }

  let t2 () =
    let sderiv = [
      Cos.{ name = Contract ; path = Q.of_list [`r ; `r] } ;
      Cos.{ name = Goal_ts_imp `l ; path = Q.of_list [`r] } ;
      Cos.{ name = Asms_imp { minor = `r ; pick = `l } ; path = Q.of_list [`r ; `l] } ;
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

  let r x y = App { head = Const ("r", Arrow (ty_i, Arrow (ty_i, ty_o))) ;
                    spine = [x ; y] }
  let dbx n = App { head = Index n ; spine = [] }

  let qexch = {
    tycx = empty ;
    data = mk_imp
        (mk_ex { var = "x" ; ty = ty_i }
           (mk_all { var = "y" ; ty = ty_i } (r (dbx 1) (dbx 0))))
        (mk_all { var = "y" ; ty = ty_i }
           (mk_ex { var = "x" ; ty = ty_i } (r (dbx 0) (dbx 1)))) }

  let t3 () =
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
    Dmanip.compute_derivation ~emit scomb @@ Link_form {
      src = Q.of_list [`l ; `r ; `r] ;
      dest = Q.of_list [`r ; `r ; `r] ;
    } ;
    compute_forms_simp scomb (List.rev !deriv)

  let qexch_d () =
    let deriv = ref [] in
    let emit rule = deriv := rule :: !deriv in
    Dmanip.compute_derivation ~emit qexch @@ Link_form {
      src = Q.of_list [`l ; `d ; `d] ;
      dest = Q.of_list [`r ; `d ; `d] ;
    } ;
    compute_forms_simp qexch (List.rev !deriv)
end
