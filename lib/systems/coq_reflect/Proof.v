Require Import Profint.
Require Import List.
Import ListNotations.

Section Example.
Context {i : Type}.
Context {a : Prop}.
Context {b : Prop}.
Context {c : Prop}.
Context {f : i -> i}.
Context {g : i -> i -> i}.
Context {j : i}.
Context {k : i}.
Context {p : i -> Prop}.
Context {q : i -> Prop}.
Context {r : i -> i -> Prop}.
Goal (True) -> a /\ b -> b /\ a.
  let h := fresh "H" in
  intro h ;
  let deriv := fresh "deriv" in
  pose (deriv := [ (RN_contract, [])
                   (* a /\ b -> a /\ b -> b /\ a *) ;
                   (RN_goal_ts_and_l, [1])
                   (* a /\ b -> (a /\ b -> b) /\ a *) ;
                   (RN_goal_and_ts_r, [1;0])
                   (* a /\ b -> (b -> b) /\ a *) ;
                   (RN_init, [1;0])
                   (* a /\ b -> True /\ a *) ;
                   (RN_simp_goal_top_and, [1])
                   (* a /\ b -> a *) ;
                   (RN_goal_and_ts_l, [])
                   (* a -> a *) ;
                   (RN_init, [])
                   (* True *) ] : Profint.deriv) ;
  apply (Profint.correctness deriv) ;
  unfold deriv ; Profint.check_solve.
Qed.
End Example.

(*PROOF*)

(* All done *)
