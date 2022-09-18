Unset Suggest Proof Using.

(* These are the transport combinators *)

Theorem go_left_and {a b c : Prop} :
  (a -> b) -> (a /\ c -> b /\ c).
Proof. intuition. Qed.

Theorem go_right_and {a b c : Prop} :
  (a -> b) -> (c /\ a -> c /\ b).
Proof. intuition. Qed.

Theorem go_left_or {a b c : Prop} :
  (a -> b) -> (a \/ c -> b \/ c).
Proof. intuition. Qed.

Theorem go_right_or {a b c : Prop} :
  (a -> b) -> (c \/ a -> c \/ b).
Proof. intuition. Qed.

Theorem go_left_imp {a b c : Prop} :
  (b -> a) -> ((a -> c) -> (b -> c)).
Proof. intuition. Qed.

Theorem go_right_imp {a b c : Prop} :
  (a -> b) -> ((c -> a) -> (c -> b)).
Proof. intuition. Qed.

Theorem go_down_all {T : Type} {p q : T -> Prop} :
  (forall x, p x -> q x) -> (forall x, p x) -> (forall x, q x).
Proof. intuition. Qed.

Theorem go_down_ex {T : Type} {p q : T -> Prop} :
  (forall x, p x -> q x) -> (exists x, p x) -> (exists x, q x).
Proof. intros Hpq (x & Hpx). exists x. exact (Hpq x Hpx). Qed.

(* These are the rule names *)

Theorem goal_ts_and_l {a b c : Prop} :
  ((a -> b) /\ c) -> (a -> (b /\ c)).
Proof. intuition. Qed.

Theorem goal_ts_and_r {a b c : Prop} :
  (c /\ (a -> b)) -> (a -> (c /\ b)).
Proof. intuition. Qed.

Theorem goal_and_ts_l {a b c : Prop} :
  (a -> b) -> (a /\ c -> b).
Proof. intuition. Qed.

Theorem goal_and_ts_r {a b c : Prop} :
  (a -> b) -> (c /\ a -> b).
Proof. intuition. Qed.

Theorem goal_ts_or_l {a b c : Prop} :
  (a -> b) -> (a -> b \/ c).
Proof. intuition. Qed.

Theorem goal_ts_or_r {a b c : Prop} :
  (a -> b) -> (a -> c \/ b).
Proof. intuition. Qed.

Theorem goal_or_ts {a b c : Prop} :
  ((a -> c) /\ (b -> c)) -> (a \/ b -> c).
Proof. intuition. Qed.

Theorem goal_ts_imp_l {a b c : Prop} :
  (a /\ b -> c) -> (a -> b -> c).
Proof. intuition. Qed.

Theorem goal_ts_imp_r {a b c : Prop} :
  (c -> a -> b) -> (a -> c -> b).
Proof. intuition. Qed.

Theorem goal_imp_ts {a b c : Prop} :
  (c /\ (a -> b)) -> ((c -> a) -> b).
Proof. intuition. Qed.

Theorem goal_ts_all {T : Type} {a : Prop} {p : T -> Prop} :
  (forall x, a -> p x) -> (a -> forall x, p x).
Proof. intuition. Qed.

Theorem goal_all_ts {T : Type} {b : Prop } {p : T -> Prop} :
  (exists x, p x -> b) -> (forall x, p x) -> b.
Proof. intros (x & Hpb) Hp. exact (Hpb (Hp x)). Qed.

Theorem goal_ts_ex {T : Type} {a : Prop } {p : T -> Prop} :
  (exists x, a -> p x) -> (a -> exists x, p x).
Proof. intros (x & Hap) Ha. exists x. exact (Hap Ha). Qed.

Theorem goal_ex_ts {T : Type} {a : Prop} {p : T -> Prop} :
  (forall x, p x -> a) -> (exists x, p x) -> a.
Proof. intros H (x & Hp). exact (H x Hp). Qed.

Theorem asms_and_l_l {a b c : Prop } :
  (a /\ (b /\ c)) -> (a /\ b).
Proof. intuition. Qed.

Theorem asms_and_l_r {a b c : Prop } :
  (a /\ (c /\ b)) -> (a /\ b).
Proof. intuition. Qed.

Theorem asms_and_r_l {a b c : Prop } :
  ((a /\ c) /\ b) -> (a /\ b).
Proof. intuition. Qed.

Theorem asms_and_r_r {a b c : Prop } :
  ((c /\ a) /\ b) -> (a /\ b).
Proof. intuition. Qed.

Theorem asms_or_l_l {a b c : Prop } :
  (a /\ (b \/ c)) -> ((a /\ b) \/ c).
Proof. intuition. Qed.

Theorem asms_or_l_r {a b c : Prop } :
  (a /\ (c \/ b)) -> (c \/ (a /\ b)).
Proof. intuition. Qed.

Theorem asms_or_r_l {a b c : Prop } :
  ((a \/ c) /\ b) -> ((a /\ b) \/ c).
Proof. intuition. Qed.

Theorem asms_or_r_r {a b c : Prop} :
  ((c \/ a) /\ b) -> (c \/ (a /\ b)).
Proof. intuition. Qed.

Theorem asms_imp_l_l {a b c : Prop} :
  (a /\ (b -> c)) -> ((a -> b) -> c).
Proof. intuition. Qed.

Theorem asms_imp_l_r {a b c : Prop} :
  (a /\ (c -> b)) -> (c -> (a /\ b)).
Proof. intuition. Qed.

Theorem asms_imp_r_l {a b c : Prop} :
  ((a -> c) /\ b) -> ((b -> a) -> c).
Proof. intuition. Qed.

Theorem asms_imp_r_r {a b c : Prop} :
  ((c -> a) /\ b) -> (c -> (a /\ b)).
Proof. intuition. Qed.

Theorem asms_all_l {T : Type} {a : Prop} {p : T -> Prop} :
  (a /\ forall x, p x) -> forall x, (a /\ p x).
Proof. intuition. Qed.

Theorem asms_all_r {T : Type} {a : Prop} {p : T -> Prop} :
  ((forall x, p x) /\ a) -> forall x, (p x /\ a).
Proof. intuition. Qed.

Theorem asms_ex_l {T : Type} {a : Prop} {p : T -> Prop} :
  (a /\ exists x, p x) -> exists x, (a /\ p x).
Proof. intros (Ha & x & Hp). exists x. auto. Qed.

Theorem asms_ex_r {T : Type} {a : Prop} {p : T -> Prop} :
  ((exists x, p x) /\ a) -> exists x, (p x /\ a).
Proof. intros ((x & Hp) & Ha). exists x. intuition. Qed.

Theorem contract {a b : Prop} :
  (a -> a -> b) -> (a -> b).
Proof. intuition. Qed.

Theorem weaken {a b : Prop} :
  b -> (a -> b).
Proof. intuition. Qed.

Theorem inst_r {T : Type} {p : T -> Prop} (t : T) :
  p t -> (exists x, p x).
Proof. exists t. trivial. Qed.

Theorem inst_l {T : Type} {p : T -> Prop} (t : T) :
  (forall x, p x) -> p t.
Proof. intuition. Qed.

Theorem rewrite_rtl {T : Type} {s t : T} {p : T -> Prop} :
  p s -> s = t -> p t.
Proof. intros x q. rewrite <- q. trivial. Qed.

Theorem rewrite_ltr {T : Type} {s t : T} {p : T -> Prop} :
  p t -> s = t -> p s.
Proof. intros x q. rewrite q. trivial. Qed.

Theorem simp_goal_and_top {a : Prop} : a -> (a /\ True).
Proof. intuition. Qed.

Theorem simp_goal_top_and {a : Prop} : a -> (True /\ a).
Proof. intuition. Qed.

Theorem simp_asms_and_top {a : Prop} : (a /\ True) -> a.
Proof. intuition. Qed.

Theorem simp_asms_top_and {a : Prop} : (True /\ a) -> a.
Proof. intuition. Qed.

Theorem simp_goal_or_top {a : Prop}  : True -> (a \/ True).
Proof. intuition. Qed.

Theorem simp_goal_top_or {a : Prop}  : True -> (True \/ a).
Proof. intuition. Qed.

Theorem simp_asms_or_top {a : Prop}  : (a \/ True) -> True.
Proof. intuition. Qed.

Theorem simp_asms_top_or {a : Prop}  : (True \/ a) -> True.
Proof. intuition. Qed.

Theorem simp_goal_imp_top {a : Prop} : True -> (a -> True).
Proof. intuition. Qed.

Theorem simp_goal_top_imp {a : Prop} : a -> (True -> a).
Proof. intuition. Qed.

Theorem simp_asms_imp_top {a : Prop} : (a -> True) -> True.
Proof. intuition. Qed.

Theorem simp_asms_top_imp {a : Prop} : (True -> a) -> a.
Proof. intuition. Qed.

Theorem simp_goal_and_bot {a : Prop} : False -> (a /\ False).
Proof. intuition. Qed.

Theorem simp_goal_bot_and {a : Prop} : False -> (False /\ a).
Proof. intuition. Qed.

Theorem simp_asms_and_bot {a : Prop} : (a /\ False) -> False.
Proof. intuition. Qed.

Theorem simp_asms_bot_and {a : Prop} : (False /\ a) -> False.
Proof. intuition. Qed.

Theorem simp_goal_or_bot  {a : Prop} : a -> (a \/ False).
Proof. intuition. Qed.

Theorem simp_goal_bot_or  {a : Prop} : a -> (False \/ a).
Proof. intuition. Qed.

Theorem simp_asms_or_bot  {a : Prop} : (a \/ False) -> a.
Proof. intuition. Qed.

Theorem simp_asms_bot_or  {a : Prop} : (False \/ a) -> a.
Proof. intuition. Qed.

Theorem simp_goal_bot_imp {a : Prop} : True -> (False -> a).
Proof. intuition. Qed.

Theorem simp_asms_bot_imp {a : Prop} : (False -> a) -> True.
Proof. intuition. Qed.

Theorem simp_goal_all_top {T : Type} : True -> forall (_ : T), True.
Proof. intuition. Qed.

Theorem simp_asms_all_top {T : Type} : (forall (_ : T), True) -> True.
Proof. intuition. Qed.

Theorem simp_goal_ex_bot {T : Type} : False -> exists (_ : T), False.
Proof. intuition. Qed.

Theorem simp_asms_ex_bot {T : Type} : (exists (_ : T), False) -> False.
Proof. intro h ; destruct h as (_ & h) ; destruct h. Qed.

(* This ltac proves lemmas generated by init/congr *)

Ltac profint_discharge_lemma :=
  match goal with
  | [ |- True -> _ ] =>
      let h := fresh "H" in
      intro h ; clear h
  | [ |- @eq _ _ _ -> _ ] =>
      let h := fresh "H" in
      intro h ; try rewrite h ; clear h
  | [ |- ((@eq _ _ _) /\ _) -> _ ] =>
      let h1 := fresh "H" in
      let h2 := fresh "H" in
      intros (h1 & h2) ; revert h2 ; try rewrite h1 ; clear h1 ;
      profint_discharge_lemma
  end ; trivial.
