namespace Profint

universe  u
variable  {T : Type u}
variables {a b c : Prop}
variables {p q : T -> Prop}

-- These utility theorems are used for traversal

theorem go_left_and : (a → b) → (a ∧ c → b ∧ c) :=
  fun f ac, and.intro (f (and.left ac)) (and.right ac)
theorem go_right_and : (a → b) → (c ∧ a → c ∧ b) :=
  fun f ca, and.intro (and.left ca) (f (and.right ca))
theorem go_left_or : (a → b) → (a ∨ c → b ∨ c) :=
  fun f ac, or.elim ac (fun x, or.inl (f x)) or.inr
theorem go_right_or : (a → b) → (c ∨ a → c ∨ b) :=
  fun f ca, or.elim ca or.inl (fun x, or.inr (f x))
theorem go_left_imp : (b → a) → ((a → c) → (b → c)) :=
  fun f ac x, ac (f x)
theorem go_right_imp : (a → b) → ((c → a) → (c → b)) :=
  fun f ca x, f (ca x)
theorem go_down_all : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun f a x, f x (a x)
theorem go_down_ex : (∀ x, p x → q x) → (∃ x, p x) → (∃ x, q x) :=
  fun f a, exists.elim a (fun x px, exists.intro x (f x px))

-- These are the rule names

theorem goal_ts_and_l : ((a → b) ∧ c) → (a → (b ∧ c)) :=
  fun x y, and.intro (and.left x y) (and.right x)
theorem goal_ts_and_r : (c ∧ (a → b)) → (a → (c ∧ b)) :=
  fun x y, and.intro (and.left x) (and.right x y)
theorem goal_and_ts_l : (a → b) → (a ∧ c → b) :=
  fun f x, f (and.left x)
theorem goal_and_ts_r : (a → b) → (c ∧ a → b) :=
  fun f x, f (and.right x)
theorem goal_ts_or_l : (a → b) → (a → b ∨ c) :=
  fun f x, or.inl (f x)
theorem goal_ts_or_r : (a → b) → (a → c ∨ b) :=
  fun f x, or.inr (f x)
theorem goal_or_ts : ((a → c) ∧ (b → c)) → (a ∨ b → c) :=
  fun ff xab, or.elim xab (fun xa, and.left ff xa) (fun xb, and.right ff xb)
theorem goal_ts_imp_l : (a ∧ b → c) → (a → b → c) :=
  fun f x y, f (and.intro x y)
theorem goal_ts_imp_r : (c → a → b) → (a → c → b) :=
  fun f x y, f y x
theorem goal_imp_ts : (c ∧ (a → b)) → ((c → a) → b) :=
  fun ff g, and.right ff (g (and.left ff))
theorem goal_ts_all : (∀ x, a → p x) → (a → ∀ x, p x) :=
  fun ff xa x, ff x xa
theorem goal_all_ts : (∃ x, p x → b) → (∀ x, p x) → b :=
  fun fex g, exists.elim fex (fun x f, f (g x))
theorem goal_ts_ex : (∃ x, a → p x) → (a → ∃ x, p x) :=
  fun fex xa, exists.elim fex (fun x f, exists.intro x (f xa))
theorem goal_ex_ts : (∀ x, p x → a) → (∃ x, p x) → a :=
  fun ff xpex, exists.elim xpex (fun x xp, ff x xp)
theorem asms_and_l_l : (a ∧ (b ∧ c)) → (a ∧ b) :=
  fun xabc, and.intro (and.left xabc) (and.left (and.right xabc))
theorem asms_and_l_r : (a ∧ (c ∧ b)) → (a ∧ b) :=
  fun xabc, and.intro (and.left xabc) (and.right (and.right xabc))
theorem asms_and_r_l : ((a ∧ c) ∧ b) → (a ∧ b) :=
  fun xacb, and.intro (and.left (and.left xacb)) (and.right xacb)
theorem asms_and_r_r : ((c ∧ a) ∧ b) → (a ∧ b) :=
  fun xacb, and.intro (and.right (and.left xacb)) (and.right xacb)
theorem asms_or_l_l : (a ∧ (b ∨ c)) → ((a ∧ b) ∨ c) :=
  fun xabc, or.elim (and.right xabc) (fun xb, or.inl (and.intro (and.left xabc) xb)) or.inr
theorem asms_or_l_r : (a ∧ (c ∨ b)) → (c ∨ (a ∧ b)) :=
  fun xacb, or.elim (and.right xacb) or.inl (fun xb, or.inr (and.intro (and.left xacb) xb))
theorem asms_or_r_l : ((a ∨ c) ∧ b) → ((a ∧ b) ∨ c) :=
  fun xacb, or.elim (and.left xacb) (fun xa, or.inl (and.intro xa (and.right xacb))) or.inr
theorem asms_or_r_r : ((c ∨ a) ∧ b) → (c ∨ (a ∧ b)) :=
  fun xcab, or.elim (and.left xcab) or.inl (fun xa, or.inr (and.intro xa (and.right xcab)))
theorem asms_imp_l_l : (a ∧ (b → c)) → ((a → b) → c) :=
  fun xaf g, and.right xaf (g (and.left xaf))
theorem asms_imp_l_r : (a ∧ (c → b)) → (c → (a ∧ b)) :=
  fun xaf xc, and.intro (and.left xaf) (and.right xaf xc)
theorem asms_imp_r_l : ((a → c) ∧ b) → ((b → a) → c) :=
  fun xfb g, and.left xfb (g (and.right xfb))
theorem asms_imp_r_r : ((c → a) ∧ b) → (c → (a ∧ b)) :=
  fun xfb xc, and.intro (and.left xfb xc) (and.right xfb)
theorem asms_all_l : (a ∧ ∀ x, p x) → ∀ x, (a ∧ p x) :=
  fun xaf x, and.intro (and.left xaf) (and.right xaf x)
theorem asms_all_r : ((∀ x, p x) ∧ a) → ∀ x, (p x ∧ a) :=
  fun fxa x, and.intro (and.left fxa x) (and.right fxa)
theorem asms_ex_l : (a ∧ ∃ x, p x) → ∃ x, (a ∧ p x) :=
  fun xaep, exists.elim (and.right xaep) (fun x xp, exists.intro x (and.intro (and.left xaep) xp))
theorem asms_ex_r : ((∃ x, p x) ∧ a) → ∃ x, (p x ∧ a) :=
  fun epxa, exists.elim (and.left epxa) (fun x xp, exists.intro x (and.intro xp (and.right epxa)))
theorem contract : (a → a → b) → (a → b) :=
  fun f xa, f xa xa
theorem weaken : b → (a → b) :=
  fun xb xa, xb
theorem inst (t : T) : p t → (∃ x, p x) :=
  exists.intro t
theorem inst_all (t : T): (∀ x, p x) → p t :=
  fun f, f t
theorem simp_imp_true : true → a → true :=
  fun _ _, true.intro
theorem simp_true_imp_r : a → (true → a) :=
  fun xa _, xa
theorem simp_true_imp_l : (true → a) → a :=
  fun f, f true.intro
theorem simp_false_imp : true → (false → a) :=
  fun _, false.elim
theorem simp_and_true_l : a → (a ∧ true) :=
  fun xa, and.intro xa true.intro
theorem simp_and_true_r : a → (true ∧ a) :=
  fun xa, and.intro true.intro xa
theorem simp_or_true_l : true → (a ∨ true) :=
  fun _, or.inr true.intro
theorem simp_or_true_r : true -> (true ∨ a) :=
  fun _, or.inl true.intro
theorem simp_all_true : true → ∀ (_ : T), true :=
  fun _ _, true.intro

open tactic

meta def profint_discharge : tactic unit := do
  h ← get_unused_name `h none,
  he ← intro h,
  ht ← infer_type he >>= whnf,
  match ht with
  | `(and _ %%b) := do
    hq ← mk_mapp ``and.left [none, none, some he],
    try (rewrite_target hq),
    hrest ← mk_mapp ``and.right [none, none, some he],
    clear he,
    assertv h b hrest >>= revert,
    profint_discharge
  | _ := do
    try (rewrite_target he),
    clear he,
    -- could also match target to discriminate these two cases
    `[exact id <|> apply eq.refl]
  end

/- ignore this namespace -/
namespace Debug

theorem init0 (f : Prop) :
   true → f → f :=
by profint_discharge

theorem congr0 (f : T) :
   true → f = f :=
by profint_discharge

theorem init1 (s t : T) (f : T → Prop) :
   s = t → f s → f t :=
by profint_discharge

theorem congr1 (s t : T) (f : T → T) :
   s = t → f s = f t :=
by profint_discharge

theorem initN (s t u v z w : T) (f : T → T → T → Prop) :
   s = t ∧ u = v ∧ z = w → f s u z → f t v w :=
by profint_discharge

theorem congrN (s t u v z w : T) (f : T → T → T → T) :
   s = t ∧ u = v ∧ z = w → f s u z = f t v w :=
by profint_discharge

end Debug

end Profint
