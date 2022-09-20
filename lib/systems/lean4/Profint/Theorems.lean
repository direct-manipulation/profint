-- Transport and Rule combinators

namespace Profint

section Profint_theorems

universe u v
variable {T : Type u}
variable {a b c : Prop}
variable {p q : T → Prop}

/- These are the transport combinators -/

theorem go_left_and : (a → b) → (a ∧ c → b ∧ c) :=
  fun f ac => ⟨f ac.1, ac.2⟩
theorem go_right_and : (a → b) → (c ∧ a → c ∧ b) :=
  fun f ca => ⟨ca.1, f ca.2⟩
theorem go_left_or : (a → b) → (a ∨ c → b ∨ c) :=
  fun f ac => ac.elim (fun x => Or.inl (f x)) (fun x => Or.inr x)
theorem go_right_or : (a → b) → (c ∨ a → c ∨ b) :=
  fun f ca => ca.elim (fun x => Or.inl x) (fun x => Or.inr (f x))
theorem go_left_imp : (b → a) → ((a → c) → (b → c)) :=
  fun f ac x => ac (f x)
theorem go_right_imp : (a → b) → ((c → a) → (c → b)) :=
  fun f ca x => f (ca x)
theorem go_down_all : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun qf qa x => qf x (qa x)
theorem go_down_ex : (∀ x, p x → q x) → (∃ x, p x) → (∃ x, q x) :=
  fun qf qa => qa.elim (fun x pf => ⟨x, qf x pf⟩)

/- These are the rule names -/

theorem goal_ts_and_l : ((a → b) ∧ c) → (a → (b ∧ c))     := fun x y => ⟨x.1 y, x.2⟩
theorem goal_ts_and_r : (c ∧ (a → b)) → (a → (c ∧ b))     := fun x y => ⟨x.1, x.2 y⟩
theorem goal_and_ts_l : (a → b) → (a ∧ c → b)             := fun x y => x y.1
theorem goal_and_ts_r : (a → b) → (c ∧ a → b)             := fun x y => x y.2
theorem goal_ts_or_l  : (a → b) → (a → b ∨ c)             := fun x y => Or.inl (x y)
theorem goal_ts_or_r  : (a → b) → (a → c ∨ b)             := fun x y => Or.inr (x y)
theorem goal_or_ts    : ((a → c) ∧ (b → c)) → (a ∨ b → c) := fun x y => match y with | .inl u => x.1 u | .inr v => x.2 v
theorem goal_ts_imp_l : (a ∧ b → c) → (a → b → c)         := fun f x y => f ⟨x, y⟩
theorem goal_ts_imp_r : (c → a → b) → (a → c → b)         := fun k x y => k y x
theorem goal_imp_ts   : (c ∧ (a → b)) → ((c → a) → b)     := fun x y => x.2 (y x.1)
theorem goal_ts_all   : (∀ x, a → p x) → (a → ∀ x, p x)   := fun x y z => x z y
theorem goal_all_ts   : (∃ x, p x → b) → (∀ x, p x) → b   := fun x y => match x with | .intro u f => f (y u)
theorem goal_ts_ex    : (∃ x, a → p x) → (a → ∃ x, p x)   := fun x y => match x with | .intro u f => Exists.intro u (f y)
theorem goal_ex_ts    : (∀ x, p x → a) → (∃ x, p x) → a   := fun x y => match y with | .intro u z => x u z

theorem asms_and_l_l : (a ∧ (b ∧ c)) → (a ∧ b)           := fun x => ⟨x.1, x.2.1⟩
theorem asms_and_l_r : (a ∧ (c ∧ b)) → (a ∧ b)           := fun x => ⟨x.1, x.2.2⟩
theorem asms_and_r_l : ((a ∧ c) ∧ b) → (a ∧ b)           := fun x => ⟨x.1.1, x.2⟩
theorem asms_and_r_r : ((c ∧ a) ∧ b) → (a ∧ b)           := fun x => ⟨x.1.2, x.2⟩
theorem asms_or_l_l  : (a ∧ (b ∨ c)) → ((a ∧ b) ∨ c)     := fun x => match x.2 with | .inl u => Or.inl ⟨x.1, u⟩ | .inr u => Or.inr u
theorem asms_or_l_r  : (a ∧ (c ∨ b)) → (c ∨ (a ∧ b))     := fun x => match x.2 with | .inl u => Or.inl u | .inr u => Or.inr ⟨x.1, u⟩
theorem asms_or_r_l  : ((a ∨ c) ∧ b) → ((a ∧ b) ∨ c)     := fun x => match x.1 with | .inl u => Or.inl ⟨u, x.2⟩ | .inr u => Or.inr u
theorem asms_or_r_r  : ((c ∨ a) ∧ b) → (c ∨ (a ∧ b))     := fun x => match x.1 with | .inl u => Or.inl u | .inr u => Or.inr ⟨u, x.2⟩
theorem asms_imp_l_l : (a ∧ (b → c)) → ((a → b) → c)     := fun x y => x.2 (y x.1)
theorem asms_imp_l_r : (a ∧ (c → b)) → (c → (a ∧ b))     := fun x y => ⟨x.1, x.2 y⟩
theorem asms_imp_r_l : ((a → c) ∧ b) → ((b → a) → c)     := fun x y => x.1 (y x.2)
theorem asms_imp_r_r : ((c → a) ∧ b) → (c → (a ∧ b))     := fun x y => ⟨x.1 y, x.2⟩
theorem asms_all_l   : (a ∧ ∀ x, p x) → ∀ x, (a ∧ p x)   := fun x y => ⟨x.1, x.2 y⟩
theorem asms_all_r   : ((∀ x, p x) ∧ a) → ∀ x, (p x ∧ a) := fun x y => ⟨x.1 y, x.2⟩
theorem asms_ex_l    : (a ∧ ∃ x, p x) → ∃ x, (a ∧ p x)   := fun x => match x.2 with | .intro y u => Exists.intro y ⟨x.1, u⟩
theorem asms_ex_r    : ((∃ x, p x) ∧ a) → ∃ x, (p x ∧ a) := fun x => match x.1 with | .intro y u => Exists.intro y ⟨u, x.2⟩

theorem contract : (a → a → b) → (a → b) := fun f x => f x x
theorem weaken   : b → (a → b)           := fun x _ => x
theorem inst_r t : p t → (∃ x, p x)      := fun f => Exists.intro t f
theorem inst_l t : (∀ x, p x) → p t      := fun f => f t

theorem simp_goal_and_top : a → (a ∧ True)      := fun x => And.intro x True.intro
theorem simp_goal_top_and : a → (True ∧ a)      := fun x => And.intro True.intro x
theorem simp_asms_and_top : (a ∧ True) → a      := fun x => x.1
theorem simp_asms_top_and : (True ∧ a) → a      := fun x => x.2

theorem simp_goal_or_top  : True → (a ∨ True)   := fun _ => Or.inr True.intro
theorem simp_goal_top_or  : True → (True ∨ a)   := fun _ => Or.inl True.intro
theorem simp_asms_or_top  : (a ∨ True) → True   := fun _ => True.intro
theorem simp_asms_top_or  : (True ∨ a) → True   := fun _ => True.intro

theorem simp_goal_imp_top : True → (a → True)   := fun _ _ => True.intro
theorem simp_goal_top_imp : a → (True → a)      := fun x _ => x
theorem simp_asms_imp_top : (a → True) → True   := fun _ => True.intro
theorem simp_asms_top_imp : (True → a) → a      := fun x => x True.intro

theorem simp_goal_and_bot : False → (a ∧ False) := fun x => False.elim x
theorem simp_goal_bot_and : False → (False ∧ a) := fun x => False.elim x
theorem simp_asms_and_bot : (a ∧ False) → False := fun x => False.elim x.2
theorem simp_asms_bot_and : (False ∧ a) → False := fun x => False.elim x.1

theorem simp_goal_or_bot  : a → (a ∨ False)     := fun x => Or.inl x
theorem simp_goal_bot_or  : a → (False ∨ a)     := fun x => Or.inr x
theorem simp_asms_or_bot  : (a ∨ False) → a     := fun x => match x with | .inl u => u | .inr u => False.elim u
theorem simp_asms_bot_or  : (False ∨ a) → a     := fun x => match x with | .inl u => False.elim u | .inr u => u

theorem simp_goal_bot_imp : True → (False → a)  := fun _ x => False.elim x
theorem simp_asms_bot_imp : (False → a) → True  := fun _ => True.intro

theorem simp_goal_all_top : True → ∀ (_ : T), True     := fun _ _ => True.intro
theorem simp_asms_all_top : (∀ (_ : T), True) → True   := fun _ => True.intro
theorem simp_goal_ex_bot  : False → ∃ (_ : T), False   := fun x => False.elim x
theorem simp_asms_ex_bot  : (∃ (_ : T), False) → False := fun x => Exists.elim x (fun _ u => False.elim u)

end Profint_theorems

end Profint

-- Local Variables:
-- mode: lean4
-- End:
