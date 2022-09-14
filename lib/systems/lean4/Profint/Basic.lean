-- Setup for lean4 proofs from the profint web tool
-- https://chaudhuri.info/research/profint/

import Lean

namespace Profint

section Profint_theorems

universe u v
variable {T : Type u}
variable {a b c : Prop}
variable {p q : T → Prop}

/- These utility theorems are used for traversal -/

theorem go_left_and : (a → b) → (a ∧ c → b ∧ c) :=
  fun f ac => ⟨f ac.1, ac.2⟩
theorem go_right_and : (a → b) → (c ∧ a → c ∧ b) :=
  fun f ca => ⟨ca.1, f ca.2⟩
theorem go_left_or : (a → b) → (a ∨ c → b ∨ c) :=
  fun f ac => match ac with | .inl x => Or.inl (f x) | .inr x => Or.inr x
theorem go_right_or : (a → b) → (c ∨ a → c ∨ b) :=
  fun f ca => match ca with | .inl x => Or.inl x | .inr x => Or.inr (f x)
theorem go_left_imp : (b → a) → ((a → c) → (b → c)) :=
  fun f ac x => ac (f x)
theorem go_right_imp : (a → b) → ((c → a) → (c → b)) :=
  fun f ca x => f (ca x)
theorem go_down_all : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun qf qa x => qf x (qa x)
theorem go_down_ex : (∀ x, p x → q x) → (∃ x, p x) → (∃ x, q x) :=
  fun qf qa => match qa with | .intro x pf => Exists.intro x (qf x pf)

/- These are the rule names -/

theorem goal_ts_and_l   : ((a → b) ∧ c) → (a → (b ∧ c))         := fun x y => ⟨x.1 y, x.2⟩
theorem goal_ts_and_r   : (c ∧ (a → b)) → (a → (c ∧ b))         := fun x y => ⟨x.1, x.2 y⟩
theorem goal_and_ts_l   : (a → b) → (a ∧ c → b)                 := fun x y => x y.1
theorem goal_and_ts_r   : (a → b) → (c ∧ a → b)                 := fun x y => x y.2
theorem goal_ts_or_l    : (a → b) → (a → b ∨ c)                 := fun x y => Or.inl (x y)
theorem goal_ts_or_r    : (a → b) → (a → c ∨ b)                 := fun x y => Or.inr (x y)
theorem goal_or_ts      : ((a₁ → b) ∧ (a₂ → b)) → (a₁ ∨ a₂ → b) := fun x y => match y with | .inl u => x.1 u | .inr v => x.2 v
theorem goal_ts_imp_l   : (a ∧ b → c) → (a → b → c)             := fun f x y => f ⟨x, y⟩
theorem goal_ts_imp_r   : (c → a → b) → (a → c → b)             := fun k x y => k y x
theorem goal_imp_ts     : (c ∧ (a → b)) → ((c → a) → b)         := fun x y => x.2 (y x.1)
theorem goal_ts_all     : (∀ x, a → p x) → (a → ∀ x, p x)       := fun x y z => x z y
theorem goal_all_ts     : (∃ x, p x → b) → (∀ x, p x) → b       := fun x y => match x with | .intro u f => f (y u)
theorem goal_ts_ex      : (∃ x, a → p x) → (a → ∃ x, p x)       := fun x y => match x with | .intro u f => Exists.intro u (f y)
theorem goal_ex_ts      : (∀ x, p x → a) → (∃ x, p x) → a       := fun x y => match y with | .intro u z => x u z

theorem asms_and_l_l    : (a ∧ (b ∧ c)) → (a ∧ b)               := fun x => ⟨x.1, x.2.1⟩
theorem asms_and_l_r    : (a ∧ (c ∧ b)) → (a ∧ b)               := fun x => ⟨x.1, x.2.2⟩
theorem asms_and_r_l    : ((a ∧ c) ∧ b) → (a ∧ b)               := fun x => ⟨x.1.1, x.2⟩
theorem asms_and_r_r    : ((c ∧ a) ∧ b) → (a ∧ b)               := fun x => ⟨x.1.2, x.2⟩
theorem asms_or_l_l     : (a ∧ (b ∨ c)) → ((a ∧ b) ∨ c)         := fun x => match x.2 with | .inl u => Or.inl ⟨x.1, u⟩ | .inr u => Or.inr u
theorem asms_or_l_r     : (a ∧ (c ∨ b)) → (c ∨ (a ∧ b))         := fun x => match x.2 with | .inl u => Or.inl u | .inr u => Or.inr ⟨x.1, u⟩
theorem asms_or_r_l     : ((a ∨ c) ∧ b) → ((a ∧ b) ∨ c)         := fun x => match x.1 with | .inl u => Or.inl ⟨u, x.2⟩ | .inr u => Or.inr u
theorem asms_or_r_r     : ((c ∨ a) ∧ b) → (c ∨ (a ∧ b))         := fun x => match x.1 with | .inl u => Or.inl u | .inr u => Or.inr ⟨u, x.2⟩
theorem asms_imp_l_l    : (a ∧ (b → c)) → ((a → b) → c)         := fun x y => x.2 (y x.1)
theorem asms_imp_l_r    : (a ∧ (c → b)) → (c → (a ∧ b))         := fun x y => ⟨x.1, x.2 y⟩
theorem asms_imp_r_l    : ((a → c) ∧ b) → ((b → a) → c)         := fun x y => x.1 (y x.2)
theorem asms_imp_r_r    : ((c → a) ∧ b) → (c → (a ∧ b))         := fun x y => ⟨x.1 y, x.2⟩
theorem asms_all_l      : (a ∧ ∀ x, p x) → ∀ x, (a ∧ p x)       := fun x y => ⟨x.1, x.2 y⟩
theorem asms_all_r      : ((∀ x, p x) ∧ a) → ∀ x, (p x ∧ a)     := fun x y => ⟨x.1 y, x.2⟩
theorem asms_ex_l       : (a ∧ ∃ x, p x) → ∃ x, (a ∧ p x)       := fun x => match x.2 with | .intro y u => Exists.intro y ⟨x.1, u⟩
theorem asms_ex_r       : ((∃ x, p x) ∧ a) → ∃ x, (p x ∧ a)     := fun x => match x.1 with | .intro y u => Exists.intro y ⟨u, x.2⟩

theorem contract        : (a → a → b) → (a → b)                 := fun f x => f x x
theorem weaken          : b → (a → b)                           := fun x _ => x
theorem inst_r t        : p t → (∃ x, p x)                      := fun f => Exists.intro t f
theorem inst_l t        : (∀ x, p x) → p t                      := fun f => f t
theorem rewrite_rtl {s t} : p s → (s = t) → p t                 := fun x q => q ▸ x
theorem rewrite_ltr {s t} : p t → (s = t) → p s                 := fun x q => q ▸ x

theorem simp_imp_true   : True → a → True                       := fun _ _ => True.intro
theorem simp_true_imp_r : a → (True → a)                        := fun x _ => x
theorem simp_true_imp_l : (True → a) → a                        := fun x => x True.intro
theorem simp_false_imp  : True → (False → a)                    := fun _ x => x.elim
theorem simp_and_true_l : a → (a ∧ True)                        := fun x => ⟨x, True.intro⟩
theorem simp_and_true_r : a → (True ∧ a)                        := fun x => ⟨True.intro, x⟩
theorem simp_or_true_l  : True → (a ∨ True)                     := fun _ => Or.inr True.intro
theorem simp_or_true_r  : True -> (True ∨ a)                    := fun _ => Or.inl True.intro
theorem simp_all_true   : True → ∀ (_ : T), True                := fun _ _ => True.intro

end Profint_theorems

section Profint_paths

open Lean Parser.Tactic Elab Elab.Tactic Meta

inductive Direction : Type where
  | l (count : Nat)
  | r (count : Nat)
  | d (count : Nat)
  | i (x : Ident) (xs : List Ident)
deriving Inhabited

def Direction.toString (d : Direction) :=
  match d with
  | .l n => s!"(l {n})"
  | .r n => s!"(r {n})"
  | .d n => s!"(d {n})"
  | .i x xs => s!"(i {x} {xs})"

instance : ToString Direction := ⟨Direction.toString⟩

abbrev Path := Array Direction

def pushN.{u} {α : Type u} (arr : Array α) (thing : α) (n : Nat) :=
  match n with
  | 0 => arr
  | n + 1 => pushN (arr.push thing) thing n

def parseDirectionAlt (stx : Term) (arr : Path) : CoreM Path :=
  match stx with
  | `(l $n:num) => pure <| pushN arr (Direction.l 1) n.getNat
  | `(l)        => pure <| arr.push (Direction.l 1)
  | _ => throwErrorAt stx s!"illegal direction"

def parseDirection (stx : Term) : TacticM Direction :=
  match stx with
  | `(l $n:num) => return Direction.l n.getNat
  | `(l)        => return Direction.l 1
  | `(r $n:num) => return Direction.r n.getNat
  | `(r)        => return Direction.r 1
  | `(d $n:num) => return Direction.d n.getNat
  | `(d)        => return Direction.d 1
  | `(i $x:ident $xs:ident* ) => return Direction.i x xs.toList
  | _ => throwErrorAt stx s!"not a valid direction"

def parsePath (stx : Array Term) : TacticM Path := do
  stx.sequenceMap parseDirection

def Direction.size (d : Direction) : Nat :=
  match d with
  | .l n | .r n | .d n => n
  | .i _ xs => xs.length + 1

def pathMeasure (path : Path) (pos : Nat) : Nat × Nat :=
  ⟨path.size - pos, Array.foldl (fun tot d => d.size + tot) 0 path⟩

def withCurNext (path : Path) (pos : Nat) (base : α) (step : Direction → Path → Nat → α) : α :=
  if path.size <= pos then base else
  match path[pos]! with
  | .l 0 | .r 0 | .d 0 => withCurNext path (pos + 1) base step
  | d@(.l n) => step d (path.set! pos (Direction.l (n - 1))) pos
  | d@(.r n) => step d (path.set! pos (Direction.r (n - 1))) pos
  | d@(.d n) => step d (path.set! pos (Direction.d (n - 1))) pos
  | d@(.i _ [])        => step d path (pos + 1)
  | d@(.i _ (y :: xs)) => step d (path.set! pos (Direction.i y xs)) pos
termination_by withCurNext path pos _ _ => pathMeasure path pos
decreasing_by
  rename_i hgt ; simp_wf ; apply Prod.Lex.left ;
  unfold pathMeasure ; apply Nat.sub_succ_lt_self ;
  simp_arith at hgt |- ; assumption

def checkDefEq (t1 t2 : Expr) : TacticM Unit := do
  if (← isDefEq t1 t2) then pure ()
  else throwError s!"match failure"

def filterEqns (pins qins pouts qouts : Array Expr) (k : Nat)
  : TacticM (Array Expr × Array Expr) := do
  if k >= pins.size then pure ⟨pouts, qouts⟩ else
  if (← isDefEq pins[k]! qins[k]!) then
    filterEqns pins qins pouts qouts (k + 1)
  else
    filterEqns pins qins (pouts.push pins[k]!) (qouts.push qins[k]!) (k + 1)
termination_by filterEqns pins _ _ _ k => pins.size - k
decreasing_by
  rename_i hgt ; simp_wf ; apply Nat.sub_succ_lt_self
  simp_arith at hgt |- ; assumption

/--
Given:
  - `lty` a term of the form `p s1 s2 ... sn`
  - `pargs` the array `#[s1, s2, ..., sn]`
  - `qargs` the array `#[t1, t2, ..., tn]`

Builds:
  - a proof term for: `s1 = t1 ∧ s2 = t2 ∧ ... ∧ sn = tn → p s1 s2 ... sn → p t1 t2 ... tn`
-/
def mkProofInit (lty : Term) (pargs qargs : Array Expr) (k : Nat := 0)
  : TacticM Term := do
  -- trace[Meta.debug] s!"mkProofInit: {lty} {pargs} {qargs} {k}"
  if k >= pargs.size then
    `(fun (_ : True) (x : $lty) => x)
  else
    let s ← Lean.PrettyPrinter.delab <| pargs[k]!
    let t ← Lean.PrettyPrinter.delab <| qargs[k]!
    if k + 1 == pargs.size then
      `(fun (q : $s = $t) (x : $lty) => q ▸ x)
    else
      let bod ← mkProofInit lty pargs qargs (k + 1)
      `(fun (q : ($s = $t) ∧ _) (x : $lty) => q.1 ▸ $bod q.2 x)
termination_by mkProofInit _ pargs _ k => pargs.size - k
decreasing_by
  rename_i hg1 _ ; simp_wf ; apply Nat.sub_succ_lt_self
  simp_arith at hg1 |- ; assumption

/--
Given:
  - `fargs` the array `#[s1, s2, ..., sn]`
  - `gargs` the array `#[t1, t2, ..., tn]`

Builds:
  - a proof term for: `s1 = t1 ∧ s2 = t2 ∧ ... ∧ sn = tn → f s1 s2 ... sn = f t1 t2 ... tn`
    (no matter what `f` is)
-/
def mkProofCongr (fargs gargs : Array Expr) (k : Nat := 0) : TacticM Term := do
  if k >= fargs.size then
    `(fun (_ : True) => Eq.refl _)
  else
    let s ← Lean.PrettyPrinter.delab <| fargs[k]!
    let t ← Lean.PrettyPrinter.delab <| gargs[k]!
    if k + 1 == fargs.size then
      `(fun (q : $s = $t) => q ▸ rfl)
    else
      let bod ← mkProofCongr fargs gargs (k + 1)
      `(fun (q : ($s = $t) ∧ _) => q.1 ▸ $bod q.2)
termination_by mkProofCongr pargs _ k => pargs.size - k
decreasing_by
  rename_i hg1 _ ; simp_wf ; apply Nat.sub_succ_lt_self
  simp_arith at hg1 |- ; assumption

/--
`mkInner rn goal`: use `rn` as the "inner proof" to be executed at the location
pointed to by the `within` invocation.

Note that `goal_init` (for the case of `a → a`) and `goal_congr` (for the case
of `s = t`), both in positive formula contexts, are special cased. They produce
a computed conjunction of equations for the arguments to the predicates and
functions, respectively.
-/
def mkInner (rn : Term) (goal : Expr) : TacticM Term := do
  match rn with
  | `(init) =>
    -- goal must be of the form `l → r`
    match (← whnf goal) with
    | .forallE _ l r _ =>
      if r.hasLooseBVars then throwError s!"goal not (convertible to) →"
      (← whnf l).withApp fun p pargs => do
        (← whnf r).withApp fun q qargs => do
          checkDefEq p q <|> throwError s!"predicates {p} and {q} do not match"
          if pargs.size != qargs.size then
            throwError s!"different #args: {pargs.size} vs. {qargs.size}"
          let lty ← Lean.PrettyPrinter.delab (← instantiateMVars l)
          let ⟨pargs, qargs⟩ ← filterEqns pargs qargs #[] #[] 0
          mkProofInit lty pargs qargs
    | _ => throwError s!"goal not (convertible to) →"
  | `(congr) =>
    -- goal must be of the form `l = r`
    (← whnf goal).withApp fun q args => do
      if not <| q.isConstOf ``Eq then throwError s!"goal not (convertible to) ="
      let l := args[1]!
      let r := args[2]!
      (← whnf l).withApp fun f fargs => do
        (← whnf r).withApp fun g gargs => do
          checkDefEq f g <|> throwError s!"functions {f} and {g} do not match"
          if fargs.size != gargs.size then
            throwError s!"different #args: {fargs.size} vs. {gargs.size}"
          let ⟨fargs, gargs⟩ ← filterEqns fargs gargs #[] #[] 0
          mkProofCongr fargs gargs
  | _ => pure rn

partial def mkWithinArg (path : Path) (pos : Nat) (rn : Term) (goal : Expr) : TacticM Term :=
  withCurNext path pos (mkInner rn goal) fun dir nextPath nextPos => do
    -- trace[Meta.debug] s!"mkWithinArg: trying to go {dir} in {goal}"
    let goal ← whnf goal
    match goal with
    | .app .. =>
        goal.withApp fun h args => do
          if h.isConstOf ``And then
            match dir with
            | .l _ =>
              let trm ← mkWithinArg nextPath nextPos rn args[0]! ; `(go_left_and $trm)
            | .r _ =>
              let trm ← mkWithinArg nextPath nextPos rn args[1]! ; `(go_right_and $trm)
            | _ => throwError s!"{dir} incompatible with ∧"
          else if h.isConstOf ``Or then
            match dir with
            | .l _ =>
              let trm ← mkWithinArg nextPath nextPos rn args[0]! ; `(go_left_or $trm)
            | .r _ =>
              let trm ← mkWithinArg nextPath nextPos rn args[1]! ; `(go_right_or $trm)
            | _ => throwError s!"{dir} incompatible with ∨"
          else if h.isConstOf ``Not then
            match dir with
            | .d _ | .r _ =>
              let trm ← mkWithinArg nextPath nextPos rn args[0]!
              `(go_down_not $trm)
            | _ => throwError s!"{dir} incompatible with ¬"
          else if h.isConstOf ``Exists then
            match args[1]? with
            | some (Expr.lam x ty bod bi) => do
              match dir with
              | .d _ => do
                let x ← mkIdentFromRef (← mkFreshUserName x)
                withLocalDecl x.getId bi ty fun v => do
                  let trm ← mkWithinArg nextPath nextPos rn (bod.instantiate #[v])
                  `(go_down_ex (fun $x => $trm))
              | .i x _ =>
                withLocalDecl x.getId bi ty fun v => do
                  let trm ← mkWithinArg nextPath nextPos rn (bod.instantiate #[v])
                  `(go_down_ex (fun $x => $trm))
              | _ => throwError s!"{dir} incompatible with ∃"
            | _ => throwError s!"{dir}: malformed ∃: {goal}"
          else throwError s!"within/app: {dir} incompatible with {h}"
    | .forallE x ty bod bi =>
      match dir with
      | .d _ => do
        let x ← mkIdentFromRef (← mkFreshUserName x)
        withLocalDecl x.getId bi ty fun v => do
          let trm ← mkWithinArg nextPath nextPos rn (bod.instantiate #[v])
          `(go_down_all (fun $x => $trm))
      | .i x _ =>
        withLocalDecl x.getId bi ty fun v => do
          let trm ← mkWithinArg nextPath nextPos rn (bod.instantiate #[v])
          `(go_down_all (fun $x => $trm))
      | .l _ =>
        let trm ← mkWithinArg nextPath nextPos rn ty ; `(go_left_imp $trm)
      | .r _ =>
        let trm ← mkWithinArg nextPath nextPos rn bod ; `(go_right_imp $trm)
    | _ => throwError s!"within/main: {dir} incompatible with {goal}"

elab "within " path:term,* " use " rn:term : tactic => do
  let path ← parsePath path
  let goal := (← Lean.MVarId.getType (← getMainGoal))
  let arg ← mkWithinArg path 0 rn goal
  evalTactic (← `(tactic| refine' $arg _))

end Profint_paths

end Profint
