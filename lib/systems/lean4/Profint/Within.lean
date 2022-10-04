-- Implementation of the `within ... use ...` tactic

import Init.Data.ToString
import Lean

import Profint.Theorems
import Profint.Paths

open Lean Elab Meta Tactic

namespace Profint

def checkDefEq (t1 t2 : Expr) : TacticM Unit := do
  if (← isDefEq t1 t2) then pure ()
  else throwError s!"match failure"

def filterSame (qs : Array (Expr × Expr)) : TacticM (Array (Expr × Expr)) := do
  let mut result := #[]
  for (s, t) in qs do
    if !(← isDefEq s t) then
      result := result.push (s, t)
  return result

def mkBigEq (qs : Array (Expr × Expr)) : TacticM Expr := do
  let qs ← filterSame qs
  if qs.isEmpty then return (mkConst ``True) else
  let (s, t) := qs.back
  let mut result ← mkEq s t
  for (s, t) in qs.reverse[1:] do
    result := mkAnd (← mkEq s t) result
  return result

/--
Given:
  - `lty` a term of the form `p s1 s2 ... sn`
  - `pargs` the array `#[s1, s2, ..., sn]`
  - `qargs` the array `#[t1, t2, ..., tn]`

Builds:
  - a proof term for: `s1 = t1 ∧ s2 = t2 ∧ ... ∧ sn = tn → p s1 s2 ... sn → p t1 t2 ... tn`
-/
def mkProofInit (hd : Expr) (pargs qargs : Array Expr) : TacticM Term := do
  let qs := Array.zip pargs qargs
  let premise ← mkBigEq qs
  let qTy ← Lean.PrettyPrinter.delab premise
  let lTy ← Lean.PrettyPrinter.delab (mkAppN hd pargs)
  if qs.size = 0 then `(fun (_ : $(mkIdent ``True)) (x : $lTy) => x) else
  let mut x ← mkIdentFromRef (← mkFreshUserName `x)
  let q ← mkIdentFromRef (← mkFreshUserName `q)
  let mut result ← `($x:term)
  let mut curQ ← `($q:term)
  let mut qargs := qargs
  for i in List.range pargs.size do
    if !(← isDefEq pargs[i]! qargs[i]!) then
      let u ← mkIdentFromRef (← mkFreshUserName `u)
      qargs := qargs.set! i (mkBVar 0)
      let fn ← Lean.PrettyPrinter.delab <|
                 Expr.lam u.getId (← inferType pargs[i]!) (mkAppN hd qargs) BinderInfo.default
      qargs := qargs.set! i pargs[i]!
      let eqn ← if i + 1 < pargs.size then `($curQ.1) else `($curQ)
      let xNew ← mkIdent <$> Lean.Elab.Term.mkFreshBinderName
      result ← `(let $x := $(mkIdent ``Eq.subst) ($(mkIdent `motive) := $fn) $eqn $xNew ; $result)
      x := xNew
      curQ ← `($curQ.2)
  `(fun ($q : $qTy) ($x : $lTy) => $result)

/--
Given:
  - `fargs` the array `#[s1, s2, ..., sn]`
  - `gargs` the array `#[t1, t2, ..., tn]`

Builds:
  - a proof term for: `s1 = t1 ∧ s2 = t2 ∧ ... ∧ sn = tn → f s1 s2 ... sn = f t1 t2 ... tn`
    (no matter what `f` is)
-/
def mkProofCongr (hd : Expr) (fargs gargs : Array Expr) : TacticM Term := do
  let qs := Array.zip fargs gargs
  let qTy ← Lean.PrettyPrinter.delab (← mkBigEq qs)
  let lhs := mkAppN hd fargs
  let lhsTm ← Lean.PrettyPrinter.delab lhs
  if qs.size = 0 then `(fun (_ : $(mkIdent ``True)) => $(mkIdent ``Eq.refl) $lhsTm) else
  let mut x ← mkIdentFromRef (← mkFreshUserName `x)
  let q ← mkIdentFromRef (← mkFreshUserName `q)
  let mut result ← `($x)
  let mut curQ ← `($q:term)
  let mut gargs := gargs
  for i in List.range fargs.size do
    if !(← isDefEq fargs[i]! gargs[i]!) then
      let u ← mkIdentFromRef (← mkFreshUserName `u)
      gargs := gargs.set! i (mkBVar 0)
      let lhs_here := mkAppN hd gargs
      let mot := Expr.lam u.getId (← inferType fargs[i]!) (← mkEq lhs lhs_here)
                   BinderInfo.default
      let eqn ← if i + 1 < fargs.size then `($curQ.1) else `($curQ)
      let mot ← Lean.PrettyPrinter.delab mot
      result ← `(let $x := $(mkIdent ``Eq.subst) ($(mkIdent `motive) := $mot) $eqn $u ; $result)
      x := u
      curQ ← `($curQ.2)
      gargs := gargs.set! i fargs[i]!
  `(fun ($q : $qTy) => let $x := $(mkIdent ``Eq.refl) $lhsTm ; $result)

/--
Given:
  - goal: s = t → a⟪s⟫   or   s = t → a⟪t⟫
  - symm: false          or   true

Produces
  - proof of
    a⟪t⟫ → s = t → a⟪s⟫  or   a⟪s⟫ → s = t → a⟪t⟫
-/
def doRewrite (goal : Expr) (symm : Bool) : MetaM Term := do
  -- goal must be of the form `(s = t) → f`
  match (← whnf goal).arrow? with
  | .none => throwError s!"Not an →"
  | .some (eqn, targetType) =>
    match (← whnf eqn).eq? with
    | .none => throwError s!"lhs not ="
    | .some (_, s, t) =>
      let targetType ← whnf targetType
      let eqType ← mkEq s t
      let hEq ← mkFreshExprSyntheticOpaqueMVar eqType (tag := `q)
      let gExpr ← mkFreshExprSyntheticOpaqueMVar targetType (tag := `g)
      let g := gExpr.mvarId!
      let r ← g.rewrite targetType hEq symm
      let gg ← g.replaceTargetEq r.eNew r.eqProof
      let sourceType ← gg.getType
      let xTy ← Lean.PrettyPrinter.delab sourceType
      let qTy ← Lean.PrettyPrinter.delab eqType
      let rTy ← Lean.PrettyPrinter.delab targetType
      let syn ← `((fun (x : $xTy) (q : $qTy) => ((q ▸ x) : $rTy)))
      trace[Meta.debug] s!"computed:\n{syn}"
      pure syn

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
    match (← whnf goal).arrow? with
    | .none => throwError "goal not →"
    | .some (l, r) =>
      (← whnf l).withApp fun p pargs => do
      (← whnf r).withApp fun q qargs => do
        checkDefEq p q <|> throwError s!"predicates {p} and {q} do not match"
        mkProofInit p pargs qargs
  | `(congr) =>
    match (← whnf goal).eq? with
    | .none => throwError "goal not ="
    | .some (_, l, r) =>
      (← whnf l).withApp fun f fargs => do
      (← whnf r).withApp fun g gargs => do
        checkDefEq f g <|> throwError s!"functions {f} and {g} do not match"
        mkProofCongr f fargs gargs
  | `(rewrite_rtl) => doRewrite goal True
  | `(rewrite_ltr) => doRewrite goal False
  | _ => pure rn

def mkWithinArg (path : Path) (pos : Nat) (rn : Term) (goal : Expr)
  : TacticM Term :=
  if pos >= path.size then mkInner rn goal else do
  let goal ← whnf goal
  let dir := path[pos]!
  match goal with
  | .app .. =>
      goal.withApp fun h args => do
        if h.isConstOf ``And then
          match dir with
          | .l =>
            let trm ← mkWithinArg path (pos + 1) rn args[0]! ;
            `($(mkIdent ``go_left_and) $trm)
          | .r =>
            let trm ← mkWithinArg path (pos + 1) rn args[1]! ;
            `($(mkIdent ``go_right_and) $trm)
          | _ => throwError s!"{dir} incompatible with ∧"
        else if h.isConstOf ``Or then
          match dir with
          | .l =>
            let trm ← mkWithinArg path (pos + 1) rn args[0]! ;
            ``($(mkIdent ``go_left_or) $trm)
          | .r =>
            let trm ← mkWithinArg path (pos + 1) rn args[1]! ;
            `($(mkIdent ``go_right_or) $trm)
          | _ => throwError s!"{dir} incompatible with ∨"
        else if h.isConstOf ``Exists then
          match args[1]? with
          | some (Expr.lam x ty bod bi) => do
            match dir with
            | .d => do
              let x ← mkIdentFromRef (← mkFreshUserName x)
              withLocalDecl x.getId bi ty fun v => do
                let trm ← mkWithinArg path (pos + 1) rn (bod.instantiate #[v])
                `($(mkIdent ``go_down_ex) (fun $x => $trm))
            | .i x =>
              withLocalDecl x.getId bi ty fun v => do
                let trm ← mkWithinArg path (pos + 1) rn (bod.instantiate #[v])
                `($(mkIdent ``go_down_ex) (fun $x => $trm))
            | _ => throwError s!"{dir} incompatible with ∃"
          | _ => throwError s!"{dir}: malformed ∃: {goal}"
        else throwError s!"within/app: {dir} incompatible with {h}"
  | .forallE x ty bod bi =>
    match dir with
    | .d => do
      let x ← mkIdentFromRef (← mkFreshUserName x)
      withLocalDecl x.getId bi ty fun v => do
        let trm ← mkWithinArg path (pos + 1) rn (bod.instantiate #[v])
        `($(mkIdent ``go_down_all) (fun $x => $trm))
    | .i x =>
      withLocalDecl x.getId bi ty fun v => do
        let trm ← mkWithinArg path (pos + 1) rn (bod.instantiate #[v])
        `($(mkIdent ``go_down_all) (fun $x => $trm))
    | .l =>
      let trm ← mkWithinArg path (pos + 1) rn ty ;
      `($(mkIdent ``go_left_imp) $trm)
    | .r =>
      let trm ← mkWithinArg path (pos + 1) rn bod ;
      `($(mkIdent ``go_right_imp) $trm)
  | _ => throwError s!"within/main: {dir} incompatible with {goal}"
termination_by mkWithinArg path pos _ _ => path.size - pos
decreasing_by
  rename_i hgt ; simp_wf ; apply Nat.sub_succ_lt_self ;
  simp_arith at hgt |- ; assumption

elab "within " path:term,* " use " rule:term : tactic => do
  let path ← parsePath path
  let goal ← Lean.MVarId.getType (← getMainGoal)
  let arg ← mkWithinArg path 0 rule goal
  trace[Meta.debug] "within/arg:\n{arg}"
  evalTactic (← `(tactic| refine' $arg _))

end Profint

-- Local Variables:
-- mode: lean4
-- End:
