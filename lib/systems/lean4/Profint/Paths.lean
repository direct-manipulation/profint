-- Export lean4 proofs from the profint web tool

-- Parsing paths

import Lean

namespace Profint

open Lean Parser.Tactic Elab Elab.Tactic Meta

inductive Direction : Type where
  | l | r | d | i (x : Ident)
deriving Inhabited

def Direction.toString (dir : Direction) :=
  match dir with
  | .l => "(l)"
  | .r => "(r)"
  | .d => "(d)"
  | .i x => s!"(i {x})"

instance : ToString Direction := ⟨Direction.toString⟩

abbrev Path := Array Direction

private def pushN.{u} {α : Type u} (arr : Array α) (x : α) (n : Nat)
  : Array α :=
  if n = 0 then arr else pushN (arr.push x) x (n - 1)

def parseDirection (stx : Term) (arr : Path) : CoreM Path :=
  match stx with
  | `(l $n:num) => pure <| pushN arr Direction.l n.getNat
  | `(r $n:num) => pure <| pushN arr Direction.r n.getNat
  | `(d $n:num) => pure <| pushN arr Direction.d n.getNat
  | `(l)        => pure <| arr.push Direction.l
  | `(r)        => pure <| arr.push Direction.r
  | `(d)        => pure <| arr.push Direction.d
  | `(i $x:ident $xs:ident*) => do
      let mut arr := arr.push (Direction.i x)
      for x in xs.toList do
        arr := arr.push (Direction.i x)
      return arr
  | _ => throwErrorAt stx s!"not a valid direction"

def parsePath (stxs : Array Term) : TacticM Path := do
  let mut path := #[]
  for stx in stxs do path ← parseDirection stx path
  return path

end Profint

-- Local Variables:
-- mode: lean4
-- End:
