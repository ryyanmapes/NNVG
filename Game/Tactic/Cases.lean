import Game.MyNat.Definition

/-!
# Cases

Visual Lean plays a case split on a number as `cases n with d`, as in NNG4. This gives
that syntax to Lean's own `cases`, and has the zero case show `0` instead of
`MyNat.zero`. On a proof of `False`, `cases h` is Lean's own.
-/

namespace MyNat

/-- Case analysis on `MyNat`, with a zero case that shows `0`. -/
@[cases_eliminator]
theorem casesOn' {P : ℕ → Prop} (t : ℕ) (zero : P 0) (S : (n : ℕ) → P (MyNat.S n)) : P t := by
  cases t using MyNat.casesOn with
  | zero => exact zero
  | S n => exact S n

end MyNat

/-- `cases n with d` splits the goal into the case `n = 0` and the case `n = S d`. -/
macro (name := MyNat.casesWith) "cases " target:ident " with " d:ident : tactic =>
  `(tactic| cases $target:ident with
    | zero => ?_
    | S $d:ident => ?_)
