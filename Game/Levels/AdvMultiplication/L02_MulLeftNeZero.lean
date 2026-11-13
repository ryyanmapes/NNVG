import Game.Levels.AdvMultiplication.L01_MulLeMulRight

World "AdvMultiplication"
Level 2

Title "`mul_left_ne_zero`"

VisualLevelNumber "2"

VisualGoalInfo below false "A new fundamental theorem, `peano_cases`, has been added to the Axioms tab. You may need it throughout this world."

namespace MyNat

Introduction
"
Remember that `b ≠ 0` is `b = 0 → False`: {pc: click | mobile: tap} the goal to assume `b = 0`,
then `h` is a short way to `False`.
"

/-- `mul_left_ne_zero a b` is a proof that `a * b ≠ 0 → b ≠ 0`. -/
TheoremDoc MyNat.mul_left_ne_zero as "mul_left_ne_zero" in "*"

/-- `peano_cases a` is a proof that `a = 0 ∨ ∃ b, a = S b`: every number is
either zero or a successor. -/
TheoremDoc MyNat.peano_cases as "peano_cases" in "Peano"

NewTheorem MyNat.peano_cases

Statement mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  exact fun hb => h (by rw [hb, mul_zero])
