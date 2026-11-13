import Game.Levels.LessOrEqual
import Game.Levels.Multiplication

World "AdvMultiplication"
Level 1

Title "`mul_le_mul_right`"

VisualLevelNumber "1"

namespace MyNat

Introduction
"
Let's warm up with an easy one, which works even if `t = 0`.
"

/-- `mul_le_mul_right a b t` is a proof that `a ≤ b → a * t ≤ b * t`. -/
TheoremDoc MyNat.mul_le_mul_right as "mul_le_mul_right" in "*"

Statement mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  cases h with
  | intro d hd => exact (⟨d * t, by rw [hd, add_mul]⟩ : ∃ c, b * t = a * t + c)
