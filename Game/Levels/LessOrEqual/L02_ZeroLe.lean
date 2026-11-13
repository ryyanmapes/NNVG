import Game.Levels.LessOrEqual.L01_LeRefl

World "LessOrEqual"
Level 2

Title "Positivity"

VisualLevelNumber "2"

namespace MyNat

Introduction
"
To solve this level, you need to build a number `c` such that `x = 0 + c`.
"

/-- `zero_le x` is a proof that `0 ≤ x`. -/
TheoremDoc MyNat.zero_le as "zero_le" in "≤"

Statement zero_le (x : ℕ) : 0 ≤ x := by
  exact (⟨x, by rw [zero_add]⟩ : ∃ c, x = 0 + c)
