import Game.Levels.Power.L03_PowOne

World "Power"
Level 4

Title "`one_pow`"

VisualLevelNumber "4"

namespace MyNat

/-- `one_pow n` is a proof that $1^n=1$. -/
TheoremDoc MyNat.one_pow as "one_pow" in "^"

Statement one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with t ht
  · rw [pow_zero]
  · rw [pow_succ, ht, mul_one]
