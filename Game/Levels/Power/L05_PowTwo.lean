import Game.Levels.Power.L04_OnePow

World "Power"
Level 5

Title "`pow_two`"

VisualLevelNumber "5"

namespace MyNat

Introduction
"
Note: this lemma will be useful for the final boss!
"

/-- `pow_two a` says that `a ^ 2 = a * a`. -/
TheoremDoc MyNat.pow_two as "pow_two" in "^"

Statement pow_two (a : ℕ) : a ^ 2 = a * a := by
  rw [two_eq_succ_one, pow_succ, pow_one]
