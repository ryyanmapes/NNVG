import Game.Levels.AdvMultiplication.L03_EqSuccOfNeZero

World "AdvMultiplication"
Level 4

Title "`one_le_of_ne_zero`"

VisualLevelNumber "4"

namespace MyNat

Introduction
"
The previous lemma can be used to prove this one.
"

/-- `one_le_of_ne_zero a` is a proof that `a ≠ 0 → 1 ≤ a`. -/
TheoremDoc MyNat.one_le_of_ne_zero as "one_le_of_ne_zero" in "≤"

Statement one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  cases eq_succ_of_ne_zero a ha with
  | intro n hn => exact (⟨n, by rw [hn, ← add_one_eq_succ, add_comm]⟩ : ∃ c, a = 1 + c)
