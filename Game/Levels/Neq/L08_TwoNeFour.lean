import Game.Levels.Neq.L07_ZeroNeOne

World "Neq"
Level 8

Title "2 ≠ 4"

VisualLevelNumber "7"

namespace MyNat

-- Unlocked by completing `zero_ne_one` (the level before).
/-- `one_ne_zero` is a proof of `1 ≠ 0`. -/
TheoremDoc MyNat.one_ne_zero as "one_ne_zero" in "012"

NewTheorem MyNat.one_ne_zero

Statement : (2 : ℕ) ≠ 4 := by
  exact fun h => zero_ne_succ 1 (succ_inj 0 2 (succ_inj 1 3 h))
