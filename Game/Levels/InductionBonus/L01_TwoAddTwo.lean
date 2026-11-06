import Game.Levels.Induction

World "InductionBonus"
Level 1

Title "`2 + 2 = 4`"

VisualLevelNumber "A1"
VisualRewriteOnly

namespace MyNat

Statement : (2 : ℕ) + 2 = 4 := by
  rw [four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, add_succ, one_eq_succ_zero,
    add_succ, add_zero]
