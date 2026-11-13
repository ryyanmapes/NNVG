import Game.Levels.Successor.L02_AddOne

World "Successor"
Level 3

Title "Counting to Four"

VisualLevelNumber "3"
VisualRewriteOnly
VisualBossLevel
VisualEmphasize MyNat.add_one_eq_succ

namespace MyNat

Statement : (1 : ℕ) + 1 + 1 + 1 = 4 := by
  rw [add_one_eq_succ, add_one_eq_succ, add_one_eq_succ, four_eq_succ_three, three_eq_succ_two,
    two_eq_succ_one]

VisualTransformText "You can use what you proved in ‘theorem’ levels to save time in future levels!"
