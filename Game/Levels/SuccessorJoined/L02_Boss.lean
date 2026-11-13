import Game.Levels.SuccessorJoined.L01_CrossingTheBeams

World "SuccessorJoined"
Level 2

Title "Plug and Chug (Successor World Boss)"

VisualLevelNumber "5"
VisualBossLevel

namespace MyNat

Statement (a b c : ℕ) (ha : a = 0 + 1) (hb : S (0 + 0) = b) (hc : c = (a + 0) + (0 + b)) :
    c + c = 4 := by
  rw [one_eq_succ_zero, add_succ, add_zero] at ha
  rw [add_zero] at hb
  rw [add_zero, ha, ← hb, add_succ, add_zero, add_succ, add_zero] at hc
  rw [hc, four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero, add_succ,
    add_succ, add_zero]
