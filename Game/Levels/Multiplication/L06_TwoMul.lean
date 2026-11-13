import Game.Levels.Multiplication.L05_OneMul

World "Multiplication"
Level 6

Title "`two_mul`"

VisualLevelNumber "6"

namespace MyNat

Introduction
"
This level is more important than you think; it plays
a useful role when battling a big boss later on.
"

/--
`two_mul m` is the proof that `2 * m = m + m`.
-/
TheoremDoc MyNat.two_mul as "two_mul" in "*"

Statement two_mul (m : ℕ) : 2 * m = m + m := by
  rw [two_eq_succ_one, succ_mul, one_mul]
