import Game.Levels.Multiplication.L04_MulComm

World "Multiplication"
Level 5

Title "`one_mul`"

VisualLevelNumber "5"

namespace MyNat

Introduction
"
You can prove $1\\times m=m$ in at least three ways.
Either by induction, or by using `succ_mul`, or
by using commutativity. Which do you think is quickest?
"

/--  `one_mul m` is the proof `1 * m = m`. -/
TheoremDoc MyNat.one_mul as "one_mul" in "*"

Statement one_mul (m : ℕ) : 1 * m = m := by
  rw [mul_comm, mul_one]
