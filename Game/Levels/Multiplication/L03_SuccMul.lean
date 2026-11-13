import Game.Levels.Multiplication.L02_ZeroMul

World "Multiplication"
Level 3

Title "`succ_mul`"

VisualLevelNumber "3"

namespace MyNat

Introduction
"
Similarly we have `mul_succ`
but we're going to need `succ_mul` (guess what it says -- maybe you
are getting the hang of Lean's naming conventions).

The last level from addition world might help you in this level.
If you can't remember what it is, you can go back to the
home screen by clicking the house icon and then taking a look.
You won't lose any progress.
"

/--
`succ_mul a b` is the proof that `S a * b = a * b + b`.

It could be deduced from `mul_succ` and `mul_comm`, however this argument
would be circular because the proof of `mul_comm` uses `mul_succ`.
-/
TheoremDoc MyNat.succ_mul as "succ_mul" in "*"

Statement succ_mul (a b : ℕ) : S a * b = a * b + b := by
  induction b with d hd
  · rw [mul_zero, mul_zero, add_zero]
  · rw [mul_succ, mul_succ, hd, add_succ, add_succ, add_assoc, add_assoc, add_comm d a]
