import Game.Levels.Multiplication.L07_MulAdd

World "Multiplication"
Level 8

Title "`add_mul`"

VisualLevelNumber "8"

namespace MyNat

Introduction
"
`add_mul` is just as fiddly to prove by induction; but there's a trick
which avoids it. Can you spot it?
"

/--
`add_mul a b c` is a proof that $(a+b)c=ac+bc$.
-/
TheoremDoc MyNat.add_mul as "add_mul" in "*"

Statement add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]
