import Game.Levels.Multiplication.L03_SuccMul

World "Multiplication"
Level 4

Title "`mul_comm`"

VisualLevelNumber "4"

namespace MyNat

Introduction
"
The first sub-boss of Multiplication World is `mul_comm x y : x * y = y * x`.

When you've proved this theorem we will have \"spare\" proofs
such as `zero_mul`, which is now easily deducible from `mul_zero`.
But we'll keep hold of these proofs anyway, because it's convenient
to have exactly the right tool for a job.
"

/--
`mul_comm` is the proof that multiplication is commutative. More precisely,
`mul_comm a b` is the proof that `a * b = b * a`.
-/
TheoremDoc MyNat.mul_comm as "mul_comm" in "*"

Statement mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with d hd
  · rw [zero_mul, mul_zero]
  · rw [succ_mul, ← hd, mul_succ]
