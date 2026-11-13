import Game.Levels.Multiplication.L06_TwoMul

World "Multiplication"
Level 7

Title "`mul_add`"

VisualLevelNumber "7"

namespace MyNat

Introduction
"
Our next goal is \"left and right distributivity\",
meaning $a(b+c)=ab+ac$ and $(b+c)a=ba+ca$. Rather than
these slightly pompous names, the name of the proofs
in Lean are descriptive. Let's start with
`mul_add a b c`, the proof of `a * (b + c) = a * b + a * c`.
Note that the left hand side contains a multiplication
and then an addition.
"

/--
Multiplication distributes
over addition on the left.

`mul_add a b c` is the proof that `a * (b + c) = a * b + a * c`.
-/
TheoremDoc MyNat.mul_add as "mul_add" in "*"

Statement mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with d hd
  · rw [add_zero, mul_zero, add_zero]
  · rw [add_succ, mul_succ, hd, mul_succ, add_assoc]

Conclusion
"
Inducting on `a` or `b` also works, but might take longer.
"
