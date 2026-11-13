import Game.Levels.AdvMultiplication.L07_MulNeZero

World "AdvMultiplication"
Level 8

Title "`mul_eq_zero`"

VisualLevelNumber "8"

namespace MyNat

Introduction
"
This level proves that if `a * b = 0` then `a = 0` or `b = 0`. It is
logically equivalent to the last level, so there is a very short proof.
"

/-- `mul_eq_zero a b` is a proof that if `a * b = 0` then `a = 0` or `b = 0`. -/
TheoremDoc MyNat.mul_eq_zero as "mul_eq_zero" in "*"

Statement mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  cases b with e
  · exact .inr (reflection 0)
  · exact .inl (add_left_eq_zero (a * e) a (by rw [mul_succ] at h; exact h))

Conclusion
"
Splitting on `b` does all the work. If `b` is a successor then `a * b` is
`a * e + a`, so `a * b = 0` forces `a = 0` and the left hand side is the true one.
"
