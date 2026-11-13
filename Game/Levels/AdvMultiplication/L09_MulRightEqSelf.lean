import Game.Levels.AdvMultiplication.L08_MulEqZero

World "AdvMultiplication"
Level 9

Title "`mul_right_eq_self`"

VisualLevelNumber "9"

namespace MyNat

Introduction
"
The lemma proved in this level will be helpful in Divisibility World, one day.
Splitting `b` into its two forms does most of the work.
"

/-- `mul_right_eq_self a b` is a proof that if `a ≠ 0` and `a * b = a` then `b = 1`. -/
TheoremDoc MyNat.mul_right_eq_self as "mul_right_eq_self" in "*"

Statement mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  cases b with d
  · exact (ha (by rw [mul_zero] at h; exact h.symm)).elim
  · exact (mul_eq_zero a d (add_left_eq_self (a * d) a (by rw [mul_succ] at h; exact h))).elim
      (fun h0 => (ha h0).elim)
      (fun hd => by rw [hd, one_eq_succ_zero])

Conclusion
"
We now have all the tools necessary to set up the basic theory of divisibility of naturals.

One boss to go.
"
