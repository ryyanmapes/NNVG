import Game.Levels.AdvMultiplication.L06_MulRightEqOne

World "AdvMultiplication"
Level 7

Title "`mul_ne_zero`"

VisualLevelNumber "7"

namespace MyNat

Introduction
"
This level proves that if `a ≠ 0` and `b ≠ 0` then `a * b ≠ 0`. One strategy
is to write both `a` and `b` as `S` of something, deduce that `a * b` is
also `S` of something, and then use `zero_ne_succ`.
"

/-- `mul_ne_zero a b` is a proof that if `a ≠ 0` and `b ≠ 0` then `a * b ≠ 0`. -/
TheoremDoc MyNat.mul_ne_zero as "mul_ne_zero" in "*"

Statement mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  cases eq_succ_of_ne_zero a ha with
  | intro c hc =>
    cases eq_succ_of_ne_zero b hb with
    | intro d hd => exact fun h => zero_ne_succ _ (by rw [hc, hd, mul_succ, add_succ] at h; exact h.symm)
