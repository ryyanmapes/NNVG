import Game.Levels.Power.L06_PowAdd

World "Power"
Level 7

Title "`mul_pow`"

VisualLevelNumber "7"

namespace MyNat

Introduction
"
The music gets ever more dramatic, as we explore
the interplay between exponentiation and multiplication.

If you're having trouble exchanging the right `a * b`
because `rw [mul_comm]` swaps the wrong multiplication,
then read the documentation of `rw` for tips on how to fix this.
"

/-- `mul_pow a b n` is a proof that $(ab)^n=a^nb^n.$ -/
TheoremDoc MyNat.mul_pow as "mul_pow" in "^"

Statement mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with t ht
  · rw [pow_zero, pow_zero, pow_zero, mul_one]
  · rw [pow_succ, pow_succ, pow_succ, ht, mul_assoc, mul_assoc, mul_comm (b ^ t) (a * b),
      mul_assoc, mul_comm b (b ^ t)]
