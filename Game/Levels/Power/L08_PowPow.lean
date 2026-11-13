import Game.Levels.Power.L07_MulPow

World "Power"
Level 8

Title "`pow_pow`"

VisualLevelNumber "8"

namespace MyNat

Introduction
"
One of the best named levels in the game, a savage `pow_pow`
sub-boss appears as the music reaches a frenzy. What
else could there be to prove about powers after this?
"

/-- `pow_pow a m n` is a proof that $(a^m)^n=a^{mn}.$ -/
TheoremDoc MyNat.pow_pow as "pow_pow" in "^"

Statement pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with t ht
  · rw [mul_zero, pow_zero, pow_zero]
  · rw [pow_succ, ht, mul_succ, pow_add]

Conclusion
"
The music dies down. Is that it?

Course it isn't, you can
clearly see that there are two levels left.

A passing mathematician says that mathematicians don't have a name
for the structure you just constructed. You feel cheated.

Suddenly the music starts up again. This really is the final boss.
"
