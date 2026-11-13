import Game.Levels.Power.L08_PowPow

World "Power"
Level 9

Title "`add_sq` (Power World Boss)"

VisualLevelNumber "9"
VisualBossLevel

namespace MyNat

Introduction
"
[final boss music]
"

/-- `add_sq a b` is the statement that $(a+b)^2=a^2+b^2+2ab.$ -/
TheoremDoc MyNat.add_sq as "add_sq" in "^"

Statement add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [pow_two, pow_two, pow_two, mul_add, add_mul, add_mul, two_mul, add_mul, mul_comm b a,
    add_assoc, add_assoc, ← add_assoc (a * b) (a * b) (b * b), add_comm (a * b + a * b) (b * b)]

Conclusion
"
It's all over! You have proved a theorem which has tripped up
schoolkids for generations (some of them think $(a+b)^2=a^2+b^2$:
this is \"the freshman's dream\").

How many rewrites did you use? I can do it in 12.

But wait! This boss is stirring...and mutating into a second more powerful form!
"
