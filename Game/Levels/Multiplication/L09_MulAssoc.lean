import Game.Levels.Multiplication.L08_AddMul

World "Multiplication"
Level 9

Title "`mul_assoc` (Multiplication World Boss)"

VisualLevelNumber "9"
VisualBossLevel

namespace MyNat

Introduction
"
We now have enough to prove that multiplication is associative,
the boss level of multiplication world. Good luck!
"

/--
`mul_assoc a b c` is a proof that `(a * b) * c = a * (b * c)`.

Note that when Lean says `a * b * c` it means `(a * b) * c`.

Note that `(a * b) * c = a * (b * c)` cannot be proved by \"pure thought\":
for example subtraction is not associative, as `(6 - 2) - 1` is not
equal to `6 - (2 - 1)`.
-/
TheoremDoc MyNat.mul_assoc as "mul_assoc" in "*"

Statement mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction c with d hd
  · rw [mul_zero, mul_zero, mul_zero]
  · rw [mul_succ, mul_succ, hd, mul_add]

Conclusion
"
A passing mathematician notes that you've proved
that the natural numbers are a commutative semiring.

If you want to begin your journey to the final boss, head for Power World.
"
