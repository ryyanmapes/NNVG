import Game.Levels.Induction

World "Multiplication"
Level 1

Title "`mul_one`"

VisualLevelNumber "1"

namespace MyNat

Introduction
"
See the two new axioms in your inventory, `mul_zero` and `mul_succ`.
Right now these are the only facts we know about multiplication.
Let's prove nine more.

Let's start with a warm-up: no induction needed for this one,
because we know `1` is a successor.
"

/--
`Mul a b`, with notation `a * b`, is the usual product of natural numbers. Internally it
is defined via two axioms:

* `mul_zero m : m * 0 = 0`

* `mul_succ a b : a * S b = a * b + a`

Other theorems about naturals, such as `zero_mul`, are proved by induction from these
two basic theorems.
-/
DefinitionDoc Mul as "*"

NewDefinition Mul

/-- `mul_zero m` is the proof that `m * 0 = 0`. -/
TheoremDoc MyNat.mul_zero as "mul_zero" in "*"

/-- `mul_succ a b` is the proof that `a * S b = a * b + a`. -/
TheoremDoc MyNat.mul_succ as "mul_succ" in "*"

/-- `mul_one m` is the proof that `m * 1 = m`. -/
TheoremDoc MyNat.mul_one as "mul_one" in "*"

NewTheorem MyNat.mul_zero MyNat.mul_succ
VisualEmphasize MyNat.mul_zero
VisualEmphasize MyNat.mul_succ

Statement mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]
