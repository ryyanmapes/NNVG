import Game.MyNat.Definition

/-!
# Multiplication

Multiplication of the game's natural numbers, as in NNG4: opaque, with the two axioms
`mul_zero` and `mul_succ` as its only definition.
-/

namespace MyNat

/-- Multiplication of natural numbers. Opaque, so Lean never computes `2 * 3` to `6`. -/
opaque mul : MyNat → MyNat → MyNat

instance instMul : Mul MyNat where
  mul := MyNat.mul

/-- `mul_zero m` is a proof of `m * 0 = 0`. -/
axiom mul_zero (m : MyNat) : m * 0 = 0

/-- `mul_succ a b` is a proof of `a * S b = a * b + a`. -/
axiom mul_succ (a b : MyNat) : a * S b = a * b + a

end MyNat
