import Game.MyNat.Multiplication

/-!
# Powers

Exponentiation of the game's natural numbers, as in NNG4: opaque, with the two axioms
`pow_zero` and `pow_succ` as its only definition. Note that `0 ^ 0 = 1`.
-/

namespace MyNat

/-- Exponentiation of natural numbers. Opaque, so Lean never computes `2 ^ 3` to `8`. -/
opaque pow : MyNat → MyNat → MyNat

instance instPow : Pow MyNat MyNat where
  pow := pow

-- `a ^ b` with numerals, such as `2 ^ 3`, elaborates with both sides in `MyNat`.
macro_rules | `($x ^ $y) => `(HPow.hPow ($x : MyNat) ($y : MyNat))

/-- `pow_zero m` is a proof of `m ^ 0 = 1`. -/
axiom pow_zero (m : MyNat) : m ^ 0 = 1

/-- `pow_succ m n` is a proof of `m ^ S n = m ^ n * m`. -/
axiom pow_succ (m n : MyNat) : m ^ S n = m ^ n * m

end MyNat
