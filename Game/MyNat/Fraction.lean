/-!
# Fractions

A small type for the Rewrite World levels about fractions, written `ℚ`. Addition and
multiplication are opaque, and those levels only use what their hypotheses say.

Visual Lean displays a variable named `frac1over2` as a vertical fraction, and a name
ending in `_inv`, like `a_inv`, as `a⁻¹`.
-/

/-- A fraction, with notation `ℚ`. -/
structure MyRat where
  num : Nat
  den : Nat
  deriving Inhabited

@[inherit_doc]
notation (name := MyRatNotation) (priority := 1000000) "ℚ" => MyRat

namespace MyRat

/-- Addition of fractions. Opaque, so Lean never computes with it. -/
opaque add : MyRat → MyRat → MyRat

/-- Multiplication of fractions. Opaque, so Lean never computes with it. -/
opaque mul : MyRat → MyRat → MyRat

instance : Add MyRat where
  add := MyRat.add

instance : Mul MyRat where
  mul := MyRat.mul

instance {n : Nat} : OfNat MyRat n where
  ofNat := ⟨n, 1⟩

end MyRat
