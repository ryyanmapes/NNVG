import Game.Levels.Successor.L01_Successor

World "Successor"
Level 2

Title "`add_succ`"

VisualLevelNumber "2"
VisualRewriteOnly

namespace MyNat

/-- `add_zero n` is a proof of `n + 0 = n`. -/
TheoremDoc MyNat.add_zero as "add_zero" in "+"

/-- `add_succ a b` is a proof of `a + S b = S (a + b)`. -/
TheoremDoc MyNat.add_succ as "add_succ" in "+"

NewTheorem MyNat.add_zero MyNat.add_succ

/-- `add_one_eq_succ a` is a proof of `a + 1 = S a`. -/
TheoremDoc MyNat.add_one_eq_succ as "add_one_eq_succ" in "+"

Statement add_one_eq_succ (a : ℕ) : a + 1 = S a := by
  rw [one_eq_succ_zero, add_succ, add_zero]

VisualTransformText "In this world, we'll prove all the basic properties of addition from only the axioms below (and induction)!"
