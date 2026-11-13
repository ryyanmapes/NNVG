import Game.Levels.Induction.L01_ZeroAdd

World "Induction"
Level 2

Title "`succ_add`"

VisualLevelNumber "2"

namespace MyNat

Introduction
"
Oh no! On the way to `add_comm`, a wild `succ_add` appears. `succ_add a b`
is the proof that `(S a) + b = S (a + b)` for `a` and `b` numbers.
This result is what's standing in the way of `x + y = y + x`. Again
we have the problem that we are adding `b` to things, so we need
to use induction to split into the cases where `b = 0` and `b` is a successor.
"

/-- `succ_add a b` is a proof that `S a + b = S (a + b)`. -/
TheoremDoc MyNat.succ_add as "succ_add" in "+"

Statement succ_add : ∀ a b : ℕ, S a + b = S (a + b) := by
  exact fun a b => by
    induction b with d hd
    · rw [add_zero, add_zero]
    · rw [add_succ, add_succ, hd]

Conclusion
"
Well done! You now have enough tools to prove that addition is commutative.
"
