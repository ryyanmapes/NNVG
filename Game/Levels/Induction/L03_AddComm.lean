import Game.Levels.Induction.L02_SuccAdd

World "Induction"
Level 3

Title "Commutativity of Addition"

VisualLevelNumber "3"

namespace MyNat

Introduction
"
Look in your inventory to see the proofs you have available.
These should be enough.
"

/-- `add_comm x y` is a proof of `x + y = y + x`. -/
TheoremDoc MyNat.add_comm as "add_comm" in "+"

Statement add_comm : ∀ a b : ℕ, a + b = b + a := by
  exact fun a b => by
    induction b with d hd
    · rw [add_zero, zero_add]
    · rw [add_succ, succ_add, hd]
