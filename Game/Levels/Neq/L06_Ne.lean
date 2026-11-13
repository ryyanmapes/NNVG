import Game.Levels.Neq.L05_SuccInj

World "Neq"
Level 6

Title "`≠`"

VisualLevelNumber "5"

namespace MyNat

Introduction
"
`a ≠ b` means `a = b → False`.
"

Statement (x y : ℕ) : (S x = S y ∧ x ≠ y) → False := by
  exact fun h => h.2 (succ_inj x y h.1)
