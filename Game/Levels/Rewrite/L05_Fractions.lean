import Game.Metadata

World "Rewrite"
Level 5

Title "General Rewriting (Associativity)"

VisualLevelNumber "4"
VisualRewriteOnly

-- `frac1over2` displays as a vertical fraction.
Statement (frac1over2 frac1over4 : ℚ)
    (h_fourths : frac1over2 = frac1over4 + frac1over4)
    (h_halves : (1 : ℚ) = frac1over2 + frac1over2)
    (add_assoc : ∀ x y z : ℚ, (x + y) + z = x + (y + z)) :
    (frac1over2 + frac1over4) + frac1over4 = 1 := by
  rw [add_assoc, ← h_fourths, ← h_halves]
