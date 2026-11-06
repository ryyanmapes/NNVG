import Game.Metadata

World "RewriteBonus"
Level 2

Title "Inverses"

VisualLevelNumber "A2"
VisualRewriteOnly
VisualMulDot

-- A name ending in `_inv` displays with `⁻¹`.
Statement (x a a_inv : ℚ)
    (generate_a : x = x * a) (generate_a_inv : x = x * a_inv)
    (elim_a : (1 * a) * a_inv = (1 : ℚ)) (elim_a_inv : (1 * a_inv) * a = (1 : ℚ))
    (hx : x = 1) :
    x * a * a_inv * a * a * a_inv = 1 := by
  rw [← generate_a, ← generate_a_inv, ← generate_a, ← generate_a, ← generate_a_inv, hx]
