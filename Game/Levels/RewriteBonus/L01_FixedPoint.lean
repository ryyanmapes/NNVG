import Game.Metadata

World "RewriteBonus"
Level 1

Title "Fixed Point"

VisualLevelNumber "A"
VisualRewriteOnly

Statement (f : ℕ → ℕ) (x a b c : ℕ) (fixed_point : f x = x) (hx : x = a)
    (fa : f a = b) (fb : f b = c) (fc : f c = 0) : f x = 0 := by
  rw [← fixed_point, ← fixed_point, hx, fa, fb, fc]
