import Game.Metadata

World "Rewrite"
Level 3

Title "Backwards"

VisualLevelNumber "2"
VisualRewriteOnly

Statement (x y : ℕ) (zero_add_zero : (0 : ℕ) + 0 = 0)
    (hypothesis_x : 0 = x) (hypothesis_y : 0 = y) : x + y = 0 := by
  rw [← hypothesis_x, ← hypothesis_y, zero_add_zero]

VisualTransformReverseInfoOnGoal "x + y = 0" show
  "We can make substitutions both forwards and backwards!
Try {pc: clicking | mobile: tapping} here to swap substitution direction."
