import Game.Metadata

World "Rewrite"
Level 2

Title "Lots of Rewriting"

VisualLevelNumber "1"
VisualRewriteOnly
VisualHideRewriteDirection

Statement (x y z : ℕ) (hypothesis_x : x = 0) (hypothesis_y : y = 0) (hypothesis_z : z = 0)
    (zero_add_zero : (0 : ℕ) + 0 = 0) :
    (x + y) + z = 0 := by
  rw [hypothesis_x, hypothesis_y, hypothesis_z, zero_add_zero, zero_add_zero]

VisualTransformText "You may need to make many substitutions to complete a proof!
Instead of dragging hypotheses, you can also {pc: click | mobile: tap} them to make the first substitution possible (reading left to right)."
