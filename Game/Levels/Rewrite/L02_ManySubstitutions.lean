import Game.Metadata

World "Rewrite"
Level 2

Title "Many Substitutions"

VisualLevelNumber "1"
VisualRewriteOnly
VisualHideRewriteDirection

Statement (a b c : ℕ) (zero_add_zero : (0 : ℕ) + 0 = 0)
    (hypothesis_a : a = 0) (hypothesis_b : b = 0) (hypothesis_c : c = 0) :
    0 = (a + b) + c := by
  rw [hypothesis_a, hypothesis_b, hypothesis_c, zero_add_zero, zero_add_zero]

VisualTransformText "You may need to make many substitutions to complete a proof!
Instead of dragging hypotheses, you can also {pc: click | mobile: tap} them to make the first substitution possible (reading left to right)."
