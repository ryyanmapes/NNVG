import Game.Metadata

World "Rewrite"
Level 5

Title "Click to Rewrite"

VisualLevelNumber "4"
VisualRewriteOnly

Statement (a b c d : ℕ) (add_comm : ∀ a b : ℕ, a + b = b + a)
    (add_assoc : ∀ a b c : ℕ, (a + b) + c = a + (b + c))
    (hc : a + b = c) (hd : c + c = d) : ((b + b) + a) + a = d := by
  rw [add_assoc b b a, add_comm b a, hc, add_comm (b + c) a, ← add_assoc a b c, hc, hd]

VisualTransformText "Instead of dragging hypotheses, you can also {pc: click | mobile: tap} them to make the first substitution possible (reading left to right)."
