import Game.Metadata

World "Rewrite"
Level 4

Title "General Rules"

VisualLevelNumber "3"
VisualRewriteOnly
VisualEmphasizeForall add_comm

Statement (a b c : ℕ) (add_comm : ∀ x y : ℕ, x + y = y + x)
    (hx : a = 1) (hy : b = 2) (hz : c = 3) : (a + b) + c = 3 + (2 + 1) := by
  rw [hx, hy, hz, add_comm (1 + 2) 3, add_comm 1 2]

VisualTransformText "Some hypotheses are more general than others.
Here, `add_comm` can swap any pair of numbers, not just the particular `a` and `b` in this problem!"
