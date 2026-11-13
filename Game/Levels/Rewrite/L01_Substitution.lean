import Game.Metadata

World "Rewrite"
Level 1

Title "Basic Rewriting"

VisualLevelNumber "0"
VisualRewriteOnly
VisualHideRewriteDirection

Statement (x y : ℕ) (hypothesis_1 : x = 1) (hypothesis_2 : y = 2) : x + y = 1 + 2 := by
  rw [hypothesis_1, hypothesis_2]

NewTactic rw

VisualTransformRewriteInfoOnGoal hypothesis_1 "x" "x + y = 1 + 2" show
  "To show that an equality is true in Lean, we must show both sides are the same!
Drag a hypothesis onto a term to make a substitution."

VisualTransformCheckInfoOnGoal "1 + 2 = 1 + 2" show
  "Both sides are now the same, so the expression is true by the definition of equality!
So {pc: click | mobile: tap} the check mark to complete the proof."
