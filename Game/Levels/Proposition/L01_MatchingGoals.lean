import Game.Metadata

World "Proposition"
Level 1

Title "Matching Goals"

VisualLevelNumber "0"

Statement (A : Prop) (h : A) : A := by
  exact h

NewTactic exact

VisualHypGoalInfo h "Goals can be proven by dragging over a proposition that matches it!"
