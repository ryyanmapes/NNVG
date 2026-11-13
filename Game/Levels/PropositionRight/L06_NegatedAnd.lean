import Game.Metadata

World "PropositionRight"
Level 6

Title "Negation (2)"

VisualLevelNumber "12"

Statement (A : Prop) : ¬(A ∧ ¬A) := by
  exact fun h => h.2 h.1
