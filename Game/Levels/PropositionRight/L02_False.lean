import Game.Metadata

World "PropositionRight"
Level 2

Title "False"

VisualLevelNumber "7"

Statement (h : False) : (1 : ℕ) = 2 := by
  exact h.elim

VisualGoalInfo above false
  "A ‘False’ hypothesis can prove *anything*!"
