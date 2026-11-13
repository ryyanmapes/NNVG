import Game.Metadata

World "PropositionRight"
Level 4

Title "The Principle of Explosion"

VisualLevelNumber "10"

Statement (h : False) : (1 : ℕ) = 2 := by
  exact h.elim

VisualGoalInfo above false
  "A ‘False’ hypothesis can prove *anything*!"
