import Game.Metadata

World "Proposition"
Level 2

Title "Implication"

VisualLevelNumber "1"

Statement (A : Prop) : A → A := by
  exact fun h => h

VisualGoalInfoOnGoal above false "A → A" show
  "Goals with implications can be {pc: clicked | mobile: tapped} to introduce the left side as a hypothesis."
