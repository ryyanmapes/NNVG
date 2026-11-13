import Game.Metadata

World "PropositionRight"
Level 5

Title "Negation (1)"

VisualLevelNumber "11"

Statement (A : Prop) : A → ¬¬A := by
  exact fun hA hNotA => hNotA hA

VisualGoalInfo above false
  "$¬A$ just means $A → False$!"
