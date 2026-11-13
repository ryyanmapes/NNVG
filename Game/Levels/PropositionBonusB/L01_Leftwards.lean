import Game.Metadata

World "PropositionBonusB"
Level 1

Title "The Other De Morgan's Law (Leftwards)"

VisualLevelNumber "B1"

Statement (A B : Prop) : (¬A ∨ ¬B) → ¬(A ∧ B) := by
  exact fun h hAB => h.elim (fun hNotA => hNotA hAB.1) (fun hNotB => hNotB hAB.2)

VisualGoalInfo above false
  "This direction of De Morgan's other law is intuitionistically valid!"
