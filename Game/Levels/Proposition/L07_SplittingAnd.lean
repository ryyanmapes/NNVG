import Game.Metadata

World "Proposition"
Level 7

Title "Conjunction (2)"

VisualLevelNumber "6"

Statement (A B C : Prop) : (A ∧ B) → ((B → (A → C)) → (A ∧ (B ∧ C))) := by
  exact fun hAB hBAC => ⟨hAB.1, hAB.2, hBAC hAB.2 hAB.1⟩

VisualGoalInfo above false
  "$∧$ hypotheses can be split by {pc: clicking | mobile: tapping} on them!"
