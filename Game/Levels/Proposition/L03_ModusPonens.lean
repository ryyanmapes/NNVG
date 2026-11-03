import Game.Metadata

World "Proposition"
Level 3

Title "Modus Ponens"

VisualLevelNumber "2"

Statement (A B : Prop) : A → ((A → B) → B) := by
  exact fun hA hAB => hAB hA

VisualGoalInfo above false
  "Drag $A$ onto $A → B$ in your workspace to get the proposition $B$!"
