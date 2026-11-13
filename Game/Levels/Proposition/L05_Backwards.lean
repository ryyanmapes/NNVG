import Game.Metadata

World "Proposition"
Level 5

Title "Backwards Implications"

VisualLevelNumber "4"

Statement (A B C : Prop) : B → ((A → B) → C) → C := by
  exact fun hB hABC => hABC (fun _ => hB)

VisualGoalInfo above false
  "You can also prove the goal backwards!
Try dragging $(A → B) → C$ onto $C$ to turn the goal into $A → B$."
