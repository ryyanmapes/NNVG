import Game.Metadata

World "Proposition"
Level 4

Title "Implications (3)"

VisualLevelNumber "3"

Statement (A B C : Prop) : A → (A → B) → ((A → (B → C)) → C) := by
  exact fun hA hAB hABC => hABC hA (hAB hA)
