import Game.Metadata

World "Proposition"
Level 6

Title "Conjunction (1)"

VisualLevelNumber "5"

Statement (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  exact ⟨hA, hB⟩

-- Before splitting only: after the split, the hint below the proof graph takes over.
VisualGoalInfoOnGoal above true "A ∧ B" while
  "The symbol $∧$ represents ‘and’. In order to prove an ‘and’ goal, we must prove both sides.
{pc: Click | mobile: Tap} the goal here to split into two proof branches."

VisualProofGraphInfoBelow
  "The proof is only complete when all proof branches are solved.
You can jump between proof branches with the arrow buttons or by {pc: clicking | mobile: tapping} on them."
