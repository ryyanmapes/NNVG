import Game.Metadata

World "PropositionRight"
Level 2

Title "Disjunction"

VisualLevelNumber "8"

Statement (Z A B : Prop) : Z ∨ ((A ∨ B) → (B ∨ A)) := by
  exact .inr (fun h => h.elim .inr .inl)

VisualGoalInfoOnGoal above false "Z ∨ (A ∨ B → B ∨ A)" show
  "The symbol $∨$ represents ‘or’. In order to prove an ‘or’ goal, you must choose to prove either the left side or the right side."

VisualGoalInfoOnGoal above false "Z" show
  "We don't have any way of proving $Z$, so this is a dead end.
Try undoing or resetting with the buttons on the bottom left!"

VisualGoalInfoOnGoal above false "A ∨ B → B ∨ A" show
  "$∨$ hypotheses can be split by {pc: clicking | mobile: tapping} on them.
In order to finish the proof, you'll have to show that the goal is reachable from both sides!"

VisualGoalInfoOnGoalWithHyp above false "B ∨ A" "A ∨ B" show
  "$∨$ hypotheses can be split by {pc: clicking | mobile: tapping} on them.
In order to finish the proof, you'll have to show that the goal is reachable from both sides!"

-- Splitting the `∨` goal while the `∨` hypothesis is still whole.
VisualGoalInfoOnGoalWithHyp above false "B" "A ∨ B" show
  "Whether to pick $A$ or $B$ will depend on which branch of the $∨$ hypothesis we're in.
So this is a dead end: try undoing or resetting with the buttons on the bottom left!"

VisualGoalInfoOnGoalWithHyp above false "A" "A ∨ B" show
  "Whether to pick $A$ or $B$ will depend on which branch of the $∨$ hypothesis we're in.
So this is a dead end: try undoing or resetting with the buttons on the bottom left!"
