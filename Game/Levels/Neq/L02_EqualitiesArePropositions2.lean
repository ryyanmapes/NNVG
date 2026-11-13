import Game.Levels.Neq.L01_EqualitiesArePropositions1

World "Neq"
Level 2

Title "Equalities are Propositions (2)"

VisualLevelNumber "1"

-- The swap button, in Rewrite Mode on `1 = x`, is the way through.

namespace MyNat

Statement (x y : ℕ) : 1 = x → ((x = 1 → y = 2) → 2 = y) := by
  exact fun h h1 => (h1 h.symm).symm

VisualGoalInfoOnGoal above false "1 = x → (x = 1 → y = 2) → 2 = y" show
  "You'll have to reverse the direction of an equality to solve this level.
Try entering `1 = x` in Rewriting Mode."

-- In Rewriting Mode on `1 = x`: an arrow to the swap button.
VisualTransformSwapInfoOnHypothesis "1 = x" show
  "Use the swap button to swap the two sides of the equation!"
