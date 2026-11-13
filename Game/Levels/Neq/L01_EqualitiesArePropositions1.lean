import Game.Levels.SuccessorJoined
import Game.Levels.PropositionRight

World "Neq"
Level 1

Title "Equalities are Propositions (1)"

VisualLevelNumber "0"

-- Rewrite Mode on the goal is off: the equality is proved like any other proposition.
VisualNoRewriteMode

namespace MyNat

Statement (x : ℕ) : x = 1 → x = 1 := by
  exact fun h => h

VisualGoalInfoOnGoal above false "x = 1 → x = 1" show
  "Equalities are propositions just like any other.
When you have an equality hypothesis matching the goal, try dragging it to the goal instead of rewriting."
