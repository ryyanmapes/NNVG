import Game.Levels.Neq.L03_EqualitiesArePropositions3

World "Neq"
Level 4

Title "`reflection`"

VisualLevelNumber "3"

namespace MyNat

/-- `reflection n` is a proof of `n = n`: every natural number is equal to itself. -/
TheoremDoc MyNat.reflection as "reflection" in "Peano"

NewTheorem MyNat.reflection

Statement : S 0 = S 0 ∧ ((1 : ℕ) = 1 ∧ (2 : ℕ) = 2) := by
  exact ⟨reflection _, reflection _, reflection _⟩

-- Specializing `reflection` by hand, for the first goal.
VisualTheoremInfoOnGoalWithoutHyp MyNat.reflection "S(0) = S(0)" "S(0) = S(0)" show
  "We've unlocked a new proposition we can use in any level.
Let's try using it to solve this goal without entering Rewrite Mode.
{pc: Click | mobile: Tap} `reflection` to specialize it to match the goal."

VisualSpecializeBrickInfo "S(_)" "?" onGoal "S(0) = S(0)" show
  "We've now entered specialization mode.
Our goal is `S(0) = S(0)`, so let's drag `S(_)` into the workspace."

VisualSpecializeInfo "S(?)" onGoal "S(0) = S(0)" show
  "Now drag the `0` inside of that!"

VisualSpecializeDoneInfo "S(0)" onGoal "S(0) = S(0)" show
  "{pc: Click | mobile: Tap} ‘Done’ to return to Proposition Mode."

VisualGoalInfoOnGoalWithHyp above false "S(0) = S(0)" "S(0) = S(0)" show
  "Now that we have the proposition we need, drag it to the goal to complete it!"

-- The rest of the goals: drag `reflection` straight onto them.
VisualGoalInfoOnGoal above false "1 = 1 ∧ 2 = 2" show ""

VisualHypGoalInfoOnGoal MyNat.reflection "1 = 1" show
  "You can also drag general propositions to the goal to specialize them to match automatically.
Try it here!"

VisualHypGoalInfoOnGoal MyNat.reflection "2 = 2" show
  "You can also drag general propositions to the goal to specialize them to match automatically.
Try it here!"
