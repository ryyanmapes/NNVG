import Game.Levels.Neq.L02_EqualitiesArePropositions2

World "Neq"
Level 3

Title "Equalities are Propositions (3)"

VisualLevelNumber "2"

namespace MyNat

Statement (x : ℕ) : x = 1 → (x = 1 ∧ (S x = 2 ∨ (1 : ℕ) = 0)) := by
  exact fun h => ⟨h, .inl (by rw [h, two_eq_succ_one])⟩

VisualGoalInfoOnGoal above false "x = 1 → (x = 1 ∧ (S(x) = 2 ∨ 1 = 0))" show
  "Equalities are propositions just like any other."

-- Only while the goal is `x = 1`: after that, no hint.
VisualGoalInfoOnGoal above false "x = 1" while
  "You can prove this faster by dragging `x = 1` to the goal."
