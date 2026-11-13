import Game.Levels.Neq
import Game.Levels.Induction

World "NeqJoined"
Level 1

Title "Zero or No Zero"

VisualLevelNumber "8"

namespace MyNat

Statement : ∀ n : ℕ, n = 0 ∨ n ≠ 0 := by
  exact fun n => by
    induction n with d hd
    · exact .inl (reflection 0)
    · exact .inr (fun h => zero_ne_succ d h.symm)
