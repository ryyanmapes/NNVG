import Game.Levels.NeqJoined

World "NeqBoss"
Level 1

Title "Equality in ℕ is Decidable (≠ World Boss)"

VisualLevelNumber "9"
VisualBossLevel

-- The hint stays up (hints persist in this game) until induction has been done twice
-- the right way round: fix `a`, induct on it, fix `b`, induct on it. Each hint below
-- with no text matches one of the four goals that leaves, and clears it. In the two
-- `S(d)` cases the inductive hypothesis has to hold for every `b`, which it doesn't if
-- `b` was fixed before the induction on `a`.
VisualGoalInfoOnGoal above false "∀ (a b : ℕ), a = b ∨ a ≠ b" show
  "You may want to revisit this level after you've learned to use double induction."
VisualGoalInfoOnGoal above false "0 = 0 ∨ 0 ≠ 0" show ""
VisualGoalInfoOnGoal above false "0 = S(d) ∨ 0 ≠ S(d)" show ""
VisualGoalInfoOnGoalWithHyp above false "S(d) = 0 ∨ S(d) ≠ 0" "∀ (b : ℕ), d = b ∨ d ≠ b" show ""
VisualGoalInfoOnGoalWithHyp above false "S(d) = S(d2) ∨ S(d) ≠ S(d2)" "∀ (b : ℕ), d = b ∨ d ≠ b" show ""
-- If `b` was fixed first, the zero case can still be finished, which clears the hint, but
-- the `S(d)` case is stuck with a hypothesis about that one `b`: the hint comes back.
VisualGoalInfoOnGoalWithHyp above false "S(d) = b ∨ S(d) ≠ b" "d = b ∨ d ≠ b" show
  "You may want to revisit this level after you've learned to use double induction."

namespace MyNat

Statement : ∀ a b : ℕ, a = b ∨ a ≠ b := by
  exact fun a => by
    induction a with d hd
    · exact fun b => by
        induction b with e he
        · exact .inl (reflection 0)
        · exact .inr (zero_ne_succ e)
    · exact fun b => by
        induction b with e he
        · exact .inr (fun h => zero_ne_succ d h.symm)
        · exact (hd e).elim (fun h => .inl (by rw [h])) (fun h => .inr (fun h2 => h (succ_inj d e h2)))
