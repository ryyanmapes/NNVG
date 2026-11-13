import Game.Levels.AdvMultiplication.L02_MulLeftNeZero

World "AdvMultiplication"
Level 3

Title "`eq_succ_of_ne_zero`"

VisualLevelNumber "3"

namespace MyNat

Introduction
"
Multiplication usually makes a number bigger, but multiplication by zero can make
it smaller. Thus many lemmas about inequalities and multiplication need the
hypothesis `a ≠ 0`. Here is a key lemma that enables us to use this hypothesis.
"

/-- `eq_succ_of_ne_zero a` is a proof that `a ≠ 0 → ∃ n, a = S n`. -/
TheoremDoc MyNat.eq_succ_of_ne_zero as "eq_succ_of_ne_zero" in "≤"

Statement eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = S n := by
  cases a with d
  · exact (ha (reflection 0)).elim
  · exact ⟨d, reflection _⟩
