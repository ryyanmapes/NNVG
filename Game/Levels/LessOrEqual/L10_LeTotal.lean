import Game.Levels.LessOrEqual.L09_LeOne

World "LessOrEqual"
Level 10

Title "`≤` is Total (≤ World Boss)"

VisualLevelNumber "10"
VisualBossLevel

VisualGoalInfo below false "Induct after only `x` is introduced, to get a more general inductive hypothesis."

namespace MyNat

Introduction
"
This is I think the toughest level yet. Tips: dragging `cases` onto a number `a`
splits into the cases `a = 0` and `a = S b`. And don't choose a side of an `∨` goal
until your hypotheses guarantee that you can prove it!
"

/-- `le_total x y` is a proof that `x ≤ y` or `y ≤ x`. -/
TheoremDoc MyNat.le_total as "le_total" in "≤"

Statement le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction y with d hd
  · exact .inr (zero_le x)
  · exact hd.elim (fun h1 => .inl (le_trans x d _ h1 (le_succ_self d)))
      (fun h2 => by
        cases h2 with
        | intro e he =>
          cases e with a
          · exact .inl (by rw [he, add_zero]; exact le_succ_self d)
          · rw [he, add_succ, ← succ_add, ← add_one_eq_succ]
            exact .inr (⟨a, reflection _⟩ : ∃ c, d + 1 + a = d + 1 + c))

Conclusion
"
Very well done.

A passing mathematician remarks that you've just proved that `ℕ` is totally
ordered.
"
