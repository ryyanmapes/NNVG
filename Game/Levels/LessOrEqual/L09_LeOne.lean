import Game.Levels.LessOrEqual.L08_SuccLeSucc

World "LessOrEqual"
Level 9

Title "`le_one`"

VisualLevelNumber "9"

VisualGoalInfo below false "Don't forget about the `cases` tactic!"

namespace MyNat

Introduction
"
We've seen `le_zero`, the proof that if `x ≤ 0` then `x = 0`.
Now we'll prove that if `x ≤ 1` then `x = 0` or `x = 1`.
"

/-- `le_one x` is a proof that if `x ≤ 1` then `x = 0` or `x = 1`. -/
TheoremDoc MyNat.le_one as "le_one" in "≤"

Statement le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with y
  · exact .inl (reflection 0)
  · exact .inr (by rw [le_zero y (succ_le_succ y 0 (by rw [← one_eq_succ_zero]; exact hx)), one_eq_succ_zero])

Conclusion
"
If you solved this level then you are ready for the boss!
"
