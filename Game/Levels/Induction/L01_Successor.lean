import Game.Metadata

World "Induction"
Level 1

Title "The Successor"

VisualLevelNumber "1"
VisualRewriteOnly

namespace MyNat

/-- `one_eq_succ_zero` is a proof of `1 = S 0`. -/
TheoremDoc MyNat.one_eq_succ_zero as "one_eq_succ_zero" in "Axioms"

/-- `two_eq_succ_one` is a proof of `2 = S 1`. -/
TheoremDoc MyNat.two_eq_succ_one as "two_eq_succ_one" in "Axioms"

/-- `three_eq_succ_two` is a proof of `3 = S 2`. -/
TheoremDoc MyNat.three_eq_succ_two as "three_eq_succ_two" in "Axioms"

/-- `four_eq_succ_three` is a proof of `4 = S 3`. -/
TheoremDoc MyNat.four_eq_succ_three as "four_eq_succ_three" in "Axioms"

NewTheorem MyNat.one_eq_succ_zero MyNat.two_eq_succ_one MyNat.three_eq_succ_two
  MyNat.four_eq_succ_three

Statement : S (S 0) = 2 := by
  rw [← one_eq_succ_zero, ← two_eq_succ_one]

VisualTransformText "The `S` function here represents the ‘successor function’.
It's just a function that takes you from one number up to the next."
