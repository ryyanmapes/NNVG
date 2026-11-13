import Game.Levels.AdvMultiplication.L05_LeMulRight

World "AdvMultiplication"
Level 6

Title "`mul_right_eq_one`"

VisualLevelNumber "6"

namespace MyNat

Introduction
"
This level proves `x * y = 1 → x = 1`, the multiplicative analogue of Advanced Addition
World's `x + y = 0 → x = 0`. The strategy is to prove that `x ≤ 1` and then use the
lemma `le_one` from `≤` World.
"

/--
`mul_right_eq_one a b` is a proof that `a * b = 1 → a = 1`.
-/
TheoremDoc MyNat.mul_right_eq_one as "mul_right_eq_one" in "*"

Statement mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  exact (le_one x (by rw [← h]; exact le_mul_right x y (by rw [h]; exact one_ne_zero))).elim
    (fun h0 => (one_ne_zero (by rw [h0, zero_mul] at h; exact h.symm)).elim)
    (fun h1 => h1)
