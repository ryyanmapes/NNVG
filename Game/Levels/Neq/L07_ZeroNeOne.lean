import Game.Levels.Neq.L06_Ne

World "Neq"
Level 7

Title "`zero_ne_one`"

VisualLevelNumber "6"

namespace MyNat

Introduction
"
Peano's last axiom is `zero_ne_succ a`, a proof that `0 ≠ S a`: zero is not the
successor of any number.
"

/-- `zero_ne_succ a` is a proof of `0 ≠ S a`, which means `0 = S a → False`. -/
TheoremDoc MyNat.zero_ne_succ as "zero_ne_succ" in "Peano"

NewTheorem MyNat.zero_ne_succ
VisualEmphasize MyNat.zero_ne_succ

/-- `zero_ne_one` is a proof of `0 ≠ 1`. -/
TheoremDoc MyNat.zero_ne_one as "zero_ne_one" in "012"

Statement zero_ne_one : (0 : ℕ) ≠ 1 := by
  rw [one_eq_succ_zero]
  exact zero_ne_succ 0

Conclusion
"
Completing this level also unlocks `one_ne_zero`, a proof of `1 ≠ 0`.
"
