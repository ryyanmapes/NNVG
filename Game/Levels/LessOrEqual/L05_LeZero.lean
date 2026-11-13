import Game.Levels.LessOrEqual.L04_LeTrans

World "LessOrEqual"
Level 5

Title "`x ≤ 0 → x = 0`"

VisualLevelNumber "5"

namespace MyNat

Introduction
"
It's \"intuitively obvious\" that there are no numbers less than zero,
but to prove it you will need a result which you showed in advanced
addition world.
"

/-- `le_zero x` is a proof of `x ≤ 0 → x = 0`. -/
TheoremDoc MyNat.le_zero as "le_zero" in "≤"

Statement le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  cases hx with
  | intro y hy => exact add_right_eq_zero x y hy.symm
