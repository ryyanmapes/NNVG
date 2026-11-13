import Game.Levels.AdvAddition.L02_AddLeftCancel

World "AdvAddition"
Level 3

Title "`add_left_eq_self`"

VisualLevelNumber "3"

namespace MyNat

Introduction
"
`add_left_eq_self x y` is the theorem that $x + y = y\\implies x=0.$
"

/-- `add_left_eq_self x y` is the theorem that $x + y = y \implies x=0.$ -/
TheoremDoc MyNat.add_left_eq_self as "add_left_eq_self" in "+"

Statement add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  exact fun h => add_right_cancel x 0 y (by rw [zero_add]; exact h)

Conclusion
"
Did you use induction on `y`?
"
