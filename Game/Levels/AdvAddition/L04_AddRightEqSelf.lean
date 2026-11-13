import Game.Levels.AdvAddition.L03_AddLeftEqSelf

World "AdvAddition"
Level 4

Title "`add_right_eq_self`"

VisualLevelNumber "4"

namespace MyNat

Introduction
"
`add_right_eq_self x y` is the theorem that $x + y = x\\implies y=0.$
Two ways to do it spring to mind; I'll mention them when you've solved it.
"

/-- `add_right_eq_self x y` is the theorem that $x + y = x \implies y=0.$ -/
TheoremDoc MyNat.add_right_eq_self as "add_right_eq_self" in "+"

Statement add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  rw [add_comm]
  exact add_left_eq_self y x
