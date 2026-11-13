import Game.Levels.AdvAddition.L01_AddRightCancel

World "AdvAddition"
Level 2

Title "`add_left_cancel`"

VisualLevelNumber "2"

namespace MyNat

Introduction
"
`add_left_cancel a b n` is the theorem that $n+a=n+b\\implies a=b$.
You can prove it by induction on `n` or you can deduce it from `add_right_cancel`.
"

/-- `add_left_cancel a b n` is the theorem that $n+a=n+b \implies a=b.$ -/
TheoremDoc MyNat.add_left_cancel as "add_left_cancel" in "+"

Statement add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  rw [add_comm n a, add_comm n b]
  exact add_right_cancel a b n
