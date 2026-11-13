import Game.Levels.Neq.L04_Reflection

World "Neq"
Level 5

Title "`succ_inj`"

VisualLevelNumber "4"

namespace MyNat

Introduction
"
If `a` and `b` are numbers, then `succ_inj a b` is a proof
that `S a = S b` implies `a = b`.

Peano had this theorem as an axiom. Let's use it to prove $x + 1 = 4 → x = 3$.
We will proceed by manipulating our hypothesis until it becomes the goal.
"

/-- `succ_inj a b` is a proof that `S a = S b` implies `a = b`.
Peano had it as an axiom: `S` is an injective function. -/
TheoremDoc MyNat.succ_inj as "succ_inj" in "Peano"

NewTheorem MyNat.succ_inj
VisualEmphasize MyNat.succ_inj

Statement (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  rw [four_eq_succ_three, add_one_eq_succ] at h
  exact succ_inj x 3 h
