import Game.Levels.LessOrEqual.L06_LeAntisymm

World "LessOrEqual"
Level 7

Title "`∨`"

VisualLevelNumber "7"

VisualGoalInfo below false "{pc: Click | mobile: Tap} an 'or' hypothesis to split into two branches, one where each side is assumed. {pc: Click | mobile: Tap} an 'or' goal to specify which side must be true. Be careful not to dead end yourself by specifying the goal too early!"

namespace MyNat

Introduction
"
Totality of `≤` is the boss level of this world, and it's coming up soon. It says that
if `a` and `b` are naturals then either `a ≤ b` or `b ≤ a`.
But we haven't talked about \"or\" in this world yet. Here's a run-through.

1) The notation for \"or\" is `∨`.

2) If you have an \"or\" statement in the *goal*, {pc: click | mobile: tap} it to
choose a side. But don't choose a side unless your
hypotheses guarantee that it's the correct one.

3) If you have an \"or\" statement as a *hypothesis* `h`, then {pc: clicking | mobile: tapping}
it will create two goals, one where you went left, and the other where you went right.
"

Statement (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  exact h.elim (fun hx => .inr hx) (fun hy => .inl hy)

Conclusion
"
Two more levels, then the boss.
"
