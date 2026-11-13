import Game.Levels.AdvAddition.L04_AddRightEqSelf

World "AdvAddition"
Level 5

Title "`add_right_eq_zero` (Advanced Addition World Boss)"

VisualLevelNumber "5"
VisualBossLevel

-- The cases card, explained; its hint is the one from Visual NNG4, without the
-- sentence about `False` (this game closes goals with `False` on its own).
VisualGoalInfo below false "The `cases` tactic allows you to split a variable into every form it could take. For instance, natural numbers can take two forms: either `0` or the successor of another natural number."

namespace MyNat

Introduction
"
The next result we'll need in `≤` World is that if `a + b = 0` then `a = 0` and `b = 0`.
Let's prove the first of these facts in this level. The second follows from it by
swapping `a` and `b`, so you'll get that one for free.

## A new tactic: `cases`

The `cases` tactic will split an object or hypothesis up into the possible ways
that it could have been created.

For example, sometimes you want to deal with the two cases `b = 0` and `b = S d` separately,
but don't need the inductive hypothesis `hd` that comes with induction on `b`.
In this situation you can drag `cases` onto `b` instead. There are two ways to make
a number: it's either zero or a successor. So you will end up with two goals, one
with `b = 0` and one with `b = S d`.
"

/--
## Summary

If `n` is a number, then dragging `cases` onto `n` will break the goal into two goals,
one with `n = 0` and the other with `n = S d`.

If `h` is a proof (for example a hypothesis), then dragging `cases` onto `h` will break
the proof up into the pieces used to prove it.

## Example

If `n : ℕ` is a number, then dragging `cases` onto `n` will break the goal into two goals,
one with `n` replaced by 0 and the other with `n` replaced by `S d`. This
corresponds to the mathematical idea that every natural number is either `0`
or a successor.

## Example

If `h : a ≤ b` is a hypothesis, then dragging `cases` onto `h` will create a new number `c`
and a proof `hc : b = a + c`. This is because the *definition* of `a ≤ b` is
`∃ c, b = a + c`.
-/
TacticDoc cases

NewTactic cases

/--  A proof that $a+b=0 \implies a=0$. -/
TheoremDoc MyNat.add_right_eq_zero as "add_right_eq_zero" in "+"

Statement add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  cases b with d
  · exact fun h => by rw [add_zero] at h; exact h
  · exact fun h => (zero_ne_succ (a + d) (by rw [add_succ] at h; exact h.symm)).elim

/--  A proof that $a+b=0 \implies b=0$. -/
TheoremDoc MyNat.add_left_eq_zero as "add_left_eq_zero" in "+"

-- The mirror image has no level of its own. It is unlocked at the start of `≤` World.
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  rw [add_comm]
  exact add_right_eq_zero b a

Conclusion
"
That's the end of Advanced Addition World!

Swapping `a` and `b` gives the mirror image of this theorem, `add_left_eq_zero`:
if `a + b = 0` then `b = 0`. You'll have both from the next world on, `≤` World.
"
