import Game.Levels.Induction
import Game.Levels.NeqJoined

World "AdvAddition"
Level 1

Title "`add_right_cancel`"

VisualLevelNumber "1"

namespace MyNat

Introduction
"
In this world I will mostly leave you on your own.

`add_right_cancel a b n` is the theorem that $a+n=b+n\\implies a=b$.
"

/-- `add_right_cancel a b n` is the theorem that $a+n=b+n \implies a=b.$ -/
TheoremDoc MyNat.add_right_cancel as "add_right_cancel" in "+"

Statement add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  induction n with d hd
  · exact fun h => by rw [add_zero, add_zero] at h; exact h
  · exact fun h => hd (succ_inj (a + d) (b + d) (by rw [add_succ, add_succ] at h; exact h))

Conclusion
"
Nice!
"
