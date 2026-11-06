import Game.Levels.Induction

World "InductionJoined"
Level 1

Title "`zero_add`"

VisualLevelNumber "4"

namespace MyNat

Introduction
"
In this level we're going to prove that $0+n=n$, where $n$ is a secret natural number.

Wait, don't we already know that? No! We know that $n+0=n$, but that's `add_zero`.
This is `zero_add`, which is different.

The difficulty with proving `0 + n = n` is that we do not have a *formula* for
`0 + n` in general, we can only use `add_zero` and `add_succ` once
we know whether `n` is `0` or a successor. The `induction` tactic splits into these two cases.

The base case will require us to prove `0 + 0 = 0`, and the inductive step
will ask us to show that if `0 + d = d` then `0 + S d = S d`. Because
`0` and successor are the only way to make numbers, this will cover all the cases.

See if you can do your first induction proof in Lean.
"

VisualTacticHypInfo induction n "Use the induction tactic to write proofs by induction on a variable.
Drag the induction tactic to a natural number variable hypothesis to induct on it."

VisualProofGraphInfo "There are now two goals to prove: the base case when $n = 0$, and the inductive step where we assume $n$ and must show $n+1$.
Use the proof stream graph to prove each goal separately."

VisualGoalInfoOnGoal below true "0 + 0 = 0" show "{pc: Double-click | mobile: Double-tap} the goal equality to enter Rewrite Mode."

/-- `zero_add x` is the proof of `0 + x = x`. -/
TheoremDoc MyNat.zero_add as "zero_add" in "Theorems"

Statement zero_add (n : ℕ) : 0 + n = n := by
  induction n with d hd
  · rw [add_zero]
  · rw [add_succ, hd]

NewTactic induction

Conclusion
"
This lemma would have been easy if we had known that `x + y = y + x`. That theorem
is called `add_comm` and it is *true*, but unfortunately its proof *uses* both
`add_zero` and `zero_add`!
"
