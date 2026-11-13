import Game.Levels.AdvMultiplication.L09_MulRightEqSelf

World "AdvMultiplication"
Level 10

Title "`mul_left_cancel` (Advanced Multiplication World Boss)"

VisualLevelNumber "10"
VisualBossLevel

-- Inducting on `b` while `c` is still bound in the goal is what makes the inductive
-- hypothesis general enough.
VisualGoalInfo below false "Perform induction on `b` as soon as it is introduced."

namespace MyNat

Introduction
"
In this level we prove that if `a * b = a * c` and `a ≠ 0` then `b = c`. It is tricky, for
several reasons. One of these is that
we need to introduce a new idea: we will need to understand the concept of
mathematical induction a little better.

Inducting on `b` once everything is introduced is too naive, because in the inductive step
the hypothesis is `a * d = a * c → d = c` but what we know is `a * S d = a * c`,
so the induction hypothesis does not apply!

Assume `a ≠ 0` is fixed. The actual statement we want to prove by induction on `b` is
\"for all `c`, if `a * b = a * c` then `b = c`\". This *can* be proved by induction,
because we now have the flexibility to change `c`.
"

/-- `mul_left_cancel a b c` is a proof that if `a ≠ 0` and `a * b = a * c` then `b = c`. -/
TheoremDoc MyNat.mul_left_cancel as "mul_left_cancel" in "*"

Statement mul_left_cancel (a b : ℕ) : ∀ c : ℕ, a ≠ 0 → a * b = a * c → b = c := by
  induction b with d hd
  · exact fun c ha h => (mul_eq_zero a c (by rw [mul_zero] at h; exact h.symm)).elim
      (fun h0 => (ha h0).elim) (fun h0 => h0.symm)
  · exact fun c ha h => by
      cases c with e
      · exact (ha (add_left_eq_zero (a * d) a (by rw [mul_succ, mul_zero] at h; exact h))).elim
      · rw [hd e ha (add_right_cancel (a * d) (a * e) a (by rw [mul_succ, mul_succ] at h; exact h))]
