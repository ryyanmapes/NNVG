import Game.Levels.Power.L01_ZeroPowZero

World "Power"
Level 2

Title "`zero_pow_succ`"

VisualLevelNumber "2"

namespace MyNat

Introduction
"
We've just seen that `0 ^ 0 = 1`, but if `n`
is a successor, then `0 ^ n = 0`. We prove that here.
"

/-- `pow_succ a b : a ^ (S b) = a ^ b * a` is one of the
two axioms defining exponentiation in this game.
-/
TheoremDoc MyNat.pow_succ as "pow_succ" in "^"

/--
Although $0^0=1$ in this game, $0^n=0$ if $n>0$, i.e., if
$n$ is a successor.
-/
TheoremDoc MyNat.zero_pow_succ as "zero_pow_succ" in "^"

NewTheorem MyNat.pow_succ
VisualEmphasize MyNat.pow_succ

Statement zero_pow_succ (m : ℕ) : (0 : ℕ) ^ S m = 0 := by
  rw [pow_succ, mul_zero]
