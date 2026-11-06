import Game.MyNat.Definition

/-!
# Induction

Visual Lean plays an induction as `induction n with d hd`, as in NNG4. This gives that
syntax to Lean's own `induction`, and has the base case show `0` instead of `MyNat.zero`.
-/

namespace MyNat

/-- Induction on `MyNat`, with a base case that shows `0`. -/
@[induction_eliminator]
theorem rec' {P : ℕ → Prop} (zero : P 0) (S : (n : ℕ) → P n → P (MyNat.S n)) (t : ℕ) : P t := by
  induction t using MyNat.rec with
  | zero => exact zero
  | S n ih => exact S n ih

end MyNat

/-- `induction n with d hd` splits the goal into the base case for `0` and the inductive
step for `S d`, where `hd` is the inductive hypothesis. -/
macro (name := MyNat.inductionWith) "induction " target:ident " with " d:ident hd:ident : tactic =>
  `(tactic| induction $target:ident with
    | zero => ?_
    | S $d:ident $hd:ident => ?_)
