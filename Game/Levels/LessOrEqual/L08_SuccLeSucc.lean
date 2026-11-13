import Game.Levels.LessOrEqual.L07_OrSymm

World "LessOrEqual"
Level 8

Title "`S x ≤ S y → x ≤ y`"

VisualLevelNumber "8"

namespace MyNat

Introduction
"
We've proved that `x ≤ 0` implies `x = 0`. The next level
will prove which numbers are `≤ 1`. This lemma will be helpful for it.
"

/-- `succ_le_succ x y` is a proof that if `S x ≤ S y` then `x ≤ y`. -/
TheoremDoc MyNat.succ_le_succ as "succ_le_succ" in "≤"

Statement succ_le_succ (x y : ℕ) (hx : S x ≤ S y) : x ≤ y := by
  cases hx with
  | intro d hd => exact (⟨d, succ_inj y (x + d) (by rw [succ_add] at hd; exact hd)⟩ : ∃ c, y = x + c)
