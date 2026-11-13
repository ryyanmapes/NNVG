import Game.Levels.LessOrEqual.L03_LeSuccSelf

World "LessOrEqual"
Level 4

Title "Transitivity"

VisualLevelNumber "4"

namespace MyNat

Introduction
"
In this level, we see inequalities as *hypotheses*. We have not seen this before.
{pc: Click | mobile: Tap} `hxy` to take it apart.
"

/--
`le_trans x y z` is a proof that if `x ≤ y` and `y ≤ z` then `x ≤ z`.
More precisely, it is a proof that `x ≤ y → (y ≤ z → x ≤ z)`. In words,
If $x \le y$ then (pause) if $y \le z$ then $x \le z$.

## A note on associativity

In Lean, `a + b + c` means `(a + b) + c`, because `+` is left associative. However
`→` is right associative. This means that `x ≤ y → y ≤ z → x ≤ z` in Lean means
exactly that `≤` is transitive. This is different to how mathematicians use
$P \implies Q \implies R$; for them, this usually means that $P \implies Q$
and $Q \implies R$.
-/
TheoremDoc MyNat.le_trans as "le_trans" in "≤"

VisualHypInfoOnHyp hxy "x ≤ y" show "{pc: Click | mobile: Tap} there-exists hypotheses to name a variable fulfilling the condition."

Statement le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  cases hxy with
  | intro a ha =>
    cases hyz with
    | intro b hb => exact (⟨a + b, by rw [hb, ha, add_assoc]⟩ : ∃ c, z = x + c)

Conclusion
"
A passing mathematician remarks that with reflexivity and transitivity out of the way,
you have proved that `≤` is a *preorder* on `ℕ`.
"
