import Game.Levels.Induction.L03_AddComm

World "Induction"
Level 4

Title "Associativity of Addition"

VisualLevelNumber "4"

namespace MyNat

Introduction
"
We've been adding up two numbers; in this level we will add up three.

What does $x+y+z$ *mean*? It could either mean $(x+y)+z$, or it
could mean $x+(y+z)$. In Lean, $x+y+z$ means $(x+y)+z$.

But why do we care which one it means; $(x+y)+z$ and $x+(y+z)$ are *equal*!

That's true, but we didn't prove it yet. Let's prove it now by induction.
"

/-- `add_assoc a b c` is a proof that `(a + b) + c = a + (b + c)`. -/
TheoremDoc MyNat.add_assoc as "add_assoc" in "+"

Statement add_assoc : ∀ a b c : ℕ, a + b + c = a + (b + c) := by
  exact fun a b c => by
    induction c with d hd
    · rw [add_zero, add_zero]
    · rw [add_succ, add_succ, hd, add_succ]

Conclusion
"
A passing mathematician congratulates you on proving that the natural numbers
are an additive commutative monoid.
"
