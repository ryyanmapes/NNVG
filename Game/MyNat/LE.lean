import Game.MyNat.Definition

/-!
# Less than or equal

`a ≤ b` is notation for `∃ c, b = a + c`, as in NNG4. The definition is a `def`, not
reducible, so Visual Lean's cards keep showing `≤` and only the tactics see the `∃`.
-/

namespace MyNat

/-- `a ≤ b` means that there is a `c` with `b = a + c`. -/
def le (a b : MyNat) := ∃ c : MyNat, b = a + c

instance instLE : LE MyNat := ⟨MyNat.le⟩

end MyNat
