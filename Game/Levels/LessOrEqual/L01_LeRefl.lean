import Game.Levels.AdvAddition

World "LessOrEqual"
Level 1

Title "`le_refl`"

VisualLevelNumber "1"

VisualGoalInfo below false "{pc: Click | mobile: Tap} there-exists goals to enter Construction Mode."

namespace MyNat

Introduction
"
`a ≤ b` is *notation* for `∃ c, b = a + c`. This \"backwards E\"
means \"there exists\". So `a ≤ b` means that there exists
a number `c` such that `b = a + c`. This definition works
because there are no negative numbers in this game.

To *prove* an \"exists\" statement, {pc: click | mobile: tap} the goal and build the
number that works. Let's see an example.
"

/--
`a ≤ b` is *notation* for `∃ c, b = a + c`.

Because this game doesn't have negative numbers, this definition
is mathematically valid.

This means that if you have a goal of the form `a ≤ b` you can
make progress by {pc: clicking | mobile: tapping} it and building the number `c`, and if
you have a hypothesis `h : a ≤ b`, you can make progress by {pc: clicking | mobile: tapping}
it to get the number `c` and the proof that `b = a + c`.
-/
DefinitionDoc LE as "≤"

NewDefinition LE

-- Advanced Addition World proved `add_right_eq_zero`; its mirror image comes with it.
NewTheorem MyNat.add_left_eq_zero

/--
`le_refl x` is a proof of `x ≤ x`.

The reason for the name is that this lemma is "reflexivity of $\le$"
-/
TheoremDoc MyNat.le_refl as "le_refl" in "≤"

Statement le_refl (x : ℕ) : x ≤ x := by
  exact (⟨0, by rw [add_zero]⟩ : ∃ c, x = x + c)
