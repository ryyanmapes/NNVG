import Game.Metadata

World "PropositionRight"
Level 7

Title "The De Morgan's Law That Is Intuitionistically Valid (Proposition World Boss)"

VisualLevelNumber "13"
VisualBossLevel

Statement (A B : Prop) : ¬(A ∨ B) ↔ (¬A ∧ ¬B) := by
  exact ⟨fun h => ⟨fun hA => h (.inl hA), fun hB => h (.inr hB)⟩,
    fun h hAB => hAB.elim h.1 h.2⟩

VisualGoalInfo above false
  "Note that the *other* De Morgan's law is **not** valid in intuitionistic logic (which is what Lean is built to model).
See the following bonus level."
