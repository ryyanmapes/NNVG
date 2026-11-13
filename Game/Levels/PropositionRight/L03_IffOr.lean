import Game.Metadata

World "PropositionRight"
Level 3

Title "If and Only If (Disjunctions)"

VisualLevelNumber "9"

Statement (A B C : Prop) : ((A ∨ B) ∨ C) ↔ (A ∨ (B ∨ C)) := by
  exact ⟨
    fun h => h.elim (fun hAB => hAB.elim .inl (fun hB => .inr (.inl hB))) (fun hC => .inr (.inr hC)),
    fun h => h.elim (fun hA => .inl (.inl hA)) (fun hBC => hBC.elim (fun hB => .inl (.inr hB)) .inr)⟩
