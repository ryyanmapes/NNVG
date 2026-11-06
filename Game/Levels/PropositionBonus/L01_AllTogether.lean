import Game.Metadata

World "PropositionBonus"
Level 1

Title "All Together"

VisualLevelNumber "A1"

Statement (A B C : Prop) :
    (A ∨ (B → C)) → ((B ∨ (A → C)) → (C ∨ ((A ∧ B) ∨ ((A ∨ B) → C)))) := by
  exact fun h1 h2 => h1.elim
    (fun a => h2.elim (fun b => .inr (.inl ⟨a, b⟩)) (fun ac => .inl (ac a)))
    (fun bc => h2.elim (fun b => .inl (bc b)) (fun ac => .inr (.inr (fun h => h.elim ac bc))))
