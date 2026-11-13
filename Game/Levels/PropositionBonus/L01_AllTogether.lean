import Game.Metadata

World "PropositionBonus"
Level 1

Title "Many Such Cases"

VisualLevelNumber "A1"

Statement (A B C : Prop) :
    (A ∨ (B → C)) → ((B ∨ (A → C)) → ((A ∧ B) ∨ ((A ∨ B) → C))) := by
  exact fun h1 h2 => h1.elim
    (fun a => h2.elim (fun b => .inl ⟨a, b⟩) (fun ac => .inr (fun _ => ac a)))
    (fun bc => h2.elim (fun b => .inr (fun _ => bc b)) (fun ac => .inr (fun h => h.elim ac bc)))
