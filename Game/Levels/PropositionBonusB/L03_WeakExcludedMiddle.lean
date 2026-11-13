import Game.Metadata

World "PropositionBonusB"
Level 3

Title "The Other De Morgan's Law (Rightwards with the Weak Law of Excluded Middle)"

VisualLevelNumber "B3"

Statement (A B : Prop) (hA : ¬A ∨ ¬¬A) (hB : ¬B ∨ ¬¬B) : ¬(A ∧ B) → (¬A ∨ ¬B) := by
  exact fun h => hA.elim .inl
    (fun nna => hB.elim .inr
      (fun nnb => (nna (fun a => nnb (fun b => h ⟨a, b⟩))).elim))

VisualGoalInfo above false
  "We can actually do better than requiring the Law of Excluded Middle!
Try now with the Weak Law of Excluded Middle.
($∀ P, ¬P ∨ ¬¬P$)"
