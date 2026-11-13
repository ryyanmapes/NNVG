import Game.Metadata

World "PropositionBonusB"
Level 2

Title "The Other De Morgan's Law (Rightwards with the Law of Excluded Middle)"

VisualLevelNumber "B2"

Statement (A B : Prop) (hA : A ∨ ¬A) (hB : B ∨ ¬B) : ¬(A ∧ B) → (¬A ∨ ¬B) := by
  exact fun h => hA.elim
    (fun a => hB.elim (fun b => (h ⟨a, b⟩).elim) .inr)
    .inl

VisualGoalInfo above false
  "It turns out that this direction is not intuitionistically valid.
You'll have to use two hypotheses given by the Law of Excluded Middle to solve this level!
($∀ P, P ∨ ¬P$)"
