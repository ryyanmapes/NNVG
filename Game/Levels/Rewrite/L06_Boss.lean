import Game.Metadata

World "Rewrite"
Level 6

Title "On The Count of Three (Rewriting World Boss)"

VisualLevelNumber "5"
VisualRewriteOnly
VisualBossLevel

Statement (add_comm : ∀ x y : ℕ, x + y = y + x)
    (add_assoc : ∀ x y z : ℕ, (x + y) + z = x + (y + z))
    (h_two : (1 : ℕ) + 1 = 2) (h_three : (1 : ℕ) + 2 = 3) :
    (1 : ℕ) + 1 + 1 + 1 + 1 + 1 = 1 + 2 + 3 := by
  rw [h_two, add_comm 2 1, h_three, add_assoc 3 1 1, h_two, add_assoc 3 2 1, add_comm 2 1,
    h_three]

VisualTransformText "This is the final boss of Rewriting World!
Next, we'll begin building the Natural Numbers from scratch!"
