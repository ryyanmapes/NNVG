import Game.Levels.Power
import Game.Levels.AdvMultiplication
import Game.Levels.NeqBoss

World "Outro"
Level 1

Title "The End"

VisualLevelNumber "?"
VisualTextLevel

namespace MyNat

Introduction
"
Thank you for playing!
"

Statement : True := by
  trivial

NewHiddenTactic trivial
