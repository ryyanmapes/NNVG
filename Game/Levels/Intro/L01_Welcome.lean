import Game.Metadata

World "Intro"
Level 1

Title "Welcome"

VisualLevelNumber "?"
VisualTextLevel

Introduction
"
Welcome to the Natural Numbers Video Game!

Though you'll be using a simplified visual interface, make no mistake: running in the
background on your device is a Lean server translating every move into formal
mathematical code. This is not just a game about mathematics: it *is* mathematics!

So, without further ado, let's get started!
"

-- A text-only level: the map shows the introduction and completes the level when the
-- player closes it. The statement only lets the classic interface open the level.
Statement : True := by
  trivial

NewHiddenTactic trivial
