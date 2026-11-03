import Game.Levels.Intro
import Game.Levels.Rewrite
import Game.Levels.RewriteBonus
import Game.Levels.Proposition

Title "Natural Numbers Video Game"

Introduction
"
Welcome to the Natural Numbers Video Game! It is played in Visual Lean: you build
proofs by dragging and clicking, and a Lean server checks every move.
"

Info "
The Natural Numbers Video Game is a version of the Natural Number Game made for
Visual Lean's drag-and-drop interface.
"

Languages "English"
CaptionShort "Prove things about the natural numbers by dragging and clicking."
CaptionLong "A Natural Number Game built for Visual Lean. Start with substitutions and
propositions, then go wherever the map leads."

-- After the welcome text, the map splits: Rewrite World on the left and
-- Proposition World on the right. Either can be played first.
Dependency Intro → Rewrite
Dependency Intro → Proposition

VisualPathMap

MakeGame
