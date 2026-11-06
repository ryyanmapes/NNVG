import Game.Levels.Intro
import Game.Levels.Rewrite
import Game.Levels.RewriteBonus
import Game.Levels.Proposition
import Game.Levels.PropositionRight
import Game.Levels.PropositionBonus
import Game.Levels.Induction
import Game.Levels.InductionJoined
import Game.Levels.InductionBonus

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

-- Rewrite World leads to Induction World.
Dependency Rewrite → Induction

-- Proposition World forks: its left branch joins the middle of Induction World, which
-- can't continue until both are finished, and its right branch carries on alone.
Dependency Induction → InductionJoined
Dependency Proposition → InductionJoined
Dependency Proposition → PropositionRight

VisualPathMap

-- In this game, a proof of `False` closes any goal, with no `exfalso` step.
VisualFastExfalso

MakeGame
