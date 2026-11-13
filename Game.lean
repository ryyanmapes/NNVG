import Game.Levels.Intro
import Game.Levels.Rewrite
import Game.Levels.RewriteBonus
import Game.Levels.Proposition
import Game.Levels.PropositionRight
import Game.Levels.PropositionBonus
import Game.Levels.PropositionBonusB
import Game.Levels.Successor
import Game.Levels.SuccessorJoined
import Game.Levels.Induction
import Game.Levels.Neq
import Game.Levels.NeqJoined
import Game.Levels.NeqBoss
import Game.Levels.Multiplication
import Game.Levels.Power
import Game.Levels.PowerBonus
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual
import Game.Levels.AdvMultiplication
import Game.Levels.Outro

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

-- Rewrite World leads to Successor World.
Dependency Rewrite → Successor

-- Proposition World forks: its left branch joins the middle of Successor World, which
-- can't continue until both are finished, and its right branch carries on alone.
Dependency Successor → SuccessorJoined
Dependency Proposition → SuccessorJoined
Dependency Proposition → PropositionRight

-- Successor World leads to Induction World, and with all of Proposition World to the
-- ≠ World, whose last levels also wait for Induction World.
Dependency SuccessorJoined → Induction
Dependency SuccessorJoined → Neq
Dependency PropositionRight → Neq
Dependency Neq → NeqJoined
Dependency Induction → NeqJoined

-- The worlds ported from NNG4. Multiplication World and Power World hang off Induction
-- World on the far left. Advanced Addition World needs Induction World (through the ≠
-- World's level 8) and leads to ≤ World on the right. Advanced Multiplication World
-- carries on below ≤ World and needs only that and Multiplication World, whose path
-- comes across from the far left. (MakeGame drops any edge a path already implies.)
Dependency Induction → Multiplication
Dependency Multiplication → Power
Dependency NeqJoined → AdvAddition
Dependency AdvAddition → LessOrEqual
Dependency LessOrEqual → AdvMultiplication
Dependency Multiplication → AdvMultiplication

-- The End, the closing text at the bottom of the map, follows the final bosses of
-- Power World, Advanced Multiplication World and the ≠ World (its boss off to the side).
Dependency Power → Outro
Dependency AdvMultiplication → Outro
Dependency NeqBoss → Outro

VisualPathMap

-- In this game, a proof of `False` closes any goal, with no `exfalso` step.
VisualFastExfalso

-- Hints stay up as the proof moves on, until the next one replaces them.
VisualPersistentHints

-- Rewrite Mode on a goal shows the check mark once both sides match, in every level.
VisualRewriteCheck

-- The successor function is `S`, also in the specialization view's term builder.
VisualSuccessorName S

-- A goal `a = a` isn't closed by clicking it: the player opens it in Rewrite Mode and
-- uses the check mark.
VisualNoGoalRfl

-- The inventory's tabs are NNG4's. The axioms sit among the theorems of their tab, in
-- their own colour.
VisualAxioms MyNat.one_eq_succ_zero MyNat.two_eq_succ_one MyNat.three_eq_succ_two
  MyNat.four_eq_succ_three MyNat.add_zero MyNat.add_succ MyNat.mul_zero MyNat.mul_succ
  MyNat.pow_zero MyNat.pow_succ MyNat.reflection MyNat.succ_inj MyNat.zero_ne_succ
  MyNat.peano_cases

MakeGame
