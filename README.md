# Natural Numbers Video Game

A Lean 4 game built for Visual Lean's drag-and-drop interface. It needs the
`nnvg` branch of lean4game (`../lean4game`), which adds the level-format
features it uses. The spec lives in `../../NNVG_plans`.

## Layout

- `Game/Levels/Intro`: the welcome text (a `VisualTextLevel`) before the map splits.
- `Game/Levels/Rewrite`: Rewrite World, played entirely in Rewrite Mode (`VisualRewriteOnly`).
- `Game/Levels/RewriteBonus`: bonus levels A1 and A2, branching off Rewrite World level 2 (`VisualBonusOf Rewrite 3`).
- `Game/Levels/Proposition`: Proposition World up to level 5, played on the canvas.
- `Game/Levels/PropositionRight`: Proposition World from level 6, the right branch of its fork (`VisualContinues Proposition`).
- `Game/Levels/PropositionBonus`: bonus level A1, branching off level 6.
- `Game/Levels/Induction`: Induction World up to its boss, in Rewrite Mode.
- `Game/Levels/InductionJoined`: Induction World past the barrier, where Proposition World's left branch joins it (`VisualContinues Induction`).
- `Game/Levels/InductionBonus`: bonus level A1, branching off Induction World's boss.
- `Game/MyNat/Definition.lean`: the game's own natural numbers `MyNat` (`ℕ`), as in NNG4, with the successor named `S`.
- `Game/MyNat/Fraction.lean`: the small `ℚ` that the fraction levels use.
- `Game/MyNat/Induction.lean`: `induction n with d hd`, which Visual Lean plays, without Mathlib.
- `test/VisualMoves.lean`: replays the levels' solutions with Visual Lean's tactics.

Each world is a column of levels on the path map (`VisualPathMap` in `Game.lean`).
Map labels come from `VisualLevelNumber`, so levels show as 0, 1, 2, … and the
bonuses as A1, A2, while Lean numbers them from 1.

A Lean world is one unbroken chain of levels, so a named world that other paths join or
leave partway is split into several Lean worlds, joined with `Dependency` and
`VisualContinues`. A level's map node, title and unlocking all follow from that. It's
also why the player returns to the map at a fork: it's the end of a Lean world.

## Conventions

- A theorem documented `in "Axioms"` shows in the axiom colour in Rewrite Mode.
- A variable named `frac1over2` displays as a vertical fraction.
- A name ending in `_inv`, like `a_inv`, displays with `⁻¹`.

## Build and play locally

```bash
lake build                          # writes .lake/gamedata
lake env lean test/VisualMoves.lean # silent when every move works
cd ../lean4game && npm start        # then open http://localhost:3000/g/local/NNVG/visual
```

`npm start` runs the native relay, so Lean (v4.28.0, via elan) must be on the PATH.
