# Natural Numbers Video Game

A Lean 4 game built for Visual Lean's drag-and-drop interface. It needs the
`nnvg` branch of lean4game (`../lean4game`), which adds the level-format
features it uses.

## Layout

- `Game/Levels/Intro`: the welcome text (a `VisualTextLevel`) before the map splits.
- `Game/Levels/Rewrite`: Rewrite World, played entirely in Rewrite Mode (`VisualRewriteOnly`).
- `Game/Levels/RewriteBonus`: bonus level A, branching off Rewrite World level 2 (`VisualBonusOf Rewrite 3`).
- `Game/Levels/Proposition`: Proposition World, played on the canvas.
- `Game/MyNat/Definition.lean`: the game's own natural numbers `MyNat` (`ℕ`), as in NNG4.
- `test/VisualMoves.lean`: replays the Rewrite World solutions with Visual Lean's tactics.

Each world is a column of levels on the path map (`VisualPathMap` in `Game.lean`).
Map labels come from `VisualLevelNumber`, so levels show as 0, 1, 2, … and the
bonus as A, while Lean numbers them from 1.

## Build and play locally

```bash
lake build                          # writes .lake/gamedata
lake env lean test/VisualMoves.lean # silent when every move works
cd ../lean4game && npm start        # then open http://localhost:3000/g/local/NNVG/visual
```

`npm start` runs the native relay, so Lean (v4.28.0, via elan) must be on the PATH.
