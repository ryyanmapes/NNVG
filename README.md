# Natural Numbers Video Game

A Lean 4 game built for Visual Lean's drag-and-drop interface. It needs the
`nnvg` branch of lean4game (`../lean4game`), which adds the level-format
features it uses. The spec lives in `../../NNVG_plans`.

## Layout

- `Game/Levels/Intro`: the welcome text (a `VisualTextLevel`) before the map splits.
- `Game/Levels/Rewrite`: Rewrite World, played entirely in Rewrite Mode (`VisualRewriteOnly`).
- `Game/Levels/RewriteBonus`: bonus level A1, branching off Rewrite World level 2 (`VisualBonusOf Rewrite 3`).
- `Game/Levels/Proposition`: Proposition World up to level 6, played on the canvas.
- `Game/Levels/PropositionRight`: Proposition World from level 7 to the boss, level 13, the right branch of its fork (`VisualContinues Proposition`).
- `Game/Levels/PropositionBonus`: bonus level A1, branching off level 8.
- `Game/Levels/PropositionBonusB`: bonus levels B1 to B3, branching off the boss.
- `Game/Levels/Successor`: Successor World up to its first boss, in Rewrite Mode.
- `Game/Levels/SuccessorJoined`: Successor World past the barrier, where Proposition World's left branch joins it (`VisualContinues Successor`): Crossing the Beams and the boss.
- `Game/Levels/Induction`: Induction World, after Successor World: `zero_add` to `add_assoc`, with `∀` goals.
- `Game/Levels/Neq`: the ≠ World's levels 0 to 7, after Successor World and all of Proposition World.
- `Game/Levels/NeqJoined`: the ≠ World's level 8, which also needs Induction World (`VisualContinues Neq`).
- `Game/Levels/NeqBoss`: the ≠ World's boss, level 9, off to the side of level 8 (`VisualBonusOf NeqJoined 1`); no world needs it, but The End does. Its path to The End runs down the right of the map (`VisualMapColumn 3`).
- `Game/Levels/Multiplication`, `Power`, `PowerBonus`, `AdvAddition`, `LessOrEqual`, `AdvMultiplication`: the worlds ported from NNG4, with Visual Lean's gestures in place of the typed tactics in their text. Multiplication and Power World hang off Induction World on the far left; Advanced Addition World needs the ≠ World's level 8 and ends at its boss, `add_right_eq_zero` (`add_left_eq_zero` has no level: it is a plain theorem beside that level, unlocked by `NewTheorem` in ≤ World's first level); ≤ World leaves it to the right, and Advanced Multiplication World carries on below ≤ World, needing only that and Multiplication World, whose path comes across from the far left. Fermat's Last Theorem is a bonus boss off `add_sq`.
- `Game/Levels/Outro`: The End, the closing text level at the bottom of the map (`VisualMapBottom`), after the final bosses of Power World, Advanced Multiplication World and the ≠ World.
- `Game/MyNat/Definition.lean`: the game's own natural numbers `MyNat` (`ℕ`), as in NNG4, with the successor named `S`.
- `Game/MyNat/Fraction.lean`: the small `ℚ` that the fraction levels use.
- `Game/MyNat/Induction.lean`: `induction n with d hd`, which Visual Lean plays, without Mathlib.
- `Game/MyNat/Multiplication.lean`, `Power.lean`, `LE.lean`: `*`, `^` and `≤` as in NNG4 (two axioms each for `*` and `^`; `a ≤ b` is `∃ c, b = a + c`, kept semireducible so cards show `≤`).
- `Game/Tactic/Cases.lean`: `cases n with d`, which Visual Lean plays, without Mathlib; `Game/Tactic/Xyzzy.lean`: the magic word that proves Fermat's Last Theorem.
- `test/VisualMoves.lean`: replays the levels' solutions with Visual Lean's tactics.

Each world is a column of levels on the path map (`VisualPathMap` in `Game.lean`).
Map labels come from `VisualLevelNumber`, so levels show as 0, 1, 2, … and the
bonuses as A1, B1, …, while Lean numbers them from 1.

A Lean world is one unbroken chain of levels, so a named world that other paths join or
leave partway is split into several Lean worlds, joined with `Dependency` and
`VisualContinues`. A level's map node, title and unlocking all follow from that. It's
also why the player returns to the map at a fork: it's the end of a Lean world.

## Conventions

- `VisualPersistentHints` in `Game.lean` keeps a hint up after the state it was written for, until the next hint; write `VisualGoalInfoOnGoal … while …` for one that leaves with its goal, or a hint with empty text to clear.
- `VisualRewriteCheck` shows Rewrite Mode's check mark on goals in every level, not only Rewrite-only ones.
- `VisualSuccessorName S` names the successor in the specialization view's term builder.
- `VisualHideSwapSides` in a world file hides Rewrite Mode's swap-sides button (`a = b` to `b = a`) in all of that world's levels: Rewrite World and its bonus, Successor World and Induction World. The ≠ World has it.
- `VisualNoRewriteMode` in a level refuses Rewrite Mode on the goal with a warning, so the equality is proved like any proposition (the first ≠ World levels). Rewrite Mode on a hypothesis stays available.
- `VisualTransformSwapInfoOnHypothesis "1 = x" show "…"` is a Rewrite Mode hint with an arrow to the swap button.
- Every level shows its variables, like `A : Prop` and `x : ℕ`, as cards.
- The inventory's tabs are NNG4's (`+`, `*`, `^`, `≤`, `012`, `Peano`): file a theorem with `TheoremDoc … in "+"`. There is no Axioms tab; `VisualAxioms` in `Game.lean` lists the theorems shown in the axiom colour in Rewrite Mode.
- `VisualNoGoalRfl` in `Game.lean`: clicking a goal `a = a` doesn't close it. The player opens it in Rewrite Mode and uses the check mark.
- A world's final boss has its world in its title, as in `Plug and Chug (Successor World Boss)`. Other boss levels (`VisualBossLevel`) keep a plain title. No title has a chili pepper.
- A variable named `frac1over2` displays as a vertical fraction.
- A name ending in `_inv`, like `a_inv`, displays with `⁻¹`.
- Reference proofs use only `rw`, `exact`, `induction`, `cases` and term mode, so that `MakeGame` doesn't warn about tactics no world introduces: an `∃` goal is proved with `exact (⟨c, …⟩ : ∃ c, …)` and an `∃` or `≤` hypothesis taken apart with `match`.
- The ported worlds keep NNG4's theorem names, but `succ` is `S`, there is no `add_right_comm`, and `add_one_eq_succ : a + 1 = S a` stands in for `succ_eq_add_one`. They introduce no typed tactics (`use`, `left`, `right`, `have`, `tauto`, `exfalso`, `symm`): the visual gestures do those jobs.

## Build and play locally

```bash
lake build                          # writes .lake/gamedata
lake env lean test/VisualMoves.lean # silent when every move works
cd ../lean4game && npm start        # then open http://localhost:3000/g/local/NNVG/visual
```

`npm start` runs the native relay, so Lean (v4.28.0, via elan) must be on the PATH.
