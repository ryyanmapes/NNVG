import Game.Levels.Multiplication.L01_MulOne
import Game.Levels.Multiplication.L02_ZeroMul
import Game.Levels.Multiplication.L03_SuccMul
import Game.Levels.Multiplication.L04_MulComm
import Game.Levels.Multiplication.L05_OneMul
import Game.Levels.Multiplication.L06_TwoMul
import Game.Levels.Multiplication.L07_MulAdd
import Game.Levels.Multiplication.L08_AddMul
import Game.Levels.Multiplication.L09_MulAssoc

World "Multiplication"
Title "Multiplication World"

VisualWorldColor orange
VisualMapColumn -2

-- Rewrite Mode's swap-sides button is hidden throughout this world.
VisualHideSwapSides

Introduction
"
How should we define `37 * x`? Just like addition, we need to give definitions
when $x=0$ and when $x$ is a successor.

The zero case is easy: we define `37 * 0` to be `0`. Now say we know
`37 * d`. What should `37 * S d` be? Well, that's $(d+1)$ $37$s,
so it should be `37 * d + 37`.

Here are the definitions in Lean.

  * `mul_zero m : m * 0 = 0`
  * `mul_succ a d : a * S d = a * d + a`

In this world, we must not only prove facts about multiplication like `a * b = b * a`,
we must also prove facts about how multiplication interacts with addition, like `a * (b + c) = a * b + a * c`.
Let's get started.
"
