import Game.Levels.LessOrEqual.L01_LeRefl
import Game.Levels.LessOrEqual.L02_ZeroLe
import Game.Levels.LessOrEqual.L03_LeSuccSelf
import Game.Levels.LessOrEqual.L04_LeTrans
import Game.Levels.LessOrEqual.L05_LeZero
import Game.Levels.LessOrEqual.L06_LeAntisymm
import Game.Levels.LessOrEqual.L07_OrSymm
import Game.Levels.LessOrEqual.L08_SuccLeSucc
import Game.Levels.LessOrEqual.L09_LeOne
import Game.Levels.LessOrEqual.L10_LeTotal

World "LessOrEqual"
Title "≤ World"

VisualWorldColor blue
VisualMapColumn 1

Introduction
"
In this world we define `a ≤ b` and prove standard facts
about it, such as \"if `a ≤ b` and `b ≤ c` then `a ≤ c`.\"

The definition of `a ≤ b` is \"there exists a number `c`
such that `b = a + c`. \" So we're going to have to learn
how to prove \"exists\" statements, and how to use \"exists\" hypotheses.
"
