import Game.Levels.AdvMultiplication.L01_MulLeMulRight
import Game.Levels.AdvMultiplication.L02_MulLeftNeZero
import Game.Levels.AdvMultiplication.L03_EqSuccOfNeZero
import Game.Levels.AdvMultiplication.L04_OneLeOfNeZero
import Game.Levels.AdvMultiplication.L05_LeMulRight
import Game.Levels.AdvMultiplication.L06_MulRightEqOne
import Game.Levels.AdvMultiplication.L07_MulNeZero
import Game.Levels.AdvMultiplication.L08_MulEqZero
import Game.Levels.AdvMultiplication.L09_MulRightEqSelf
import Game.Levels.AdvMultiplication.L10_MulLeftCancel

World "AdvMultiplication"
Title "Advanced Multiplication World"

VisualWorldColor indigo
VisualMapColumn 1

Introduction
"
In this world we prove how multiplication interacts with `≤` and with `≠ 0`: a factor of
a nonzero number is at most that number, a product is zero only if a factor is, and a
nonzero factor can be cancelled.
"
