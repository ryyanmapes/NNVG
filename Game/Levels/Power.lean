import Game.Levels.Power.L01_ZeroPowZero
import Game.Levels.Power.L02_ZeroPowSucc
import Game.Levels.Power.L03_PowOne
import Game.Levels.Power.L04_OnePow
import Game.Levels.Power.L05_PowTwo
import Game.Levels.Power.L06_PowAdd
import Game.Levels.Power.L07_MulPow
import Game.Levels.Power.L08_PowPow
import Game.Levels.Power.L09_AddSq

World "Power"
Title "Power World"

VisualWorldColor red
VisualMapColumn -2

-- Rewrite Mode's swap-sides button is hidden throughout this world.
VisualHideSwapSides

Introduction
"
In this world we define powers, `a ^ b`, by two more axioms: `pow_zero a : a ^ 0 = 1`
and `pow_succ a b : a ^ S b = a ^ b * a`. Everything else about powers follows from
these, by induction. The boss of this world is `add_sq`, the formula for $(a + b)^2$.
"
