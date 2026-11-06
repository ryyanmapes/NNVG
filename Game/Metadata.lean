import GameServer
import Game.MyNat.Definition
import Game.MyNat.Fraction
import Game.MyNat.Induction

/-- `rw [h]` rewrites the goal with the equality `h`, replacing its left side by its
right side. `rw [← h]` rewrites from right to left. -/
TacticDoc rw

/-- `exact h` closes the goal with `h`, whose type must be exactly the goal. -/
TacticDoc exact

/-- `induction n with d hd` attempts to prove the goal by induction on `n`, with the
inductive variable in the successor case being `d`, and the inductive hypothesis
being `hd`.

If the goal is `0 + n = n`, it turns into two goals. The first is `0 + 0 = 0`; the second
has an assumption `hd : 0 + d = d` and goal `0 + S d = S d`. -/
TacticDoc induction
