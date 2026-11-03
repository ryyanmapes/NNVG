import GameServer
import Game.MyNat.Definition

/-- `rw [h]` rewrites the goal with the equality `h`, replacing its left side by its
right side. `rw [← h]` rewrites from right to left. -/
TacticDoc rw

/-- `exact h` closes the goal with `h`, whose type must be exactly the goal. -/
TacticDoc exact
