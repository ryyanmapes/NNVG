import Game.Metadata

/-!
Replays the moves a player makes in each Rewrite World level with Visual Lean's own
tactics, to check the levels are solvable the way the hints describe. Paths count
from the root of one side: `1` is a left operand (or a function's argument), `2` a
right operand. Run with `lake env lean test/VisualMoves.lean`.
-/

-- Level 0: substitute, then the check mark.
example (x y : ℕ) (hypothesis_1 : x = 1) (hypothesis_2 : y = 2) : x + y = 1 + 2 := by
  drag_rw_lhs_at [hypothesis_1] [1]
  drag_rw_lhs_at [hypothesis_2] [2]
  click_goal

-- Level 1: many substitutions; each rewrite only touches the chosen `0 + 0`.
example (a b c : ℕ) (zero_add_zero : (0 : ℕ) + 0 = 0)
    (hypothesis_a : a = 0) (hypothesis_b : b = 0) (hypothesis_c : c = 0) :
    0 = (a + b) + c := by
  drag_rw_rhs_at [hypothesis_a] [1, 1]
  drag_rw_rhs_at [hypothesis_b] [1, 2]
  drag_rw_rhs_at [hypothesis_c] [2]
  drag_rw_rhs_at [zero_add_zero] [1]
  drag_rw_rhs [zero_add_zero]
  click_goal

-- Level 2: backwards substitutions.
example (x y : ℕ) (zero_add_zero : (0 : ℕ) + 0 = 0)
    (hypothesis_x : 0 = x) (hypothesis_y : 0 = y) : x + y = 0 := by
  drag_rw_lhs_at [← hypothesis_x] [1]
  drag_rw_lhs_at [← hypothesis_y] [2]
  drag_rw_lhs [zero_add_zero]
  click_goal

-- Bonus A: unfold `x` into `f x` twice, then follow the chain.
example (f : ℕ → ℕ) (x a b c : ℕ) (fixed_point : f x = x) (hx : x = a)
    (fa : f a = b) (fb : f b = c) (fc : f c = 0) : f x = 0 := by
  drag_rw_lhs_at [← fixed_point] [1]
  drag_rw_lhs_at [← fixed_point] [1, 1]
  drag_rw_lhs_at [hx] [1, 1, 1]
  drag_rw_lhs_at [fa] [1, 1]
  drag_rw_lhs_at [fb] [1]
  drag_rw_lhs [fc]
  click_goal

-- Level 3: a ∀-hypothesis used at two different places.
example (a b c : ℕ) (add_comm : ∀ a b : ℕ, a + b = b + a)
    (hx : a = 1) (hy : b = 2) (hz : c = 3) : (a + b) + c = 3 + (2 + 1) := by
  drag_rw_lhs_at [hx] [1, 1]
  drag_rw_lhs_at [hy] [1, 2]
  drag_rw_lhs_at [hz] [2]
  drag_rw_lhs [add_comm]
  drag_rw_lhs_at [add_comm] [2]
  click_goal

-- Level 4: two ∀-hypotheses, in both directions.
example (a b c d : ℕ) (add_comm : ∀ a b : ℕ, a + b = b + a)
    (add_assoc : ∀ a b c : ℕ, (a + b) + c = a + (b + c))
    (hc : a + b = c) (hd : c + c = d) : ((b + b) + a) + a = d := by
  drag_rw_lhs_at [add_assoc] [1]
  drag_rw_lhs_at [add_comm] [1, 2]
  drag_rw_lhs_at [hc] [1, 2]
  drag_rw_lhs [add_comm]
  drag_rw_lhs [← add_assoc]
  drag_rw_lhs_at [hc] [1]
  drag_rw_lhs [hd]
  click_goal
