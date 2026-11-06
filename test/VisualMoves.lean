import Game.Metadata

/-!
Replays the moves a player makes in the game's levels with Visual Lean's own tactics, to
check the levels are solvable the way the hints describe. Paths count from the root of
one side: `1` is a left operand (or a function's argument), `2` a right operand. Run with
`lake env lean test/VisualMoves.lean`.
-/

/-! ## Rewrite World -/

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

-- Level 3: a ∀-hypothesis used at two different places.
example (a b c : ℕ) (add_comm : ∀ x y : ℕ, x + y = y + x)
    (hx : a = 1) (hy : b = 2) (hz : c = 3) : (a + b) + c = 3 + (2 + 1) := by
  drag_rw_lhs_at [hx] [1, 1]
  drag_rw_lhs_at [hy] [1, 2]
  drag_rw_lhs_at [hz] [2]
  drag_rw_lhs [add_comm]
  drag_rw_lhs_at [add_comm] [2]
  click_goal

-- Level 4: fractions; associate, then add up the fourths and the halves.
example (frac1over2 frac1over4 : ℚ)
    (add_assoc : ∀ x y z : ℚ, (x + y) + z = x + (y + z))
    (h_fourths : frac1over2 = frac1over4 + frac1over4)
    (h_halves : (1 : ℚ) = frac1over2 + frac1over2) :
    (frac1over2 + frac1over4) + frac1over4 = 1 := by
  drag_rw_lhs [add_assoc]
  drag_rw_lhs_at [← h_fourths] [2]
  drag_rw_lhs [← h_halves]
  click_goal

-- Level 5, the boss.
example (add_comm : ∀ x y : ℕ, x + y = y + x)
    (add_assoc : ∀ x y z : ℕ, (x + y) + z = x + (y + z))
    (h_two : (1 : ℕ) + 1 = 2) (h_three : (1 : ℕ) + 2 = 3) :
    (1 : ℕ) + 1 + 1 + 1 + 1 + 1 = 1 + 2 + 3 := by
  drag_rw_lhs_at [h_two] [1, 1, 1, 1]
  drag_rw_lhs_at [add_comm] [1, 1, 1]
  drag_rw_lhs_at [h_three] [1, 1, 1]
  drag_rw_rhs_at [h_three] [1]
  drag_rw_lhs_at [add_assoc] [1]
  drag_rw_lhs_at [h_two] [1, 2]
  drag_rw_lhs [add_assoc]
  drag_rw_lhs_at [add_comm] [2]
  drag_rw_lhs_at [h_three] [2]
  click_goal

/-! ## Rewrite World bonus levels -/

-- A1: unfold `x` into `f x` twice, then follow the chain.
example (f : ℕ → ℕ) (x a b c : ℕ) (fixed_point : f x = x) (hx : x = a)
    (fa : f a = b) (fb : f b = c) (fc : f c = 0) : f x = 0 := by
  drag_rw_lhs_at [← fixed_point] [1]
  drag_rw_lhs_at [← fixed_point] [1, 1]
  drag_rw_lhs_at [hx] [1, 1, 1]
  drag_rw_lhs_at [fa] [1, 1]
  drag_rw_lhs_at [fb] [1]
  drag_rw_lhs [fc]
  click_goal

-- A2: absorb the factors one at a time into `x`, innermost first.
example (x a a_inv : ℚ)
    (generate_a : x = x * a) (generate_a_inv : x = x * a_inv)
    (_elim_a : (1 * a) * a_inv = (1 : ℚ)) (_elim_a_inv : (1 * a_inv) * a = (1 : ℚ))
    (hx : x = 1) :
    x * a * a_inv * a * a * a_inv = 1 := by
  drag_rw_lhs_at [← generate_a] [1, 1, 1, 1]
  drag_rw_lhs_at [← generate_a_inv] [1, 1, 1]
  drag_rw_lhs_at [← generate_a] [1, 1]
  drag_rw_lhs_at [← generate_a] [1]
  drag_rw_lhs [← generate_a_inv]
  drag_rw_lhs [hx]
  click_goal

-- A2 again, going through `1` with the `elim` hypotheses instead.
example (x a a_inv : ℚ)
    (generate_a : x = x * a) (_generate_a_inv : x = x * a_inv)
    (elim_a : (1 * a) * a_inv = (1 : ℚ)) (_elim_a_inv : (1 * a_inv) * a = (1 : ℚ))
    (hx : x = 1) :
    x * a * a_inv * a * a * a_inv = 1 := by
  drag_rw_lhs_at [hx] [1, 1, 1, 1, 1]
  drag_rw_lhs_at [elim_a] [1, 1, 1]
  drag_rw_lhs_at [← hx] [1, 1, 1]
  drag_rw_lhs_at [← generate_a] [1, 1]
  drag_rw_lhs_at [hx] [1, 1]
  drag_rw_lhs [elim_a]
  click_goal

/-! ## Proposition World: the levels past the fork -/

-- Level 6: choose the right side, then split the `∨` hypothesis before the `∨` goal.
example (Z A B : Prop) : Z ∨ ((A ∨ B) → (B ∨ A)) := by
  click_goal_right
  intro h
  click_prop h
  · click_goal_right
    drag_goal left
  · click_goal_left
    drag_goal right

-- Level 7: a proof of `False` proves anything.
example (h : False) : (1 : ℕ) = 2 := by
  drag_goal_exfalso h

/-! ## Induction World -/

namespace MyNat

-- Level 1: fold the successors back into numerals.
example : S (S 0) = 2 := by
  drag_rw_lhs_at [← one_eq_succ_zero] [1]
  drag_rw_lhs [← two_eq_succ_one]
  click_goal

-- Level 2: a theorem, proved with the axioms.
example (a : ℕ) : a + 1 = S a := by
  drag_rw_lhs_at [one_eq_succ_zero] [2]
  drag_rw_lhs [add_succ]
  drag_rw_lhs_at [add_zero] [1]
  click_goal

-- Level 3, the boss: level 2's theorem saves time.
theorem add_one_eq_succ' (a : ℕ) : a + 1 = S a := by
  rw [one_eq_succ_zero, add_succ, add_zero]

example : (1 : ℕ) + 1 + 1 + 1 = 4 := by
  drag_rw_lhs [add_one_eq_succ']
  drag_rw_lhs_at [add_one_eq_succ'] [1]
  drag_rw_lhs_at [add_one_eq_succ'] [1, 1]
  drag_rw_rhs [four_eq_succ_three]
  drag_rw_rhs_at [three_eq_succ_two] [1]
  drag_rw_rhs_at [two_eq_succ_one] [1, 1]
  click_goal

-- Level 4: `zero_add`, by induction.
example (n : ℕ) : 0 + n = n := by
  induction n with d hd
  · drag_rw_lhs [add_zero]
    click_goal
  · drag_rw_lhs [add_succ]
    drag_rw_lhs_at [hd] [1]
    click_goal

-- A1: `2 + 2 = 4`, ported from NNG.
example : (2 : ℕ) + 2 = 4 := by
  drag_rw_lhs_at [two_eq_succ_one] [2]
  drag_rw_lhs [add_succ]
  drag_rw_lhs_at [one_eq_succ_zero] [1, 2]
  drag_rw_lhs_at [add_succ] [1]
  drag_rw_lhs_at [add_zero] [1, 1]
  drag_rw_lhs_at [← three_eq_succ_two] [1]
  drag_rw_lhs [← four_eq_succ_three]
  click_goal

end MyNat
