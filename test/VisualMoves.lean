import Game.Metadata
-- The closing level imports every world, so the ported worlds' theorems are in scope.
import Game.Levels.Outro

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
example (x y z : ℕ) (hypothesis_x : x = 0) (hypothesis_y : y = 0) (hypothesis_z : z = 0)
    (zero_add_zero : (0 : ℕ) + 0 = 0) :
    (x + y) + z = 0 := by
  drag_rw_lhs_at [hypothesis_x] [1, 1]
  drag_rw_lhs_at [hypothesis_y] [1, 2]
  drag_rw_lhs_at [hypothesis_z] [2]
  drag_rw_lhs_at [zero_add_zero] [1]
  drag_rw_lhs [zero_add_zero]
  click_goal

-- Level 2: backwards substitutions.
example (x y : ℕ) (hypothesis_x : 0 = x) (hypothesis_y : 0 = y)
    (zero_add_zero : (0 : ℕ) + 0 = 0) : x + y = 0 := by
  drag_rw_lhs_at [← hypothesis_x] [1]
  drag_rw_lhs_at [← hypothesis_y] [2]
  drag_rw_lhs [zero_add_zero]
  click_goal

-- Level 3: a ∀-hypothesis used at two different places.
example (a b c : ℕ) (hx : a = 1) (hy : b = 2) (hz : c = 3)
    (add_comm : ∀ x y : ℕ, x + y = y + x) : (a + b) + c = 3 + (2 + 1) := by
  drag_rw_lhs_at [hx] [1, 1]
  drag_rw_lhs_at [hy] [1, 2]
  drag_rw_lhs_at [hz] [2]
  drag_rw_lhs [add_comm]
  drag_rw_lhs_at [add_comm] [2]
  click_goal

-- Level 4: fractions; associate, then add up the fourths and the halves.
example (frac1over2 frac1over4 : ℚ)
    (h_fourths : frac1over2 = frac1over4 + frac1over4)
    (h_halves : (1 : ℚ) = frac1over2 + frac1over2)
    (add_assoc : ∀ x y z : ℚ, (x + y) + z = x + (y + z)) :
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

/-! ## Proposition World -/

-- Level 4: drag `(A → B) → C` onto the goal `C` to prove it backwards.
example (A B C : Prop) : B → ((A → B) → C) → C := by
  intro hB
  intro hABC
  drag_goal hABC
  intro _
  drag_goal hB

/-! ## Proposition World: the levels past the fork -/

-- Level 7: the `↔` goal separates into its two directions with a click.
example (A B C : Prop) : ((A ∧ B) ∧ C) ↔ (A ∧ (B ∧ C)) := by
  click_goal
  · intro h
    click_prop h
    click_prop left
    click_goal
    · drag_goal left1
    · click_goal
      · drag_goal right1
      · drag_goal right
  · intro h
    click_prop h
    click_prop right
    click_goal
    · click_goal
      · drag_goal left
      · drag_goal left1
    · drag_goal right1

-- Level 8: choose the right side, then split the `∨` hypothesis before the `∨` goal.
example (Z A B : Prop) : Z ∨ ((A ∨ B) → (B ∨ A)) := by
  click_goal_right
  intro h
  click_prop h
  · click_goal_right
    drag_goal left
  · click_goal_left
    drag_goal right

-- Level 9: both directions, splitting each `∨` hypothesis before choosing a side.
example (A B C : Prop) : ((A ∨ B) ∨ C) ↔ (A ∨ (B ∨ C)) := by
  click_goal
  · intro h
    click_prop h
    · click_prop left
      · click_goal_left
        drag_goal left1
      · click_goal_right
        click_goal_left
        drag_goal right
    · click_goal_right
      click_goal_right
      drag_goal right
  · intro h
    click_prop h
    · click_goal_left
      click_goal_left
      drag_goal left
    · click_prop right
      · click_goal_left
        click_goal_right
        drag_goal left
      · click_goal_right
        drag_goal right1

-- Level 10: a proof of `False` proves anything.
example (h : False) : (1 : ℕ) = 2 := by
  drag_goal_exfalso h

-- Level 11: `¬` goals introduce like implications, and `¬` cards apply like them.
example (A : Prop) : A → ¬¬A := by
  click_goal
  click_goal
  drag_to h h1
  drag_goal h2

-- Level 11 again, proving the `False` goal backwards.
example (A : Prop) : A → ¬¬A := by
  click_goal
  click_goal
  drag_goal h1
  drag_goal h

-- Level 12: split the `∧`, then apply `¬A` to `A`.
example (A : Prop) : ¬(A ∧ ¬A) := by
  click_goal
  click_prop h
  drag_to left right
  drag_goal h

-- Level 13, the boss.
example (A B : Prop) : ¬(A ∨ B) ↔ (¬A ∧ ¬B) := by
  click_goal
  · click_goal
    click_goal
    · click_goal
      drag_goal h
      click_goal_left
      drag_goal h1
    · click_goal
      drag_goal h
      click_goal_right
      drag_goal h1
  · click_goal
    click_prop h
    click_goal
    click_prop h
    · drag_to left1 left
      drag_goal h
    · drag_to right1 right
      drag_goal h

/-! ## Proposition World bonus levels -/

-- A1: split both hypotheses, and in each case either prove the left side or show `C`.
example (A B C : Prop) :
    (A ∨ (B → C)) → ((B ∨ (A → C)) → ((A ∧ B) ∨ ((A ∨ B) → C))) := by
  intro h1
  intro h2
  click_prop h1
  · click_prop h2
    · click_goal_left
      click_goal
      · drag_goal left
      · drag_goal left1
    · click_goal_right
      intro _
      drag_goal right
      drag_goal left
  · click_prop h2
    · click_goal_right
      intro _
      drag_goal right
      drag_goal left
    · click_goal_right
      intro h3
      click_prop h3
      · drag_goal right1
        drag_goal left
      · drag_goal right
        drag_goal right2

-- B1: the valid direction of the other law.
example (A B : Prop) : (¬A ∨ ¬B) → ¬(A ∧ B) := by
  click_goal
  click_goal
  click_prop h1
  click_prop h
  · drag_to left left1
    drag_goal h
  · drag_to right1 right
    drag_goal h

-- B2: with the Law of Excluded Middle for both.
example (A B : Prop) (hA : A ∨ ¬A) (hB : B ∨ ¬B) : ¬(A ∧ B) → (¬A ∨ ¬B) := by
  click_goal
  click_prop hA
  · click_prop hB
    · click_goal_left
      click_goal
      drag_goal h
      click_goal
      · drag_goal left
      · drag_goal left1
    · click_goal_right
      drag_goal right
  · click_goal_left
    drag_goal right

-- B3: with the Weak Law of Excluded Middle, the `False` goal needs both `¬¬` hypotheses.
example (A B : Prop) (hA : ¬A ∨ ¬¬A) (hB : ¬B ∨ ¬¬B) : ¬(A ∧ B) → (¬A ∨ ¬B) := by
  click_goal
  click_prop hA
  · click_goal_left
    drag_goal left
  · click_prop hB
    · click_goal_right
      drag_goal left
    · click_goal_left
      click_goal
      drag_goal right1
      click_goal
      drag_goal h
      click_goal
      · drag_goal h1
      · drag_goal h2

/-! ## Successor World -/

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

-- Level 4, Crossing the Beams: rewrite `hx` into `x = 1` in Rewriting Mode, go back,
-- then rewrite the goal and close it with the check mark.
example (x : ℕ) (hx : x = S 0) : S x = 2 := by
  drag_rw_hyp_rhs hx [← one_eq_succ_zero]
  drag_rw_lhs_at [hx] [1]
  drag_rw_rhs [two_eq_succ_one]
  click_goal

-- Level 5, the boss: tidy up the hypotheses, then the goal.
example (a b c : ℕ) (ha : a = 0 + 1) (hb : S (0 + 0) = b) (hc : c = (a + 0) + (0 + b)) :
    c + c = 4 := by
  drag_rw_hyp_rhs_at ha [one_eq_succ_zero] [2]
  drag_rw_hyp_rhs ha [add_succ]
  drag_rw_hyp_rhs_at ha [add_zero] [1]
  drag_rw_hyp_rhs ha [← one_eq_succ_zero]
  drag_rw_hyp_lhs_at hb [add_zero] [1]
  drag_rw_hyp_lhs hb [← one_eq_succ_zero]
  drag_rw_hyp_rhs_at hc [add_zero] [1]
  drag_rw_hyp_rhs_at hc [ha] [1]
  drag_rw_hyp_rhs_at hc [← hb] [2, 2]
  drag_rw_hyp_rhs_at hc [one_eq_succ_zero] [2, 2]
  drag_rw_hyp_rhs_at hc [add_succ] [2]
  drag_rw_hyp_rhs_at hc [add_zero] [2, 1]
  drag_rw_hyp_rhs hc [add_succ]
  drag_rw_hyp_rhs_at hc [add_zero] [1]
  drag_rw_hyp_rhs hc [← two_eq_succ_one]
  drag_rw_lhs_at [hc] [1]
  drag_rw_lhs_at [hc] [2]
  drag_rw_lhs_at [two_eq_succ_one] [2]
  drag_rw_lhs [add_succ]
  drag_rw_lhs_at [one_eq_succ_zero] [1, 2]
  drag_rw_lhs_at [add_succ] [1]
  drag_rw_lhs_at [add_zero] [1, 1]
  drag_rw_lhs_at [← three_eq_succ_two] [1]
  drag_rw_lhs [← four_eq_succ_three]
  click_goal

/-! ## Induction World -/

-- Level 1, `zero_add`: click the goal to fix `n`, then induct on it.
example : ∀ n : ℕ, 0 + n = n := by
  click_goal
  induction n with d hd
  · drag_rw_lhs [add_zero]
    click_goal
  · drag_rw_lhs [add_succ]
    drag_rw_lhs_at [hd] [1]
    click_goal

theorem zero_add' : ∀ n : ℕ, 0 + n = n := by
  intro n
  induction n with d hd
  · rw [add_zero]
  · rw [add_succ, hd]

-- Level 2, `succ_add`.
example : ∀ a b : ℕ, S a + b = S (a + b) := by
  click_goal
  click_goal
  induction b with d hd
  · drag_rw_lhs [add_zero]
    drag_rw_rhs_at [add_zero] [1]
    click_goal
  · drag_rw_lhs [add_succ]
    drag_rw_rhs_at [add_succ] [1]
    drag_rw_lhs_at [hd] [1]
    click_goal

theorem succ_add' : ∀ a b : ℕ, S a + b = S (a + b) := by
  intro a b
  induction b with d hd
  · rw [add_zero, add_zero]
  · rw [add_succ, add_succ, hd]

-- Level 3, commutativity.
example : ∀ a b : ℕ, a + b = b + a := by
  click_goal
  click_goal
  induction b with d hd
  · drag_rw_lhs [add_zero]
    drag_rw_rhs [zero_add']
    click_goal
  · drag_rw_lhs [add_succ]
    drag_rw_rhs [succ_add']
    drag_rw_lhs_at [hd] [1]
    click_goal

-- Level 4, associativity.
example : ∀ a b c : ℕ, a + b + c = a + (b + c) := by
  click_goal
  click_goal
  click_goal
  induction c with d hd
  · drag_rw_lhs [add_zero]
    drag_rw_rhs_at [add_zero] [2]
    click_goal
  · drag_rw_lhs [add_succ]
    drag_rw_rhs_at [add_succ] [2]
    drag_rw_rhs [add_succ]
    drag_rw_lhs_at [hd] [1]
    click_goal

/-! ## ≠ World -/

-- Level 0: an equality hypothesis proves the matching goal by dragging; Rewriting Mode
-- on the goal is off.
example (x : ℕ) : x = 1 → x = 1 := by
  click_goal
  drag_goal h

-- Level 1: swap `1 = x` round in Rewriting Mode, feed it to the implication, swap the
-- result round the same way, and drag it to the goal.
example (x y : ℕ) : 1 = x → ((x = 1 → y = 2) → 2 = y) := by
  click_goal
  click_goal
  symm at h
  drag_to h h1
  symm at h2
  drag_goal h2

-- Level 2: an equality hypothesis proves the matching goal by dragging.
example (x : ℕ) : x = 1 → (x = 1 ∧ (S x = 2 ∨ (1 : ℕ) = 0)) := by
  click_goal
  click_goal
  · drag_goal h
  · click_goal_left
    drag_rw_lhs_at [h] [1]
    drag_rw_rhs [two_eq_succ_one]
    click_goal

-- Level 3: specialize `reflection` by hand for the first goal, then drag it onto the
-- others, which specializes it automatically.
example : S 0 = S 0 ∧ ((1 : ℕ) = 1 ∧ (2 : ℕ) = 2) := by
  click_goal
  · specialize_forall_as thm_h reflection n (S 0)
    drag_goal thm_h
  · click_goal
    · drag_goal reflection
    · drag_goal reflection

-- Level 4, `succ_inj`: rewrite `h` into `S x = S 3`, then drag it onto `succ_inj`.
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  drag_rw_hyp_rhs h [four_eq_succ_three]
  drag_rw_hyp_lhs h [add_one_eq_succ']
  drag_apply succ_inj h
  drag_goal thm_succ_inj

-- Level 5: `x ≠ y` applies to `x = y` like an implication.
example (x y : ℕ) : (S x = S y ∧ x ≠ y) → False := by
  click_goal
  click_prop h
  drag_apply succ_inj left
  drag_to thm_succ_inj right
  drag_goal thm_succ_inj

-- Level 6, `zero_ne_one`.
example : (0 : ℕ) ≠ 1 := by
  click_goal
  drag_rw_hyp_rhs h [one_eq_succ_zero]
  drag_apply zero_ne_succ h
  drag_goal thm_zero_ne_succ

-- Level 7: `2 ≠ 4`, peeling off successors with `succ_inj`.
example : (2 : ℕ) ≠ 4 := by
  click_goal
  drag_rw_hyp_lhs h [two_eq_succ_one]
  drag_rw_hyp_rhs h [four_eq_succ_three]
  drag_apply succ_inj h
  drag_rw_hyp_lhs thm_succ_inj [one_eq_succ_zero]
  drag_rw_hyp_rhs thm_succ_inj [three_eq_succ_two]
  drag_apply succ_inj thm_succ_inj
  drag_rw_hyp_rhs thm_succ_inj1 [two_eq_succ_one]
  drag_apply zero_ne_succ thm_succ_inj1
  drag_goal thm_zero_ne_succ

-- Level 8, Zero or No Zero: by induction.
example : ∀ n : ℕ, n = 0 ∨ n ≠ 0 := by
  click_goal
  induction n with d hd
  · click_goal_left
    click_goal
  · click_goal_right
    click_goal
    specialize_forall_as thm_z zero_ne_succ a d
    drag_rw_hyp_lhs thm_z [← h]
    specialize_forall_as thm_r reflection n (S d)
    drag_to thm_r thm_z
    drag_goal thm_z1

-- Level 9, the boss: induction on `a`, and inside each case, induction on `b`.
example : ∀ a b : ℕ, a = b ∨ a ≠ b := by
  click_goal
  induction a with d hd
  · click_goal
    induction b with e he
    · click_goal_left
      click_goal
    · click_goal_right
      drag_goal zero_ne_succ
  · click_goal
    induction b with e he
    · click_goal_right
      click_goal
      specialize_forall_as thm_z zero_ne_succ a d
      drag_rw_hyp_lhs thm_z [← h]
      specialize_forall_as thm_r reflection n (S d)
      drag_to thm_r thm_z
      drag_goal thm_z1
    · specialize_forall_as thm_e hd b e
      click_prop thm_e
      · click_goal_left
        drag_rw_lhs_at [thm_left] [1]
        click_goal
      · click_goal_right
        click_goal
        drag_apply succ_inj h
        drag_to thm_succ_inj thm_right
        drag_goal thm_right1

/-! ## Multiplication World -/

-- Level 1: `1` is a successor, so the two axioms apply.
example (m : ℕ) : m * 1 = m := by
  drag_rw_lhs_at [one_eq_succ_zero] [2]
  drag_rw_lhs [mul_succ]
  drag_rw_lhs_at [mul_zero] [1]
  drag_rw_lhs [zero_add]
  click_goal

-- Level 9, the boss: induction on `c`.
example (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction c with d hd
  · drag_rw_lhs [mul_zero]
    drag_rw_rhs_at [mul_zero] [2]
    drag_rw_rhs [mul_zero]
    click_goal
  · drag_rw_lhs [mul_succ]
    drag_rw_rhs_at [mul_succ] [2]
    drag_rw_rhs [mul_add]
    drag_rw_lhs_at [hd] [1]
    click_goal

/-! ## Power World -/

-- Level 5: `2` is `S 1`, then the axiom and `pow_one`.
example (a : ℕ) : a ^ 2 = a * a := by
  drag_rw_lhs_at [two_eq_succ_one] [2]
  drag_rw_lhs [pow_succ]
  drag_rw_lhs_at [pow_one] [1]
  click_goal

/-! ## Advanced Addition World -/

-- Level 5: split `b` with the cases card; the successor case has `h : S (a + d) = 0`,
-- which swaps round (the swap button) to meet `zero_ne_succ`.
example (a b : ℕ) : a + b = 0 → a = 0 := by
  cases b with d
  · click_goal
    drag_rw_hyp_lhs h [add_zero]
    drag_goal h
  · click_goal
    drag_rw_hyp_lhs h [add_succ]
    symm at h
    specialize_forall_as thm zero_ne_succ a (a + d)
    drag_to h thm
    drag_goal_exfalso h1

/-! ## ≤ World -/

-- Level 1: build the `0` in the construction view, then rewrite.
example (x : ℕ) : x ≤ x := by
  refine Exists.intro (0) ?_
  drag_rw_rhs [add_zero]
  click_goal

-- Level 4: clicking a `≤` hypothesis names its number and its equation.
example (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  click_prop hxy
  click_prop hyz
  refine Exists.intro (c + c1) ?_
  drag_rw_lhs [h1]
  drag_rw_lhs_at [h] [1]
  drag_rw_lhs [add_assoc]
  click_goal

/-! ## Advanced Multiplication World -/

-- Level 3: in the zero case, clicking `ha : 0 ≠ 0` proves `False`.
example (a : ℕ) (ha : a ≠ 0) : ∃ n, a = S n := by
  cases a with d
  · click_prop ha
    drag_goal_exfalso ha
  · refine Exists.intro (d) ?_
    click_goal

end MyNat
