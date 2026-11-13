import Game.Levels.Successor

World "SuccessorJoined"
Level 1

Title "Crossing the Beams"

VisualLevelNumber "4"

namespace MyNat

-- The first level to use Rewriting Mode and Proposition Mode together: rewrite `hx`
-- into `x = 1`, go back, then rewrite the goal and close it with the check mark.
Statement (x : ℕ) (hx : x = S 0) : S x = 2 := by
  rw [← one_eq_succ_zero] at hx
  rw [hx, two_eq_succ_one]

VisualHypInfoOnHyp hx "x = S(0)" show
  "We will now put Rewriting Mode and Proposition Mode together!
Try {pc: double-clicking | mobile: double-tapping} `hx` to open it in Rewriting Mode."

VisualTransformInfoOnHypothesis "x = S(0)" show
  "Let's try rewriting this equation into `x = 1`."

VisualTransformBackInfoOnHypothesis "x = 1" show
  "We can return back to Proposition Mode by {pc: clicking | mobile: tapping} ‘Back’."

VisualGoalInfoOnGoalWithHyp above true "S(x) = 2" "x = 1" show
  "Now we can make the substitution into the goal to complete the proof.
{pc: Double-click | mobile: Double-tap} the goal to enter it in Rewriting Mode."

VisualTransformInfoOnGoal "S(x) = 2" show
  "We can finish the proof here as usual.
Notice you can use `hx` as a substitution."
