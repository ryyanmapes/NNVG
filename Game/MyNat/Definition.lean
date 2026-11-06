/-!
# The natural numbers

The game's own copy of the natural numbers, `MyNat`, written `ℕ`, as in the Natural
Number Game (NNG4). Numerals like `2` are `MyNat`s, and addition is opaque, so `1 + 2`
and `3` are different expressions: a player only makes them equal by rewriting.

The successor constructor is called `S`, so that the game displays it as `S`.
-/

/-- Our copy of the natural numbers, `MyNat`, with notation `ℕ`. -/
inductive MyNat where
  | zero : MyNat
  | S : MyNat → MyNat

attribute [pp_nodot] MyNat.S

@[inherit_doc]
notation (name := MyNatNotation) (priority := 1000000) "ℕ" => MyNat

namespace MyNat

instance : Inhabited MyNat where
  default := MyNat.zero

/-- The `MyNat` with the value of a Lean `Nat`; used for numerals. -/
def ofNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero => MyNat.zero
  | Nat.succ b => MyNat.S (ofNat b)

instance instofNat {n : Nat} : OfNat MyNat n where
  ofNat := ofNat n

/-- Addition of natural numbers. Opaque, so Lean never computes `1 + 2` to `3`. -/
opaque add : MyNat → MyNat → MyNat

instance instAdd : Add MyNat where
  add := MyNat.add

/-- `add_zero n` is a proof of `n + 0 = n`. -/
axiom add_zero (n : MyNat) : n + 0 = n

/-- `add_succ a b` is a proof of `a + S b = S (a + b)`. -/
axiom add_succ (a b : MyNat) : a + S b = S (a + b)

/-- `one_eq_succ_zero` is a proof of `1 = S 0`. -/
theorem one_eq_succ_zero : (1 : MyNat) = S 0 := rfl

/-- `two_eq_succ_one` is a proof of `2 = S 1`. -/
theorem two_eq_succ_one : (2 : MyNat) = S 1 := rfl

/-- `three_eq_succ_two` is a proof of `3 = S 2`. -/
theorem three_eq_succ_two : (3 : MyNat) = S 2 := rfl

/-- `four_eq_succ_three` is a proof of `4 = S 3`. -/
theorem four_eq_succ_three : (4 : MyNat) = S 3 := rfl

end MyNat
