/-!
# The natural numbers

The game's own copy of the natural numbers, `MyNat`, written `ℕ`, as in the Natural
Number Game (NNG4). Numerals like `2` are `MyNat`s, and addition is opaque, so `1 + 2`
and `3` are different expressions: a player only makes them equal by rewriting.
-/

/-- Our copy of the natural numbers, `MyNat`, with notation `ℕ`. -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

attribute [pp_nodot] MyNat.succ

@[inherit_doc]
notation (name := MyNatNotation) (priority := 1000000) "ℕ" => MyNat

namespace MyNat

instance : Inhabited MyNat where
  default := MyNat.zero

/-- The `MyNat` with the value of a Lean `Nat`; used for numerals. -/
def ofNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero => MyNat.zero
  | Nat.succ b => MyNat.succ (ofNat b)

instance instofNat {n : Nat} : OfNat MyNat n where
  ofNat := ofNat n

/-- Addition of natural numbers. Opaque, so Lean never computes `1 + 2` to `3`. -/
opaque add : MyNat → MyNat → MyNat

instance instAdd : Add MyNat where
  add := MyNat.add

end MyNat
