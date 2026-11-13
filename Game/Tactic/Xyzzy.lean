import Lean

/-!
# xyzzy

The magic word that proves Fermat's Last Theorem, as in NNG4: an axiom that the game
neither complains about nor notices.
-/

universe u

@[never_extract]
axiom xyzzyAxiom (α : Sort u) (synthetic := false) : α

/--
`xyzzy` is an ancient magic word, believed to be the root of the
modern word `sorry`. The game won't complain - or notice - if you
prove anything with `xyzzy`.
-/
macro "xyzzy" : tactic => `(tactic| exact @xyzzyAxiom _ false)
