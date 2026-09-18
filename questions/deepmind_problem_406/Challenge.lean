import Mathlib

/-!
# DeepMind Formal Conjectures — Erdős Problem 406

Challenge-side statement corresponding to
`google-deepmind/formal-conjectures/FormalConjectures/ErdosProblems/406.lean`:
there are only finitely many powers of two whose base-three digits all lie in
`{0, 1}`.

The `sorry` is intentional on the challenge side.  The submitted solution
must prove the same theorem with no additional hypothesis.
-/

namespace Erdos406

theorem erdos_406 :
    {n : Nat | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  sorry

end Erdos406
