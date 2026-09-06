import GSTCanonicalTailStateIso

/-!
# Ternary digit API

Clean public names for the ternary digit primitives used by the Problem 406 proof.
This file contains wrappers only and does not copy proof bodies.
-/

namespace GST
namespace Arithmetic

/-- Ternary digit at position `p`. -/
abbrev digit3 : Nat → Nat → Nat := GSTCanonicalTailStateIso.digit3

/-- Physical Graph-V2 Happy gate predicate. -/
abbrev HappyCell : Nat → Nat → Prop := GSTCanonicalTailStateIso.HappyCell

/-- Existence of a physical Happy gate. -/
abbrev Navigation : Nat → Prop := GSTCanonicalTailStateIso.Navigation

/-- Exact ternary digit projection through a low prefix. -/
theorem prefix_slice_digit_exact
    (b P tail q : Nat)
    (hP : P < 3^b) :
    digit3 (P + 3^b * tail) (b+q) = digit3 tail q := by
  exact GSTCanonicalTailStateIso.prefix_slice_digit_exact b P tail q hP

/-- Canonical tail digit/carry state isomorphism. -/
theorem canonical_tail_state_isomorphism
    (b Q j : Nat) (hb : 2 ≤ b) :
    digit3 (1 + 3^b * Q) (b+j) = digit3 Q j ∧
    GSTCanonicalTailStateIso.carry4 (1 + 3^b * Q) (b+j) =
      GSTCanonicalTailStateIso.carry4 Q j := by
  exact GSTCanonicalTailStateIso.canonical_tail_state_isomorphism b Q j hb

end Arithmetic
end GST
