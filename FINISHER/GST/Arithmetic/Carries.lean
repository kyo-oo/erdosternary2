import GST.Arithmetic.TernaryDigits
import GSTCanonicalCarryDynamics

/-!
# Carry API

Clean public names for exact base-three carry dynamics.
This file is a wrapper over the checked carry lemmas.
-/

namespace GST
namespace Arithmetic

/-- Exact carry at row `p` when multiplying by four. -/
abbrev carry4 : Nat → Nat → Nat := GSTCanonicalTailStateIso.carry4

/-- Every physical x4 carry is strictly below four. -/
theorem carry4_lt_four (R p : Nat) : carry4 R p < 4 := by
  exact GSTCanonicalCarryDynamics.carry4_lt_four R p

/-- Exact one-column carry-forward law. -/
theorem carry4_forward_exact (R p : Nat) :
    carry4 R (p+1) = (carry4 R p + 4 * digit3 R p) / 3 := by
  exact GSTCanonicalCarryDynamics.carry4_forward_exact R p

/-- Physical Happy-gate equivalence induced by the canonical tail cut. -/
theorem canonical_tail_happy_iff
    (b Q j : Nat) (hb : 2 ≤ b) :
    HappyCell
        (carry4 (1 + 3^b * Q) (b+j))
        (digit3 (1 + 3^b * Q) (b+j)) ↔
      HappyCell (carry4 Q j) (digit3 Q j) := by
  exact GSTCanonicalTailStateIso.canonical_tail_happy_iff b Q j hb

end Arithmetic
end GST
