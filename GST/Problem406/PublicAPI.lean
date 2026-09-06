import GST.Problem406.Core
import GST.Problem406.FourPower
import GST.Problem406.PrefixOne
import GST.Problem406.LocalCell
import GST.Problem406.Navigation

/-!
# Public API for Problem 406

Reviewer-facing namespace for the formalized ternary digit-two theorem.

This file intentionally exposes clean names while preserving the internal
monolithic proof artifact.  The old internal identifiers remain available for
compatibility, but new documentation should cite the names under
`GST.Problem406`.
-/

namespace GST
namespace Problem406

/-- Compatibility name: every exponent `n ≥ 9` gives a ternary digit `2` in `2^n`. -/
theorem contains_two_digit_of_nine_le
    (n : Nat) (hn : 9 ≤ n) :
    containsNoDigitTwo (2^n) = false := by
  exact power_of_two_contains_digit_two n hn

end Problem406
end GST
