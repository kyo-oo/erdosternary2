import ErdosTernary2

/-!
# Core Problem 406 API

Stable public names for the final ternary digit-two theorem.  This module wraps
the checked monolith without changing proof bodies.
-/

namespace GST
namespace Problem406

/-- Boolean predicate: the ternary expansion contains a digit `2`. -/
abbrev containsDigitTwo : Nat → Bool := hasTernaryTwo

/-- Boolean predicate: the ternary expansion contains no digit `2`. -/
abbrev containsNoDigitTwo : Nat → Bool := noTernaryTwo

/-- Main public theorem: every `2^n` with `n ≥ 9` has a ternary digit `2`. -/
theorem power_of_two_contains_digit_two
    (n : Nat) (hn : 9 ≤ n) :
    containsNoDigitTwo (2^n) = false := by
  exact erdos_ternary_2_universal n hn

end Problem406
end GST
