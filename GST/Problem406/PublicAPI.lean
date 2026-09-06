import ErdosTernary2

/-!
# Public API for Problem 406

This file gives stable, readable names for the comparator-passing theorem.
It does not alter the monolith proof. The original proof artifact remains
`ErdosTernary2.lean`; this file only re-exports its main result under a clean
review-facing namespace.
-/

namespace GST
namespace Problem406

/-- For every exponent `n ≥ 9`, the ternary expansion of `2^n` contains digit `2`. -/
theorem contains_two_digit_of_nine_le
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false := by
  exact erdos_ternary_2_universal n hn

end Problem406
end GST
