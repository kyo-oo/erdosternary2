import ErdosTernary2

/-!
# Four-power reduction API

Public names for the even-exponent and adjacent-wave layer of the Problem 406
proof.
-/

namespace GST
namespace Problem406

/-- The assertion that `4^a` has ternary digit `2`. -/
abbrev FourPowerHasDigitTwo (a : Nat) : Prop := hasTernaryTwo (4^a) = true

/-- Two adjacent four-power waves overlap through the navigation alternative. -/
abbrev AdjacentFourPowerWave : Nat → Prop := GSTPowerTwoWave

/-- Complete two-wave bad trace for adjacent multiplication by four. -/
abbrev AdjacentFourPowerBadTrace : Nat → Prop := GSTTwoWaveBadTrace

/-- Exact adjacent-power identity used by the even-exponent reduction. -/
theorem adjacent_four_power_identity
    (a : Nat) (ha : 1 ≤ a) :
    4 * 4^(a-1) = 4^a := by
  exact gst_four_pow_adjacent a ha

/-- Failure of both navigation alternatives gives a complete two-wave bad trace. -/
abbrev adjacent_bad_trace_of_no_navigation :=
  gst_twoWave_badTrace_of_no_navigation

/-- Large adjacent four-power waves satisfy the navigation alternative. -/
abbrev large_adjacent_four_power_wave :=
  gst_power_two_wave_large

/-- Every `4^a` with `a ≥ 5` has ternary digit `2`. -/
theorem four_power_contains_digit_two
    (a : Nat) (ha : 5 ≤ a) :
    FourPowerHasDigitTwo a := by
  exact erdos_ternary_2_even_universal a ha

end Problem406
end GST
