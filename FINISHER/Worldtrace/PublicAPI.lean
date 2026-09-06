import GST.PublicAPI

/-!
# Worldtrace Arithmetic public API

`Worldtrace Arithmetic` is the public umbrella for the proof stack in this
repository.  The historical Lean namespace `GST` remains available for
compatibility, but reviewer-facing entrypoints should prefer this module when
speaking about the whole mathematics rather than only the General Space Theory
pillar.

The facade is intentionally thin: it does not rename the proof corpus or change
proof bodies.  It exposes stable names over the existing checked API.
-/

namespace Worldtrace

/-- Boolean predicate: the ternary expansion contains a digit `2`. -/
abbrev containsDigitTwo : Nat → Bool := GST.Problem406.containsDigitTwo

/-- Boolean predicate: the ternary expansion contains no digit `2`. -/
abbrev containsNoDigitTwo : Nat → Bool := GST.Problem406.containsNoDigitTwo

/-- The assertion that `4^a` has ternary digit `2`. -/
abbrev FourPowerHasDigitTwo : Nat → Prop := GST.Problem406.FourPowerHasDigitTwo

/-- The full adjacent-four-power wave assertion. -/
abbrev AdjacentFourPowerWave : Nat → Prop := GST.Problem406.AdjacentFourPowerWave

/-- The complete adjacent-four-power bad-trace assertion. -/
abbrev AdjacentFourPowerBadTrace : Nat → Prop := GST.Problem406.AdjacentFourPowerBadTrace

/-- Navigation witness used by the proof stack. -/
abbrev NavigationWitness : Nat → Prop := GST.Problem406.NavigationWitness

/-- Main theorem: every `2^n` with `n ≥ 9` has a ternary digit `2`. -/
theorem erdos_ternary_two
    (n : Nat) (hn : 9 ≤ n) :
    containsNoDigitTwo (2^n) = false := by
  exact GST.Problem406.power_of_two_contains_digit_two n hn

/-- Even-exponent theorem: every `4^a` with `a ≥ 5` has a ternary digit `2`. -/
theorem four_power_contains_digit_two
    (a : Nat) (ha : 5 ≤ a) :
    FourPowerHasDigitTwo a := by
  exact GST.Problem406.four_power_contains_digit_two a ha

/-- Exact adjacent-power identity used by the even-exponent reduction. -/
theorem adjacent_four_power_identity
    (a : Nat) (ha : 1 ≤ a) :
    4 * 4^(a-1) = 4^a := by
  exact GST.Problem406.adjacent_four_power_identity a ha

/-- Failure of both navigation alternatives gives a complete two-wave bad trace. -/
theorem adjacent_bad_trace_of_no_navigation :=
  GST.Problem406.adjacent_bad_trace_of_no_navigation

/-- Large adjacent four-power waves satisfy the navigation alternative. -/
theorem large_adjacent_four_power_wave :=
  GST.Problem406.large_adjacent_four_power_wave

/-- Certified prefix-one navigation lift. -/
theorem prefix_one_navigation_lift :=
  GST.Problem406.prefix_one_navigation_lift

/-- Four-power creation master certified by the proof corpus. -/
theorem four_power_creation_master :=
  GST.Problem406.four_power_creation_master

/-- Event-word form of the positive local chord. -/
theorem physical_two_digit_chord_event_word :=
  GST.Problem406.physical_two_digit_chord_event_word

/-- Complete two-branch local dichotomy for a Happy digit-two cell. -/
theorem happy_digit_two_right_chord_dichotomy :=
  GST.Problem406.happy_digit_two_right_chord_dichotomy

/-- Canonical standalone navigation gives the navigation witness. -/
theorem navigation_witness_of_canonical_navigation :=
  GST.Problem406.navigation_witness_of_canonical_navigation

end Worldtrace
