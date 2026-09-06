import Worldtrace.Genesis
import Worldtrace.Ternary
import Worldtrace.Carry
import Worldtrace.Residue
import Worldtrace.FourPower
import Worldtrace.Navigation
import Worldtrace.Collision
import Worldtrace.Phase
import Worldtrace.Certificate

/-!
# Worldtrace Arithmetic public API

`Worldtrace Arithmetic` is the public umbrella for the proof stack in this
repository.  It is not a rename of General Space Theory: GST remains the
navigation-geometric pillar and a compatibility namespace, while Worldtrace is
the full framework spanning genesis arithmetic, ternary events, carry
information, residue towers, four-power dynamics, navigation, collision closure,
phase cycles, and finite certificates.

This facade is intentionally thin.  It does not rename the proof corpus or alter
proof bodies; it exposes stable public names over the checked Lean artifact.
-/

namespace Worldtrace

/-- Boolean predicate: the ternary expansion contains a digit `2`. -/
abbrev containsDigitTwo : Nat → Bool := Ternary.containsDigitTwo

/-- Boolean predicate: the ternary expansion contains no digit `2`. -/
abbrev containsNoDigitTwo : Nat → Bool := Ternary.containsNoDigitTwo

/-- The assertion that `4^a` has ternary digit `2`. -/
abbrev FourPowerHasDigitTwo : Nat → Prop := FourPower.hasDigitTwo

/-- The full adjacent-four-power wave assertion. -/
abbrev AdjacentFourPowerWave : Nat → Prop := FourPower.AdjacentWave

/-- The complete adjacent-four-power bad-trace assertion. -/
abbrev AdjacentFourPowerBadTrace : Nat → Prop := FourPower.AdjacentBadTrace

/-- Navigation witness used by the proof stack. -/
abbrev NavigationWitness : Nat → Prop := Navigation.Witness

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
theorem adjacent_bad_trace_of_no_navigation := FourPower.adjacent_bad_trace_of_no_navigation

/-- Large adjacent four-power waves satisfy the navigation alternative. -/
theorem large_adjacent_four_power_wave := FourPower.large_adjacent_wave

/-- Certified prefix-one navigation lift. -/
theorem prefix_one_navigation_lift := Certificate.prefix_one_navigation_lift

/-- Four-power creation master certified by the proof corpus. -/
theorem four_power_creation_master := FourPower.creation_master

/-- Event-word form of the positive local chord. -/
theorem physical_two_digit_chord_event_word := Collision.physical_two_digit_chord_event_word

/-- Complete two-branch local dichotomy for a Happy digit-two cell. -/
theorem happy_digit_two_right_chord_dichotomy := Collision.happy_digit_two_right_chord_dichotomy

/-- Canonical standalone navigation gives the navigation witness. -/
theorem navigation_witness_of_canonical_navigation := Navigation.witness_of_canonical_navigation

/-- Compile-checked theorem map for the promoted Worldtrace layer. -/
#check Worldtrace.TheoremMap

end Worldtrace
