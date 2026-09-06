import ErdosTernary2
import GST.Problem406.FourPower
import GST.FourPower.CommonTwo
import GST.FourPower.PrefixLaw
import GST.FourPower.Certificate

/-!
# Worldtrace four-power dynamics layer

Public names for adjacent four-power waves, common digit-two witnesses,
exponent-prefix obstruction, and certificate transport.  This is the core
number-theoretic dynamics layer feeding the final Problem 406 theorem.
-/

namespace Worldtrace
namespace FourPower

/-- The assertion that `4^a` contains a ternary digit `2`. -/
abbrev hasDigitTwo : Nat → Prop := GST.Problem406.FourPowerHasDigitTwo

/-- A row where `4^K` and `4^(K+1)` both have ternary digit `2`. -/
abbrev CommonTwo : Nat → Prop := GST.FourPower.CommonTwo

/-- Universal direct common-two existence target, except for the known exponent `7`. -/
abbrev DirectExistence : Prop := GST.FourPower.DirectExistence

/-- Adjacent four-power wave assertion. -/
abbrev AdjacentWave : Nat → Prop := GST.Problem406.AdjacentFourPowerWave

/-- Complete adjacent four-power bad trace. -/
abbrev AdjacentBadTrace : Nat → Prop := GST.Problem406.AdjacentFourPowerBadTrace

/-- Historical creation certificate for a number `R`. -/
abbrev CreationCertificate : Nat → Prop := GST.FourPower.CreationCertificate

/-- Universal four-power creation master proposition. -/
abbrev CreationMaster : Prop := GST.FourPower.CreationMaster

/-- Every `4^a` with `a ≥ 5` has ternary digit `2`. -/
theorem contains_digit_two := GST.Problem406.four_power_contains_digit_two

/-- Exact adjacent-power identity used by the even-exponent reduction. -/
theorem adjacent_identity := GST.Problem406.adjacent_four_power_identity

/-- Failure of both navigation alternatives gives a complete two-wave bad trace. -/
theorem adjacent_bad_trace_of_no_navigation := GST.Problem406.adjacent_bad_trace_of_no_navigation

/-- Large adjacent four-power waves satisfy the navigation alternative. -/
theorem large_adjacent_wave := GST.Problem406.large_adjacent_four_power_wave

/-- A common-two witness gives a digit two in the source power. -/
theorem common_two_has_source_two := GST.FourPower.common_two_has_source_two

/-- A common-two witness gives a digit two in the target power. -/
theorem common_two_has_target_two := GST.FourPower.common_two_has_target_two

/-- Exact row-two common-two classes modulo nine. -/
theorem common_two_of_mod9_five_or_six := GST.FourPower.common_two_of_mod9_five_or_six

/-- Exponent-prefix/trit decomposition. -/
theorem exponent_prefix_trit_decomposition := GST.FourPower.exponent_prefix_trit_decomposition

/-- Consecutive-power pair formula from the exponent trit. -/
theorem pow4_pair_from_exponent_trit := GST.FourPower.pow4_pair_from_exponent_trit

/-- Parametric direct obstruction on every ternary exponent trit. -/
theorem no_common_two_exponent_trit_obstruction := GST.FourPower.no_common_two_exponent_trit_obstruction

/-- A creation certificate gives a navigation witness. -/
theorem creation_certificate_to_navigation := GST.FourPower.creation_certificate_to_navigation

/-- Four-power navigation from a supplied creation master. -/
theorem navigation_of_creation_master := GST.FourPower.four_power_navigation_of_master

/-- Certified four-power creation master from the proof corpus. -/
theorem creation_master := GST.Problem406.four_power_creation_master

end FourPower
end Worldtrace
