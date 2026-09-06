import ErdosTernary2
import GST.Problem406.LocalCell

/-!
# Worldtrace collision-closure layer

Public names for local cell classification, bad traces, residual NULL closure,
terminal gates, and exact physical rectangles.  This layer is where forbidden
worldtraces are forced into contradictions.
-/

namespace Worldtrace
namespace Collision

/-- Local BIG1-clear condition at one physical digit-two cell. -/
abbrev PhysicalTwoDigitClear : Nat → Nat → Prop := GST.Problem406.PhysicalTwoDigitClear

/-- Complete adjacent four-power bad-trace assertion. -/
abbrev AdjacentBadTrace : Nat → Prop := GST.Problem406.AdjacentFourPowerBadTrace

/-- The second microscopic output equals the ordinary x4 output digit. -/
theorem second_micro_output_eq_x4_output := GST.Problem406.second_micro_output_eq_x4_output

/-- The local clear branch forces the positive carry-three orientation. -/
theorem physical_two_digit_chord_forces_plus := GST.Problem406.physical_two_digit_chord_forces_plus

/-- Event-word form of the positive local chord. -/
theorem physical_two_digit_chord_event_word := GST.Problem406.physical_two_digit_chord_event_word

/-- Numeric form of the local chord: the aligned two-layer code is `6^2 - 1`. -/
theorem physical_two_digit_chord_code := GST.Problem406.physical_two_digit_chord_code

/-- At an already-Happy digit-two cell, clear is equivalent to carry three. -/
theorem happy_digit_two_clear_iff_plus := GST.Problem406.happy_digit_two_clear_iff_plus

/-- The complementary branch is the null local orientation. -/
theorem happy_digit_two_not_clear_is_null := GST.Problem406.happy_digit_two_not_clear_is_null

/-- Complete two-branch local dichotomy for a Happy digit-two cell. -/
theorem happy_digit_two_right_chord_dichotomy := GST.Problem406.happy_digit_two_right_chord_dichotomy

/-- Exact local hand-off at the last child Happy gate. -/
theorem last_child_gate_right_chord := GST.Problem406.last_child_gate_right_chord

/-- The residual NULL terminal word. -/
abbrev ResidualNullTerminal : Nat → Nat := _root_.gstResidualNullTerminalS

/-- Stable low residue of the terminal NULL suffix. -/
theorem residual_null_terminal_mod27 := _root_.gst_residual_null_terminal_mod27S

/-- The stable terminal NULL suffix has a physical Happy gate at position two. -/
theorem residual_null_terminal_happy := _root_.gst_residual_null_terminal_happyS

/-- Explicit level-one terminal gate. -/
theorem residual_null_terminal_happy_s1 := _root_.gst_residual_null_terminal_happy_s1S

/-- Explicit level-two terminal gate. -/
theorem residual_null_terminal_happy_s2 := _root_.gst_residual_null_terminal_happy_s2S

/-- Explicit level-three terminal gate. -/
theorem residual_null_terminal_happy_s3 := _root_.gst_residual_null_terminal_happy_s3S

/-- Every positive canonical level has an explicit terminal NULL gate. -/
theorem residual_null_terminal_happy_all := _root_.gst_residual_null_terminal_happy_allS

/-- The NULL-reduced origin-one expression is exactly the canonical terminal word. -/
theorem residual_null_origin_one_terminal_eq := _root_.gst_residual_null_origin_one_terminal_eqS

/-- Complete terminal base for every positive canonical level. -/
theorem residual_null_origin_one_bad_impossible_all := _root_.gst_residual_null_origin_one_bad_impossible_allS

/-- NULL forcing step: a completely bad residual origin must go deeper. -/
theorem residual_null_bad_forces_deeper_origin := _root_.gst_residual_null_bad_forces_deeper_originS

/-- Exact channel equation in physical power-grid coordinates. -/
theorem exact_power_block_channel_echo := _root_.gst_exact_power_block_channel_echoS

/-- Exact conservation across one physical power rectangle. -/
theorem exact_power_rectangle_conservation := _root_.gst_exact_power_rectangle_conservationS

/-- Parent badness forbids a residue sector in the exact power rectangle. -/
theorem pure_power_parent_bad_forbids_residue_sector := _root_.gst_pure_power_parent_bad_forbids_residue_sectorS

end Collision
end Worldtrace
