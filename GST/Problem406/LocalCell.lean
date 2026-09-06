import ErdosTernary2

/-!
# Local cell classification API

Public names for the finite local classification used by the right-chord and
last-gate arguments.
-/

namespace GST
namespace Problem406

/-- Local BIG1-clear condition at one physical digit-two cell. -/
abbrev PhysicalTwoDigitClear : Nat → Nat → Prop := GSTPhysicalTwoDigitBig1ClearS

/-- The second microscopic output equals the ordinary x4 output digit. -/
theorem second_micro_output_eq_x4_output :=
  gst_second_micro_output_eq_x4_outputS

/-- The local clear branch forces the positive carry-three orientation. -/
theorem physical_two_digit_chord_forces_plus :=
  gst_physical_two_digit_chord_forces_gst_plusS

/-- Event-word form of the positive local chord. -/
theorem physical_two_digit_chord_event_word :=
  gst_physical_two_digit_chord_event_88S

/-- Numeric form of the local chord: the aligned two-layer code is `6^2 - 1`. -/
theorem physical_two_digit_chord_code :=
  gst_physical_two_digit_chord_35S

/-- At an already-Happy digit-two cell, clear is equivalent to carry three. -/
theorem happy_digit_two_clear_iff_plus :=
  gst_happy_big2_two_digit_clear_iff_plusS

/-- The complementary branch is the null local orientation. -/
theorem happy_digit_two_not_clear_is_null :=
  gst_happy_big2_two_digit_not_clear_is_nullS

/-- Complete two-branch local dichotomy for a Happy digit-two cell. -/
theorem happy_digit_two_right_chord_dichotomy :=
  gst_happy_big2_right_chord_dichotomyS

/-- Exact local hand-off at the last child Happy gate. -/
theorem last_child_gate_right_chord :=
  gst_last_child_gate_right_chordS

end Problem406
end GST
