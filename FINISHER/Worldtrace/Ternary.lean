import ErdosTernary2
import GST.Arithmetic.TernaryDigits

/-!
# Worldtrace ternary event layer

Clean public names for digit-two predicates, finite-prefix scans, and positional
ternary witnesses.  This layer records the digit/event part of Worldtrace
Arithmetic before the carry and navigation layers are added.
-/

namespace Worldtrace
namespace Ternary

/-- Boolean predicate: the ternary expansion contains no digit `2`. -/
abbrev containsNoDigitTwo : Nat → Bool := _root_.noTernaryTwo

/-- Structural bounded form of `containsNoDigitTwo`. -/
abbrev containsNoDigitTwoStruct : Nat → Nat → Bool := _root_.noTernaryTwoStruct

/-- Boolean predicate: the ternary expansion contains a digit `2`. -/
abbrev containsDigitTwo : Nat → Bool := _root_.hasTernaryTwo

/-- Structural bounded form of `containsDigitTwo`. -/
abbrev containsDigitTwoStruct : Nat → Nat → Bool := _root_.hasTernaryTwoStruct

/-- Predicate checking whether position `p` carries digit `2`. -/
abbrev hasDigitTwoAtPosition : Nat → Nat → Bool := _root_.hasD2AtPos

/-- Predicate checking whether a digit `2` appears in the first `k` ternary rows. -/
abbrev hasDigitTwoInPrefix : Nat → Nat → Bool := _root_.hasTwoInFirstK

/-- Structural prefix scanner used by decidable finite checks. -/
abbrev hasDigitTwoInPrefixStruct : Nat → Nat → Bool := _root_.hasTwoInFirstKStruct

/-- Public ternary digit projection. -/
abbrev digit : Nat → Nat → Nat := GST.Arithmetic.digit3

/-- Structural no-digit-two computation agrees with the recursive predicate past the full horizon. -/
theorem no_digit_two_eq_struct := _root_.noTernaryTwo_eq_struct

/-- Prefix scanner agrees with its structural form. -/
theorem prefix_scan_eq_struct := _root_.hasTwoInFirstK_eq_struct

/-- A successful prefix scan gives an explicit digit-two position. -/
theorem prefix_scan_has_position := _root_.hasTwoInFirstK_pos

/-- A bounded prefix witness lifts to an unbounded digit-two witness. -/
theorem prefix_scan_contains_digit_two := _root_.hasTwoInFirstK_imp_hasTernaryTwo

/-- A low-residue digit-two witness lifts to the original number. -/
theorem residue_contains_digit_two := _root_.mod_has_two

/-- Exact digit projection through a low prefix. -/
theorem prefix_slice_digit_exact := GST.Arithmetic.prefix_slice_digit_exact

/-- Canonical tail digit/carry state isomorphism. -/
theorem canonical_tail_state_isomorphism := GST.Arithmetic.canonical_tail_state_isomorphism

end Ternary
end Worldtrace
