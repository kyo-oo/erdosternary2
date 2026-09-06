import GSTFourPowerDirectExistence

/-!
# Four-power common-two API

Public names for the direct arithmetic common digit-two witness between two
consecutive powers of four.
-/

namespace GST
namespace FourPower

/-- A row where `4^K` and `4^(K+1)` both have ternary digit `2`. -/
abbrev CommonTwo : Nat → Prop := GSTFourPowerDirectExistence.CommonTwo

/-- Universal direct common-two existence target, except for the known exponent `7`. -/
abbrev DirectExistence : Prop := GSTFourPowerDirectExistence.FourPowerDirectExistence

/-- A common-two witness gives a digit two in the source power. -/
theorem common_two_has_source_two
    (K : Nat) (h : CommonTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ GSTFourPowerDirectResidue.digit3 (4^K) p = 2 := by
  exact GSTFourPowerDirectExistence.commonTwo_has_source_two K h

/-- A common-two witness gives a digit two in the next power. -/
theorem common_two_has_target_two
    (K : Nat) (h : CommonTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ GSTFourPowerDirectResidue.digit3 (4^(K+1)) p = 2 := by
  exact GSTFourPowerDirectExistence.commonTwo_has_target_two K h

/-- Exact row-two direct common-two classes modulo nine. -/
theorem common_two_of_mod9_five_or_six
    (K : Nat) (hres : K % 9 = 5 ∨ K % 9 = 6) :
    CommonTwo K := by
  exact GSTFourPowerDirectExistence.commonTwo_of_mod9_five_or_six K hres

end FourPower
end GST
