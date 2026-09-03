import GSTFourPowerAffinePeelClassifier
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineHappyConstruction

open GSTFourPowerAffinePeelClassifier
open GSTFourPowerDirectHappyBridge

/-- Direct physical construction on affine exponent branch `0`.  The affine
classifier kills a bad state when the next exponent trit is `2`; the resulting
`CommonTwo` witness is converted at the very same row into an actual physical
Happy cell. -/
theorem physical_happy_three_mul_of_q_mod_three_eq_two
    (u : Nat) (hu : u % 3 = 2) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(3*u)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(3*u)) q) := by
  exact commonTwo_to_physical_happy_row
    (3*u)
    (commonTwo_three_mul_of_q_mod_three_eq_two u hu)

/-- Direct physical construction on affine exponent branch `2`.  When the next
exponent trit is `1`, the twisted second affine read is `2`, terminating state
`3`; again the common-two row itself is the physical Happy row. -/
theorem physical_happy_three_mul_add_two_of_q_mod_three_eq_one
    (u : Nat) (hu : u % 3 = 1) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(3*u+2)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(3*u+2)) q) := by
  exact commonTwo_to_physical_happy_row
    (3*u+2)
    (commonTwo_three_mul_add_two_of_q_mod_three_eq_one u hu)

/-- Relocation-shaped branch `0` constructor.  No global direct-existence
assumption is used: if the next exponent itself has affine suffix `20`, a real
Happy row on `4^(K+1)` is constructed directly. -/
theorem relocated_physical_happy_of_next_three_mul
    (K u : Nat) (hEq : K + 1 = 3*u) (hu : u % 3 = 2) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  rw [hEq]
  exact physical_happy_three_mul_of_q_mod_three_eq_two u hu

/-- Relocation-shaped branch `2` constructor.  If the next exponent has affine
suffix `12` (least-significant trit first), the direct finite-state kill law
constructs an actual relocated Happy row `q ≥ 1` with no navigation route and
no `FourPowerDirectExistence` hypothesis. -/
theorem relocated_physical_happy_of_next_three_mul_add_two
    (K u : Nat) (hEq : K + 1 = 3*u+2) (hu : u % 3 = 1) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  rw [hEq]
  exact physical_happy_three_mul_add_two_of_q_mod_three_eq_one u hu

#check physical_happy_three_mul_of_q_mod_three_eq_two
#check physical_happy_three_mul_add_two_of_q_mod_three_eq_one
#check relocated_physical_happy_of_next_three_mul
#check relocated_physical_happy_of_next_three_mul_add_two
#print axioms physical_happy_three_mul_of_q_mod_three_eq_two
#print axioms physical_happy_three_mul_add_two_of_q_mod_three_eq_one
#print axioms relocated_physical_happy_of_next_three_mul
#print axioms relocated_physical_happy_of_next_three_mul_add_two

end GSTFourPowerAffineHappyConstruction
