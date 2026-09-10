import GSTFourPowerUniversalInduction
import GSTFourPowerAffineTwoTritClassifier

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-!
# Third-wave branch reactor for the four-power direct existence seam

This file does not introduce a new axiom and does not touch the production
monolith.  It puts the remaining custom-axiom replacement seam into the
renormalized GST branch universe.

The key point is that the three apparently different branch goals in
`BranchBadDescent` are exactly the three exponent-descent reactions

* `¬ CommonTwo (3*q)     -> ¬ CommonTwo q`
* `¬ CommonTwo (3*q + 1) -> ¬ CommonTwo q`
* `¬ CommonTwo (3*q + 2) -> ¬ CommonTwo q`

under the already-compiled affine/renormalized classifiers.  This is the clean
third-wave target: prove the direct exponent no-common descent, and the
universal provider follows without the old custom axiom.
-/

namespace GSTFourPowerThirdWaveBranchReactor

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerAffinePeelClassifier
open GSTFourPowerAffineRenormalizedOrbit
open GSTFourPowerAffineTwoTritClassifier
open GSTFourPowerUniversalInduction

/-- Direct exponent form of the third-wave no-common descent. -/
def ThirdWaveNoCommonDescent : Prop :=
  (∀ q : Nat, ¬ CommonTwo (3*q) → ¬ CommonTwo q) ∧
  (∀ q : Nat, ¬ CommonTwo (3*q + 1) → ¬ CommonTwo q) ∧
  (∀ q : Nat, ¬ CommonTwo (3*q + 2) → ¬ CommonTwo q)

/-- Branch 0 is exactly the no-common reaction `3q -> q`. -/
theorem branch_zero_iff_noCommon_descent :
    (∀ q : Nat,
      BadChannel 0 (renormOrbit q) →
        BadChannel 1 (affineOrbit q)) ↔
    (∀ q : Nat, ¬ CommonTwo (3*q) → ¬ CommonTwo q) := by
  constructor
  · intro h q hNo
    exact (noCommonTwo_iff_badChannel_one q).2
      (h q ((noCommonTwo_three_mul_renorm_iff q).1 hNo))
  · intro h q hBad
    exact (noCommonTwo_iff_badChannel_one q).1
      (h q ((noCommonTwo_three_mul_renorm_iff q).2 hBad))

/-- Branch 1 is exactly the no-common reaction `3q+1 -> q`. -/
theorem branch_one_iff_noCommon_descent :
    (∀ q : Nat,
      BadChannel 1 (4 * renormOrbit q) →
        BadChannel 1 (affineOrbit q)) ↔
    (∀ q : Nat, ¬ CommonTwo (3*q + 1) → ¬ CommonTwo q) := by
  constructor
  · intro h q hNo
    exact (noCommonTwo_iff_badChannel_one q).2
      (h q ((noCommonTwo_three_mul_add_one_renorm_iff q).1 hNo))
  · intro h q hBad
    exact (noCommonTwo_iff_badChannel_one q).1
      (h q ((noCommonTwo_three_mul_add_one_renorm_iff q).2 hBad))

/-- Branch 2 is exactly the no-common reaction `3q+2 -> q`. -/
theorem branch_two_iff_noCommon_descent :
    (∀ q : Nat,
      BadChannel 3 (16 * renormOrbit q + 1) →
        BadChannel 1 (affineOrbit q)) ↔
    (∀ q : Nat, ¬ CommonTwo (3*q + 2) → ¬ CommonTwo q) := by
  constructor
  · intro h q hNo
    exact (noCommonTwo_iff_badChannel_one q).2
      (h q ((noCommonTwo_three_mul_add_two_renorm_iff q).1 hNo))
  · intro h q hBad
    exact (noCommonTwo_iff_badChannel_one q).1
      (h q ((noCommonTwo_three_mul_add_two_renorm_iff q).2 hBad))

/-- The renormalized branch package and the direct exponent-descent package are
literally equivalent.  This is the third-wave merge point. -/
theorem branchBadDescent_iff_thirdWaveNoCommonDescent :
    BranchBadDescent ↔ ThirdWaveNoCommonDescent := by
  constructor
  · intro h
    unfold BranchBadDescent at h
    unfold ThirdWaveNoCommonDescent
    exact ⟨
      (branch_zero_iff_noCommon_descent.mp h.1),
      (branch_one_iff_noCommon_descent.mp h.2.1),
      (branch_two_iff_noCommon_descent.mp h.2.2)
    ⟩
  · intro h
    unfold BranchBadDescent
    unfold ThirdWaveNoCommonDescent at h
    exact ⟨
      (branch_zero_iff_noCommon_descent.mpr h.1),
      (branch_one_iff_noCommon_descent.mpr h.2.1),
      (branch_two_iff_noCommon_descent.mpr h.2.2)
    ⟩

/-- The first third-wave reaction expanded through the second exponent trit. -/
theorem branch_zero_second_trit_split
    (q : Nat) (hBad : BadChannel 0 (renormOrbit q)) :
    (q % 3 = 0 ∧ BadChannel 0 (tail3 (renormOrbit q))) ∨
      (q % 3 = 1 ∧ BadChannel 1 (tail3 (renormOrbit q))) := by
  have hNo : ¬ CommonTwo (3*q) :=
    (noCommonTwo_three_mul_renorm_iff q).2 hBad
  simpa [renormOrbit] using
    (noCommonTwo_three_mul_second_iff q).1 hNo

/-- Third-wave branch zero cannot survive when the next exponent trit is `2`;
that is exactly the structural `K mod 9 = 6` kill class. -/
theorem branch_zero_forces_not_mod_three_two
    (q : Nat) (hBad : BadChannel 0 (renormOrbit q)) :
    q % 3 ≠ 2 := by
  intro hq
  have hNo : ¬ CommonTwo (3*q) :=
    (noCommonTwo_three_mul_renorm_iff q).2 hBad
  exact hNo (commonTwo_three_mul_of_q_mod_three_two q hq)

/-- The middle third-wave reaction expanded through the second exponent trit. -/
theorem branch_one_second_trit_split
    (q : Nat) (hBad : BadChannel 1 (4 * renormOrbit q)) :
    (q % 3 = 0 ∧ BadChannel 0 (tail3 (4 * renormOrbit q))) ∨
      (q % 3 = 1 ∧ BadChannel 1 (tail3 (4 * renormOrbit q))) ∨
      (q % 3 = 2 ∧ BadChannel 3 (tail3 (4 * renormOrbit q))) := by
  have hNo : ¬ CommonTwo (3*q + 1) :=
    (noCommonTwo_three_mul_add_one_renorm_iff q).2 hBad
  simpa [peel1_eq_four_renorm] using
    (noCommonTwo_three_mul_add_one_second_iff q).1 hNo

/-- The final third-wave reaction expanded through the twisted second trit. -/
theorem branch_two_second_trit_split
    (q : Nat) (hBad : BadChannel 3 (16 * renormOrbit q + 1)) :
    ((q + 1) % 3 = 0 ∧
        BadChannel 1 (tail3 (16 * renormOrbit q + 1))) ∨
      ((q + 1) % 3 = 1 ∧
        BadChannel 2 (tail3 (16 * renormOrbit q + 1))) := by
  have hNo : ¬ CommonTwo (3*q + 2) :=
    (noCommonTwo_three_mul_add_two_renorm_iff q).2 hBad
  simpa [peel2_eq_sixteen_renorm_add_one] using
    (noCommonTwo_three_mul_add_two_second_iff q).1 hNo

/-- Third-wave branch two cannot survive when `q % 3 = 1`; that is the
structural `K mod 9 = 5` kill class. -/
theorem branch_two_forces_not_mod_three_one
    (q : Nat) (hBad : BadChannel 3 (16 * renormOrbit q + 1)) :
    q % 3 ≠ 1 := by
  intro hq
  have hNo : ¬ CommonTwo (3*q + 2) :=
    (noCommonTwo_three_mul_add_two_renorm_iff q).2 hBad
  exact hNo (commonTwo_three_mul_add_two_of_q_mod_three_one q hq)

/-- If the third-wave direct exponent descent is proved, the old custom
four-power direct-existence boundary is discharged. -/
theorem fourPowerDirectExistence_of_thirdWaveNoCommonDescent
    (hWave : ThirdWaveNoCommonDescent) :
    FourPowerDirectExistence := by
  exact fourPowerDirectExistence_of_branch_bad_descent
    ((branchBadDescent_iff_thirdWaveNoCommonDescent).2 hWave)

/-- The exact theorem still to be closed for the unconditional replacement.
This is deliberately a `def` target, not an axiom or a theorem with a fake body. -/
def ThirdWaveUniversalClosure : Prop := ThirdWaveNoCommonDescent

#check ThirdWaveNoCommonDescent
#check branch_zero_iff_noCommon_descent
#check branch_one_iff_noCommon_descent
#check branch_two_iff_noCommon_descent
#check branchBadDescent_iff_thirdWaveNoCommonDescent
#check branch_zero_second_trit_split
#check branch_zero_forces_not_mod_three_two
#check branch_one_second_trit_split
#check branch_two_second_trit_split
#check branch_two_forces_not_mod_three_one
#check fourPowerDirectExistence_of_thirdWaveNoCommonDescent
#print axioms branch_zero_iff_noCommon_descent
#print axioms branch_one_iff_noCommon_descent
#print axioms branch_two_iff_noCommon_descent
#print axioms branchBadDescent_iff_thirdWaveNoCommonDescent
#print axioms branch_zero_second_trit_split
#print axioms branch_zero_forces_not_mod_three_two
#print axioms branch_one_second_trit_split
#print axioms branch_two_second_trit_split
#print axioms branch_two_forces_not_mod_three_one
#print axioms fourPowerDirectExistence_of_thirdWaveNoCommonDescent

end GSTFourPowerThirdWaveBranchReactor
