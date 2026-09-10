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
#check fourPowerDirectExistence_of_thirdWaveNoCommonDescent
#print axioms branch_zero_iff_noCommon_descent
#print axioms branch_one_iff_noCommon_descent
#print axioms branch_two_iff_noCommon_descent
#print axioms branchBadDescent_iff_thirdWaveNoCommonDescent
#print axioms fourPowerDirectExistence_of_thirdWaveNoCommonDescent

end GSTFourPowerThirdWaveBranchReactor
