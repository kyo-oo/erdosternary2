import GSTFourPowerMultiscaleRenormalization
import GSTFourPowerAffineRenormalizedOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

namespace GSTFourPowerThirdWaveMultiscaleBridge

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineRenormalizedOrbit
open GSTFourPowerMultiscaleRenormalization

/-- Scale zero is exactly the historical affine orbit. -/
theorem scaleOrbit_zero_eq_affineOrbit (q : Nat) :
    scaleOrbit 0 q = affineOrbit q := by
  induction q with
  | zero =>
      simp [scaleOrbit, affineOrbit]
  | succ q ih =>
      rw [scaleOrbit_zero_succ, affineOrbit_succ, ih]

/-- Scale one is exactly the renormalized orbit used by the third-wave analysis. -/
theorem scaleOrbit_one_eq_renormOrbit (q : Nat) :
    scaleOrbit 1 q = renormOrbit q := by
  induction q with
  | zero =>
      simp [scaleOrbit, renormOrbit, GSTFourPowerAffineExponentPeel.peel0,
        affineOrbit]
  | succ q ih =>
      rw [scaleOrbit_one_succ, renormOrbit_succ, ih]

/-- The zero child of one ternary exponent digit is the exact cross-scale
conjugacy from scale zero to scale one. -/
theorem affineOrbit_three_mul_multiscale (q : Nat) :
    affineOrbit (3*q) = 3 * scaleOrbit 1 q := by
  rw [← scaleOrbit_zero_eq_affineOrbit]
  exact scaleOrbit_three_mul 0 q

/-- Exact scale-one form of the exponent child 3q+1. -/
theorem affineOrbit_three_mul_add_one_multiscale (q : Nat) :
    affineOrbit (3*q+1) = 1 + 12 * scaleOrbit 1 q := by
  rw [show 3*q+1 = (3*q)+1 by omega, affineOrbit_succ,
    affineOrbit_three_mul_multiscale]
  ring

/-- Exact scale-one form of the exponent child 3q+2. -/
theorem affineOrbit_three_mul_add_two_multiscale (q : Nat) :
    affineOrbit (3*q+2) = 5 + 48 * scaleOrbit 1 q := by
  rw [show 3*q+2 = (3*q+1)+1 by omega, affineOrbit_succ,
    affineOrbit_three_mul_add_one_multiscale]
  ring

/-- Removing the exponent trit from the 3q child lands literally on scale one. -/
theorem tail3_affineOrbit_three_mul_multiscale (q : Nat) :
    tail3 (affineOrbit (3*q)) = scaleOrbit 1 q := by
  rw [affineOrbit_three_mul_multiscale]
  simp [tail3]

/-- Removing the exponent trit from the 3q+1 child lands on the first affine
edge over scale one. -/
theorem tail3_affineOrbit_three_mul_add_one_multiscale (q : Nat) :
    tail3 (affineOrbit (3*q+1)) = 4 * scaleOrbit 1 q := by
  rw [affineOrbit_three_mul_add_one_multiscale]
  unfold tail3
  omega

/-- Removing the exponent trit from the 3q+2 child lands on the second affine
edge over scale one. -/
theorem tail3_affineOrbit_three_mul_add_two_multiscale (q : Nat) :
    tail3 (affineOrbit (3*q+2)) = 16 * scaleOrbit 1 q + 1 := by
  rw [affineOrbit_three_mul_add_two_multiscale]
  unfold tail3
  omega

/-- The branch-zero classifier expressed entirely through the multiscale orbit. -/
theorem noCommonTwo_three_mul_scale_iff (q : Nat) :
    (¬ CommonTwo (3*q)) ↔ BadChannel 0 (scaleOrbit 1 q) := by
  simpa [scaleOrbit_one_eq_renormOrbit] using
    (GSTFourPowerAffineRenormalizedOrbit.noCommonTwo_three_mul_renorm_iff q)

/-- The branch-one classifier expressed entirely through the multiscale orbit. -/
theorem noCommonTwo_three_mul_add_one_scale_iff (q : Nat) :
    (¬ CommonTwo (3*q+1)) ↔ BadChannel 1 (4 * scaleOrbit 1 q) := by
  simpa [scaleOrbit_one_eq_renormOrbit] using
    (GSTFourPowerAffineRenormalizedOrbit.noCommonTwo_three_mul_add_one_renorm_iff q)

/-- The branch-two classifier expressed entirely through the multiscale orbit. -/
theorem noCommonTwo_three_mul_add_two_scale_iff (q : Nat) :
    (¬ CommonTwo (3*q+2)) ↔ BadChannel 3 (16 * scaleOrbit 1 q + 1) := by
  simpa [scaleOrbit_one_eq_renormOrbit] using
    (GSTFourPowerAffineRenormalizedOrbit.noCommonTwo_three_mul_add_two_renorm_iff q)

/-- Exact exponent form of the remaining third-wave closure. -/
def ThirdWaveNoCommonDescent : Prop :=
  (∀ q : Nat, ¬ CommonTwo (3*q) → ¬ CommonTwo q) ∧
  (∀ q : Nat, ¬ CommonTwo (3*q+1) → ¬ CommonTwo q) ∧
  (∀ q : Nat, ¬ CommonTwo (3*q+2) → ¬ CommonTwo q)

/-- Same closure expressed on the canonical scale-zero/scale-one coordinates. -/
def MultiscaleBranchBadDescent : Prop :=
  (∀ q : Nat,
    BadChannel 0 (scaleOrbit 1 q) →
      BadChannel 1 (scaleOrbit 0 q)) ∧
  (∀ q : Nat,
    BadChannel 1 (4 * scaleOrbit 1 q) →
      BadChannel 1 (scaleOrbit 0 q)) ∧
  (∀ q : Nat,
    BadChannel 3 (16 * scaleOrbit 1 q + 1) →
      BadChannel 1 (scaleOrbit 0 q))

/-- The direct exponent closure and the multiscale bad-channel closure are
literally the same theorem after the exact scale conjugacies. -/
theorem thirdWaveNoCommonDescent_iff_multiscale :
    ThirdWaveNoCommonDescent ↔ MultiscaleBranchBadDescent := by
  constructor
  · intro h
    unfold ThirdWaveNoCommonDescent at h
    unfold MultiscaleBranchBadDescent
    constructor
    · intro q hBad
      have hNoChild : ¬ CommonTwo (3*q) :=
        (noCommonTwo_three_mul_scale_iff q).2 hBad
      have hNoParent := h.1 q hNoChild
      have hp : BadChannel 1 (affineOrbit q) :=
        (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).1 hNoParent
      simpa [scaleOrbit_zero_eq_affineOrbit] using hp
    · constructor
      · intro q hBad
        have hNoChild : ¬ CommonTwo (3*q+1) :=
          (noCommonTwo_three_mul_add_one_scale_iff q).2 hBad
        have hNoParent := h.2.1 q hNoChild
        have hp : BadChannel 1 (affineOrbit q) :=
          (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).1 hNoParent
        simpa [scaleOrbit_zero_eq_affineOrbit] using hp
      · intro q hBad
        have hNoChild : ¬ CommonTwo (3*q+2) :=
          (noCommonTwo_three_mul_add_two_scale_iff q).2 hBad
        have hNoParent := h.2.2 q hNoChild
        have hp : BadChannel 1 (affineOrbit q) :=
          (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).1 hNoParent
        simpa [scaleOrbit_zero_eq_affineOrbit] using hp
  · intro h
    unfold MultiscaleBranchBadDescent at h
    unfold ThirdWaveNoCommonDescent
    constructor
    · intro q hNoChild
      have hb : BadChannel 0 (scaleOrbit 1 q) :=
        (noCommonTwo_three_mul_scale_iff q).1 hNoChild
      have hp := h.1 q hb
      have hp' : BadChannel 1 (affineOrbit q) := by
        simpa [scaleOrbit_zero_eq_affineOrbit] using hp
      exact (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).2 hp'
    · constructor
      · intro q hNoChild
        have hb : BadChannel 1 (4 * scaleOrbit 1 q) :=
          (noCommonTwo_three_mul_add_one_scale_iff q).1 hNoChild
        have hp := h.2.1 q hb
        have hp' : BadChannel 1 (affineOrbit q) := by
          simpa [scaleOrbit_zero_eq_affineOrbit] using hp
        exact (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).2 hp'
      · intro q hNoChild
        have hb : BadChannel 3 (16 * scaleOrbit 1 q + 1) :=
          (noCommonTwo_three_mul_add_two_scale_iff q).1 hNoChild
        have hp := h.2.2 q hb
        have hp' : BadChannel 1 (affineOrbit q) := by
          simpa [scaleOrbit_zero_eq_affineOrbit] using hp
        exact (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).2 hp'

#print axioms scaleOrbit_zero_eq_affineOrbit
#print axioms scaleOrbit_one_eq_renormOrbit
#print axioms affineOrbit_three_mul_multiscale
#print axioms tail3_affineOrbit_three_mul_add_two_multiscale
#print axioms thirdWaveNoCommonDescent_iff_multiscale

end GSTFourPowerThirdWaveMultiscaleBridge
