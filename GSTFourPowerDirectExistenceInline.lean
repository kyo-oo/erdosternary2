import GSTFourPowerDirectExistence
import GSTFourPowerDirectNo22
import GSTFourPowerThreeStepQuotientChannel

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

-- CI trigger: standalone conditional bridge only; no production transplant.

namespace GSTFourPowerDirectExistenceInline

open GSTFourPowerDirectExistence
open GSTFourPowerDirectNo22
open GSTFourPowerDirectResidue
open GSTFourPowerDirectResidue81
open GSTFourPowerExponentTritObstruction
open GSTFourPowerThreeStepBadnessDescent
open GSTFourPowerThreeStepQuotientChannel
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineBadState

/--
The exact remaining pure-power seam after all Graph-V2 and Navigation wrappers
are stripped away.

This is intentionally restricted to the canonical affine orbit `affineOrbit K`.
The unrestricted statement for arbitrary naturals is false, so this is the only
legitimate theorem target for the replacement proof.
-/
def CanonicalThreeStepChannelDescent : Prop :=
  ∀ K : Nat,
    BadChannel
      (channelAfterTwo 1 (affineOrbit (K+3)))
      (tail9 (affineOrbit (K+3))) →
    BadChannel
      (channelAfterTwo 1 (affineOrbit K))
      (tail9 (affineOrbit K))

/--
The canonical channel descent is exactly the missing all-depth badness descent.
This theorem is a checked bridge only; it does not pretend to solve the pure
power channel invariant.
-/
theorem gst_three_step_badness_descent_of_canonical_channel_descent
    (hChannel : CanonicalThreeStepChannelDescent) :
    ThreeStepBadnessDescent := by
  intro K hBadNext
  have hNextChannel :
      BadChannel
        (channelAfterTwo 1 (affineOrbit (K+3)))
        (tail9 (affineOrbit (K+3))) :=
    (badAboveThree_iff_quotient_badChannel (K+3)).1 hBadNext
  exact (badAboveThree_iff_quotient_badChannel K).2
    (hChannel K hNextChannel)

/-- The canonical channel descent gives a physical Happy row >= 3 at every
K >= 8. -/
theorem gst_four_power_happy_ge_three_of_canonical_channel_descent
    (hChannel : CanonicalThreeStepChannelDescent) :
    ∀ K : Nat, 8 ≤ K →
      ∃ p : Nat, 3 ≤ p ∧
        GSTU2DEventTransport.HappyCell
          (GSTCanonicalSevenAxisBridge.carry4 (4^K) p)
          (GSTCanonicalSevenAxisBridge.digit3 (4^K) p) := by
  exact happy_ge_three_of_three_step_badness_descent
    (gst_three_step_badness_descent_of_canonical_channel_descent hChannel)

/-- A physical Happy row is a direct common-two witness for consecutive powers
of four. -/
theorem happy_row_to_commonTwo_inline
    (K p : Nat) (hp : 1 ≤ p)
    (hHappy :
      GSTU2DEventTransport.HappyCell
        (GSTCanonicalSevenAxisBridge.carry4 (4^K) p)
        (GSTCanonicalSevenAxisBridge.digit3 (4^K) p)) :
    CommonTwo K := by
  have hPair :=
    (happyCell_iff_four_mul_common_two (4^K) p).1 hHappy
  refine ⟨p, hp, hPair.1, ?_⟩
  simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    hPair.2

/--
Conditional replacement theorem for the old four-power creation boundary.
The only remaining mathematical input is `CanonicalThreeStepChannelDescent`.
-/
theorem gst_four_power_direct_existence_of_canonical_channel_descent
    (hChannel : CanonicalThreeStepChannelDescent) :
    FourPowerDirectExistence := by
  intro K hK5 hK7
  by_cases hK8 : 8 ≤ K
  · obtain ⟨p, hp3, hHappy⟩ :=
      gst_four_power_happy_ge_three_of_canonical_channel_descent hChannel K hK8
    exact happy_row_to_commonTwo_inline K p (by omega) hHappy
  · have hCases : K = 5 ∨ K = 6 ∨ K = 7 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact commonTwo_of_mod9_five_or_six 5 (by decide)
    · exact commonTwo_of_mod9_five_or_six 6 (by decide)
    · exact (hK7 rfl).elim

#check CanonicalThreeStepChannelDescent
#check gst_three_step_badness_descent_of_canonical_channel_descent
#check gst_four_power_happy_ge_three_of_canonical_channel_descent
#check happy_row_to_commonTwo_inline
#check gst_four_power_direct_existence_of_canonical_channel_descent
#print axioms gst_three_step_badness_descent_of_canonical_channel_descent
#print axioms gst_four_power_happy_ge_three_of_canonical_channel_descent
#print axioms happy_row_to_commonTwo_inline
#print axioms gst_four_power_direct_existence_of_canonical_channel_descent

end GSTFourPowerDirectExistenceInline
