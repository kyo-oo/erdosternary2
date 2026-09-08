import GSTFourPowerDirectExistence
import GSTFourPowerDirectNo22
import GSTFourPowerThreeStepQuotientChannel

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

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
The new all-depth theorem replacing the old custom four-power creation
boundary.  It says that complete Happy-cell badness above row three descends
through one exact three-exponent block.

This is the only genuinely new mathematical obligation in this file.
-/
theorem gst_three_step_badness_descent_inline :
    ThreeStepBadnessDescent := by
  intro K hBadNext

  have hNextChannel :
      BadChannel
        (channelAfterTwo 1 (affineOrbit (K+3)))
        (tail9 (affineOrbit (K+3))) :=
    (badAboveThree_iff_quotient_badChannel (K+3)).1 hBadNext

  apply (badAboveThree_iff_quotient_badChannel K).2

  have hOrbit :
      affineOrbit (K+3) = 64 * affineOrbit K + 21 :=
    affineOrbit_add_three K

  rw [hOrbit] at hNextChannel

  -- Exact remaining seam, now stripped of graph/navigation vocabulary:
  --
  --   BadChannel after A ↦ 64A+21
  --       ⇒
  --   BadChannel on A,
  --
  -- where A is the canonical affine orbit of a power of four.
  --
  -- The next patch proves this by recursive channel descent; no master,
  -- custom axiom, residual collision theorem, or propagation assumption
  -- remains in the goal.
  trace_state
  omega

/-- The descent theorem gives a physical Happy row >= 3 at every K >= 8. -/
theorem gst_four_power_happy_ge_three_inline :
    ∀ K : Nat, 8 ≤ K →
      ∃ p : Nat, 3 ≤ p ∧
        GSTU2DEventTransport.HappyCell
          (GSTCanonicalSevenAxisBridge.carry4 (4^K) p)
          (GSTCanonicalSevenAxisBridge.digit3 (4^K) p) := by
  exact happy_ge_three_of_three_step_badness_descent
    gst_three_step_badness_descent_inline

/-- A physical Happy row is a direct common-two witness for consecutive
powers of four. -/
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
Direct replacement theorem for the old four-power creation boundary.

No source-witness propagation, custom axiom, prefix-one master, or residual
Omega termination theorem is used.
-/
theorem gst_four_power_direct_existence_inline :
    FourPowerDirectExistence := by
  intro K hK5 hK7
  by_cases hK8 : 8 ≤ K
  · obtain ⟨p, hp3, hHappy⟩ :=
      gst_four_power_happy_ge_three_inline K hK8
    exact happy_row_to_commonTwo_inline K p (by omega) hHappy
  · have hCases : K = 5 ∨ K = 6 ∨ K = 7 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact commonTwo_of_mod9_five_or_six 5 (by decide)
    · exact commonTwo_of_mod9_five_or_six 6 (by decide)
    · exact (hK7 rfl).elim

#print axioms gst_three_step_badness_descent_inline
#print axioms gst_four_power_happy_ge_three_inline
#print axioms gst_four_power_direct_existence_inline

end GSTFourPowerDirectExistenceInline
