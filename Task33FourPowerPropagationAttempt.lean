import GSTGraphV2FourPowerCanonicalParentObstruction
import Task33ResidualCollisionBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task33FourPowerPropagationAttempt

open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2NonlocalCascade
open GSTGraphV2FourPowerRelocation
open GSTGraphV2FourPowerResidueObstruction
open GSTGraphV2FourPowerCanonicalParentObstruction

/-- Direct Task 3.3 attack.  The proof immediately consumes the already-green
local split, closes the direct branch, and turns the latent branch into the
literal global no-relocation contradiction language.  The remaining compiler
state is therefore exactly the power-specific obstruction demanded by the
handoff, not repository archaeology. -/
theorem four_power_happy_propagates_attempt :
    GSTGraphV2FourPowerRelocation.FourPowerHappyPropagation := by
  intro K p hK hp hHappy
  rcases four_power_happy_lifts_or_latent K p hHappy with hDirect | hLatent
  · exact ⟨p, hp, hDirect⟩
  · by_contra hNo
    have hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
        HappyCell (graph 1 (K+1) q).seven.carry
          (graph 1 (K+1) q).seven.digit := by
      simpa using hNo
    have hFutureBad :=
      future_bad_of_no_relocated_happy K p hNoRelocated
    have hResidue56 :=
      no_relocated_happy_forbids_mod9_five_six K hNoRelocated
    rcases hLatent with ⟨hDigit, hCarry, hNext⟩
    have hPacket := latent_vertical_future_packet K p hNext
    have hNeutral := four_power_graph_neutral_at_support_cutoff K
    -- Force Lean to expose the exact residual bridge still required after all
    -- already-certified physical/arithmetic facts have been installed.
    have hmodlt : (K+1) % 9 < 9 := Nat.mod_lt _ (by decide)
    interval_cases hmod : (K+1) % 9
    all_goals try omega

#check four_power_happy_propagates_attempt
#print axioms four_power_happy_propagates_attempt

end Task33FourPowerPropagationAttempt
