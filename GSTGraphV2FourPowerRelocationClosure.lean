import GSTGraphV2FourPowerCanonicalParentObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerRelocationClosure

open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2NonlocalCascade
open GSTGraphV2FourPowerRelocation
open GSTGraphV2FourPowerResidueObstruction
open GSTGraphV2FourPowerCanonicalParentObstruction

/-- Concrete universal-relocation proof attempt.  This is intentionally a real
Lean theorem, not a proposition alias or a search note.  Every contradiction
branch must manufacture the target Happy witness. -/
theorem four_power_happy_propagates :
    GSTGraphV2FourPowerRelocation.FourPowerHappyPropagation := by
  intro K p hK hp hHappy
  by_cases hTarget : ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit
  · exact hTarget
  · rcases four_power_happy_lifts_or_latent K p hHappy with hDirect | hLatent
    · exact ⟨p, hp, hDirect⟩
    · rcases hLatent with ⟨hDigit, hCarry, hNext⟩
      have hResidue : (K+1) % 9 ≠ 5 ∧ (K+1) % 9 ≠ 6 :=
        no_relocated_happy_forbids_mod9_five_six K hTarget
      have hFutureBad :=
        GSTGraphV2FourPowerRelocation.future_bad_of_no_relocated_happy K p hTarget
      have hPacket :=
        GSTGraphV2FourPowerRelocation.latent_vertical_future_packet K p hNext
      -- Force Lean to expose the exact remaining arithmetic/controller cases.
      have hmodlt : (K+1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
      interval_cases hmod : (K+1) % 9
      all_goals simp_all

#check four_power_happy_propagates
#print axioms four_power_happy_propagates

end GSTGraphV2FourPowerRelocationClosure
