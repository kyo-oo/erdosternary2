import GSTInfiniteFourPowerNavigation
import GSTFourPowerOntologicalAdapter

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTFourPowerHappyGeThreeClean

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTGraphV2CoupledUFlux
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GSTFinalPurePowerResidueTransplant
open GSTU2DEventTransport

/-- Clean export of the already-closed width-three collision seam from
`GSTInfiniteFourPowerNavigation`.  This file deliberately does not re-open the
old failed `linarith` proof attempt; it pins the production theorem surface to
the green monolith proof engine. -/
theorem power_three_step_collision_clean
    (K q : Nat)
    (hChild : HappyCell
      (graph (4^K) 0 (3+q)).seven.carry
      (graph (4^K) 0 (3+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (4^K) 3 (3+j)).seven.carry
      (graph (4^K) 3 (3+j)).seven.digit) :
    False := by
  exact GSTInfiniteFourPowerNavigation.power_three_step_collision K q hChild hRightBad

/-- Clean final Task-A provider.  From exponent `8` onward, the four-power
sheet has a genuine physical Happy cell at a ternary coordinate at least `3`. -/
theorem four_power_happy_ge_three_clean
    (K : Nat) (hK : 8 ≤ K) :
    ∃ p : Nat, 3 ≤ p ∧
      HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  exact GSTInfiniteFourPowerNavigation.four_power_happy_ge_three K hK

/-- Clean creation-master export used by production surgery.  This preserves the
monolith ban on direct `GSTInfiniteFourPowerNavigation` references while still
routing through the independent kernel-checked four-power proof. -/
theorem four_power_creation_master_clean :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  intro K hK5 hK7
  simpa [GSTFourPowerOntologicalAdapter.CreationCertificate] using
    (GSTInfiniteFourPowerNavigation.gst_four_power_navigation_universal K hK5 hK7)

/-- Monolith-mined public theorem name requested by the corrected plan. -/
theorem four_power_happy_ge_three_from_monolith
    (K : Nat) (hK : 8 ≤ K) :
    ∃ p : Nat, 3 ≤ p ∧
      HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  exact four_power_happy_ge_three_clean K hK

end GSTFourPowerHappyGeThreeClean
