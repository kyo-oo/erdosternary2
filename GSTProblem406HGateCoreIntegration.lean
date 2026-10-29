import GSTProblem406HGateCoreClass
import GSTFourPowerThirdWave
import GSTFourPowerDirectCreationMaster

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Direct extraction into the exact original hGate type

Proof of the original hGate BODY (thirdWave K) on infinite
congruence-class source families, with no hGate assumption.
It directly supplies original CreationCertificate on those K.

Universal hGate is not claimed: remaining K must be discharged.
-/

namespace GSTProblem406HGateCoreIntegration

open GSTFourPowerDirectExistence
open GSTProblem406HGateCoreClass

theorem original_hGate_on_unbounded_core
    (L u : Nat) (hL : 6 ≤ L) (h3 : u%3≠0)
    (h4 : u%27≠4) (h10 : u%27≠10)
    (h13 : u%27≠13) (h16 : u%27≠16)
    (h19 : u%27≠19) (h22 : u%27≠22)
    (h25 : u%27≠25) :
    GSTFourPowerThirdWave.thirdWave (4+u*3^L) := by
  apply (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
  exact commonTwo_unbounded_core_classes L u hL h3
    h4 h10 h13 h16 h19 h22 h25

theorem original_creation_master_on_unbounded_core
    (L u : Nat) (hL : 6 ≤ L) (h3 : u%3≠0)
    (h4 : u%27≠4) (h10 : u%27≠10)
    (h13 : u%27≠13) (h16 : u%27≠16)
    (h19 : u%27≠19) (h22 : u%27≠22)
    (h25 : u%27≠25) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^(4+u*3^L)) := by
  apply GSTFourPowerDirectCreationMaster.commonTwo_to_creation_certificate
  exact commonTwo_unbounded_core_classes L u hL h3
    h4 h10 h13 h16 h19 h22 h25

#print axioms original_hGate_on_unbounded_core
#print axioms original_creation_master_on_unbounded_core

end GSTProblem406HGateCoreIntegration
