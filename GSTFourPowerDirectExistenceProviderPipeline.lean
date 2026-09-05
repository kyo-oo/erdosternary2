import GSTFourPowerDirectExistenceNoAxiom
import GSTFourPowerDirectCreationMaster
import GSTFourPowerOntologicalAdapter

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Provider pipeline for replacing the four-power direct-existence boundary

This file is the controlled next phase after the isolated bridge compiled green.
It does not edit the monolith and adds no unchecked proof hole.

It names the exact remaining provider theorem as a Prop-level seam:

`FourPowerHappyGeThreeProvider`

and proves that this provider is sufficient to recover the closed direct
existence theorem and the existing creation-master/certificate pipeline.
-/

namespace GSTFourPowerDirectExistenceProviderPipeline

open GSTFourPowerDirectExistence
open GSTFourPowerDirectExistenceNoAxiom

/-- Goal A: a theorem-backed physical Happy-row provider for every `K ≥ 8`.
This is the exact missing mathematical provider needed before the production
boundary can be deleted safely. -/
def FourPowerHappyGeThreeProvider : Prop :=
  ∀ K : Nat, 8 ≤ K →
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)

/-- Goal B: the already-green isolated bridge converts Goal A into the closed
`FourPowerDirectExistence` theorem. -/
theorem fourPowerDirectExistence_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider) :
    FourPowerDirectExistence := by
  exact fourPowerDirectExistence_from_physical_happy_ge_three hProvider

/-- Once Goal A is theorem-backed, the existing direct creation master follows
without the old production boundary. -/
theorem fourPowerCreationMaster_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      (fourPowerDirectExistence_noAxiom_from_provider hProvider)

/-- Transplant-ready certificate wrapper.  This matches the old monolith-facing
certificate API, but keeps the remaining provider requirement explicit instead
of hiding it. -/
theorem fourPowerCreationCertificate_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (fourPowerCreationMaster_noAxiom_from_provider hProvider) K hK5 hK7

#check FourPowerHappyGeThreeProvider
#check fourPowerDirectExistence_noAxiom_from_provider
#check fourPowerCreationMaster_noAxiom_from_provider
#check fourPowerCreationCertificate_noAxiom_from_provider
#print axioms fourPowerDirectExistence_noAxiom_from_provider
#print axioms fourPowerCreationMaster_noAxiom_from_provider
#print axioms fourPowerCreationCertificate_noAxiom_from_provider

end GSTFourPowerDirectExistenceProviderPipeline
