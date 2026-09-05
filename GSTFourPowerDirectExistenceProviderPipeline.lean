import GSTFourPowerDirectExistenceNoAxiom
import GSTFourPowerDirectCreationMaster
import GSTFourPowerOntologicalAdapter
import GSTFourPowerDirectChat2Application

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Provider pipeline for replacing the four-power direct-existence boundary

This file is the controlled next phase after the isolated bridge compiled green.
It does not edit the monolith and adds no unchecked proof hole.

It now exposes both legitimate proof gates:

* `FourPowerHappyGeThreeProvider`, the physical Happy-row provider originally
  needed by the isolated bridge; and
* `FourPowerDirectNoCounterexampleClosure`, the Chat-2 realization: close the
  direct `CommonTwo` counterexample language produced by the affine/residue/
  exponent-prefix surfaces.

The second gate is the corrected roadmap route.  It avoids the abandoned
future-only Happy propagation path and does not import the unresolved infinite
navigation collision file.
-/

namespace GSTFourPowerDirectExistenceProviderPipeline

open GSTFourPowerDirectExistence
open GSTFourPowerDirectExistenceNoAxiom
open GSTFourPowerDirectChat2Application

/-- Goal A: a theorem-backed physical Happy-row provider for every `K ≥ 8`.
This is sufficient for the already-green bridge, but it is not the only route. -/
def FourPowerHappyGeThreeProvider : Prop :=
  ∀ K : Nat, 8 ≤ K →
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)

/-- Goal B / Chat-2 gate: close the direct arithmetic counterexample language.
This is the productive route after the failed future-only relocation subgoal:
prove there is no genuine `CommonTwo` counterexample for `K ≥ 5`, except the
single excluded exponent `7`. -/
def FourPowerDirectNoCounterexampleClosure : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬¬ CommonTwo K

/-- The already-green isolated bridge converts Goal A into the closed
`FourPowerDirectExistence` theorem. -/
theorem fourPowerDirectExistence_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider) :
    FourPowerDirectExistence := by
  exact fourPowerDirectExistence_from_physical_happy_ge_three hProvider

/-- Chat-2 production gate: once the affine/exponent-prefix counterexample
language is closed, the direct universal theorem follows immediately. -/
theorem fourPowerDirectExistence_noAxiom_from_chat2_closure
    (hClosed : FourPowerDirectNoCounterexampleClosure) :
    FourPowerDirectExistence := by
  exact chat2_fourPowerDirectExistence_from_no_counterexample hClosed

/-- Chat-2 obstruction export: every attempted counterexample now carries the
combined row-two, row-three, row-four, and parametric exponent-prefix
obstructions from the direct theorem layer. -/
theorem chat2_counterexample_obstruction_from_pipeline
    (K : Nat) (hNo : ¬ CommonTwo K) :
    (K % 9 ≠ 5 ∧ K % 9 ≠ 6) ∧
    (K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25) ∧
    (¬ GSTFourPowerDirectResidue81.RowFourClass (K % 81)) ∧
    (∀ p : Nat,
      GSTFourPowerDirectResidue.digit3 (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1) =
        GSTFourPowerDirectResidue.digit3 (4^((GSTFourPowerExponentTritObstruction.exponentPrefix K p)+1)) (p+1) →
      GSTFourPowerExponentTritObstruction.exponentTrit K p ≠
        2 - GSTFourPowerDirectResidue.digit3 (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1)) := by
  exact chat2_counterexample_obstruction_bundle K hNo

/-- Once Goal A is theorem-backed, the existing direct creation master follows
without the old production boundary. -/
theorem fourPowerCreationMaster_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      (fourPowerDirectExistence_noAxiom_from_provider hProvider)

/-- Chat-2 creation master route: this is the direct replacement route for the
old monolith-facing boundary once `FourPowerDirectNoCounterexampleClosure` is
proved. -/
theorem fourPowerCreationMaster_noAxiom_from_chat2_closure
    (hClosed : FourPowerDirectNoCounterexampleClosure) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      (fourPowerDirectExistence_noAxiom_from_chat2_closure hClosed)

/-- Transplant-ready certificate wrapper for the original Happy-provider gate. -/
theorem fourPowerCreationCertificate_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (fourPowerCreationMaster_noAxiom_from_provider hProvider) K hK5 hK7

/-- Transplant-ready certificate wrapper for the Chat-2 direct closure gate. -/
theorem fourPowerCreationCertificate_noAxiom_from_chat2_closure
    (hClosed : FourPowerDirectNoCounterexampleClosure)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (fourPowerCreationMaster_noAxiom_from_chat2_closure hClosed) K hK5 hK7

#check FourPowerHappyGeThreeProvider
#check FourPowerDirectNoCounterexampleClosure
#check fourPowerDirectExistence_noAxiom_from_provider
#check fourPowerDirectExistence_noAxiom_from_chat2_closure
#check chat2_counterexample_obstruction_from_pipeline
#check fourPowerCreationMaster_noAxiom_from_provider
#check fourPowerCreationMaster_noAxiom_from_chat2_closure
#check fourPowerCreationCertificate_noAxiom_from_provider
#check fourPowerCreationCertificate_noAxiom_from_chat2_closure
#print axioms fourPowerDirectExistence_noAxiom_from_provider
#print axioms fourPowerDirectExistence_noAxiom_from_chat2_closure
#print axioms chat2_counterexample_obstruction_from_pipeline
#print axioms fourPowerCreationMaster_noAxiom_from_provider
#print axioms fourPowerCreationMaster_noAxiom_from_chat2_closure
#print axioms fourPowerCreationCertificate_noAxiom_from_provider
#print axioms fourPowerCreationCertificate_noAxiom_from_chat2_closure

end GSTFourPowerDirectExistenceProviderPipeline
