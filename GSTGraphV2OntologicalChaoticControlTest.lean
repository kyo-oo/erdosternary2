import GSTGraphV2OntologicalChaoticControl
import GSTGraphV2OntologicalChaoticRectangle

open GSTGraphV2NonEuclidean
open GSTGraphV2OntologicalChaoticControl
open GSTGraphV2OntologicalChaoticRectangle

example (E H t p : Nat) :
    WitnessAt (physicalProjection E H t p) ↔
      InfiniteChaoticControlAt E t p := by
  exact ambient_witness_iff_infinite_chaotic_control E H t p

example (R H : Nat) :
    HistoricalCreationCertificate R ↔
      AmbientInfiniteNavigation R H := by
  exact historical_creation_iff_ambient_infinite_navigation R H

example (E H t q N : Nat)
    (hN : 1 ≤ N)
    (hW : WitnessAt (physicalProjection E H t q)) :
    0 < ontologicalRectangle83 E t N (q+1) := by
  exact ambient_witness_forces_rectangle83_positive E H t q N hN hW

example (E H t N K : Nat)
    (hpos : 0 < ontologicalRectangle83 E t N K) :
    ∃ j p, j < N ∧ p < K ∧
      WitnessAt (physicalProjection E H (t+j) p) := by
  exact rectangle83_positive_contains_ambient_witness E H t N K hpos
