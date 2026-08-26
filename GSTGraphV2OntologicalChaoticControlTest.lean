import GSTGraphV2OntologicalChaoticControl

open GSTGraphV2NonEuclidean
open GSTGraphV2OntologicalChaoticControl

example (E H t p : Nat) :
    WitnessAt (physicalProjection E H t p) ↔
      InfiniteChaoticControlAt E t p := by
  exact ambient_witness_iff_infinite_chaotic_control E H t p

example (R H : Nat) :
    HistoricalCreationCertificate R ↔
      AmbientInfiniteNavigation R H := by
  exact historical_creation_iff_ambient_infinite_navigation R H
