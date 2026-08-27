import GSTGraphV2NonEuclideanLaws
import GSTU2DExactCrossingCharge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2OntologicalChaoticControl

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTU2DExactCrossingCharge
open GSTGraphV2InfiniteControl
open GSTGraphV2NonEuclidean
open GSTGraphV2NonEuclideanLaws

/-- Reverse horizontal crossing information along the true GST physical
projection, starting at x4 phase `t` and fixed ternary coordinate `p`. -/
def ontologicalReverseCross (E t p N : Nat) : Int :=
  reverseCrossCode
    (fun j => (graph E (t+j) p).seven.carry)
    (fun j => (graph E (t+j) p).seven.digit) N

/-- Infinite chaotic control at one ambient vertex: its horizontal orbit
retains the sharp exponential no-erasure lower envelope at every future width. -/
def InfiniteChaoticControlAt (E t p : Nat) : Prop :=
  ∀ N : Nat, 1 ≤ N →
    17 * (((4^N : Nat) : Int)) + 37 ≤ ontologicalReverseCross E t p N

/-- In the true seven-axis graph, ambient witnesshood is exactly positivity of
the enriched exact crossing observable. -/
theorem ambient_witness_iff_crossing_positive (E H t p : Nat) :
    WitnessAt (physicalProjection E H t p) ↔
      0 < (graph E t p).crossingCharge := by
  constructor
  · intro hW
    have hHappy :=
      (physical_happy_iff_ambient_witness E H t p).2 hW
    exact (graph_happy_iff_crossing_positive E t p).1 hHappy
  · intro hpos
    have hHappy :=
      (graph_happy_iff_crossing_positive E t p).2 hpos
    exact (physical_happy_iff_ambient_witness E H t p).1 hHappy

/-- Main ontological identity. A seven-axis witness is not merely a local
carry/digit event: it is exactly a vertex whose complete future x4 orbit
carries an exponentially non-erasable crossing-information signature. -/
theorem ambient_witness_iff_infinite_chaotic_control
    (E H t p : Nat) :
    WitnessAt (physicalProjection E H t p) ↔
      InfiniteChaoticControlAt E t p := by
  constructor
  · intro hW N hN
    have hHappy :
        HappyCell (graph E t p).seven.carry
          (graph E t p).seven.digit :=
      (physical_happy_iff_ambient_witness E H t p).2 hW
    have hLead :
        HappyCell
          ((fun j => (graph E (t+j) p).seven.carry) 0)
          ((fun j => (graph E (t+j) p).seven.digit) 0) := by
      simpa using hHappy
    exact reverseCrossCode_ge_exponential_of_leading_happy
      (fun j => (graph E (t+j) p).seven.carry)
      (fun j => (graph E (t+j) p).seven.digit)
      hLead N hN
      (fun j _ => graph_carry_lt_four E (t+j) p)
      (fun j _ => graph_digit_lt_three E (t+j) p)
  · intro hControl
    have h1 := hControl 1 (by decide)
    have h105 :
        (105 : Int) ≤
          crossDensity (graph E t p).seven.carry
            (graph E t p).seven.digit := by
      simpa [InfiniteChaoticControlAt, ontologicalReverseCross,
        reverseCrossCode] using h1
    have hpos :
        0 < crossDensity (graph E t p).seven.carry
          (graph E t p).seven.digit := by
      omega
    have hHappy :
        HappyCell (graph E t p).seven.carry
          (graph E t p).seven.digit :=
      (happy_iff_crossDensity_positive
        (graph E t p).seven.carry
        (graph E t p).seven.digit
        (graph_carry_lt_four E t p)
        (graph_digit_lt_three E t p)).2 hpos
    exact (physical_happy_iff_ambient_witness E H t p).1 hHappy

/-- Direct host-graph form at horizontal phase zero. -/
theorem axes_witness_iff_infinite_chaotic_control
    (R H p : Nat) :
    WitnessAt (axes R H p) ↔ InfiniteChaoticControlAt R 0 p := by
  simpa [physicalProjection] using
    (ambient_witness_iff_infinite_chaotic_control R H 0 p)

/-- The true ambient witness classifier is exactly the old Happy predicate,
expressed directly on the seven-axis vertex rather than on a subgraph cell. -/
theorem axes_witness_iff_happy (R H p : Nat) :
    WitnessAt (axes R H p) ↔ HappyCell (carry4 R p) (digit3 R p) := by
  change
    (digit3 R p = 2 ∧
      (GSTGraphV2NonEuclidean.spaceOfCarry (carry4 R p) =
          GSTGraphV2NonEuclidean.Space.null ∨
       GSTGraphV2NonEuclidean.spaceOfCarry (carry4 R p) =
          GSTGraphV2NonEuclidean.Space.gstPlus)) ↔
      (digit3 R p = 2 ∧ (carry4 R p = 0 ∨ carry4 R p = 3))
  by_cases h0 : carry4 R p = 0
  · simp [GSTGraphV2NonEuclidean.spaceOfCarry, h0]
  · by_cases h3 : carry4 R p = 3
    · simp [GSTGraphV2NonEuclidean.spaceOfCarry, h0, h3]
    · simp [GSTGraphV2NonEuclidean.spaceOfCarry, h0, h3]

/-- Physical carry is always one of the four ontological y-axis states. -/
theorem carry4_lt_four_exact (R p : Nat) : carry4 R p < 4 := by
  unfold carry4
  have hpos : 0 < 3^p := Nat.pow_pos (by decide)
  have hmod : R % 3^p < 3^p := Nat.mod_lt R hpos
  exact Nat.div_lt_of_lt_mul (by omega)

/-- Exact historical certificate contract, written with the canonical digit and
carry coordinates.  This is definitionally the old `h_creation` proposition. -/
def HistoricalCreationCertificate (R : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧ digit3 R p = 2 ∧
    (carry4 R p % 3 = 0 ∨
      (carry4 R p % 3 = 1 ∧ digit3 R (p+1) = 2))

/-- The old two-branch creation certificate is exactly existence of a Happy
vertex.  The carry-one branch advances one exact vertical edge and becomes
GST+; therefore it is not a separate ontological phenomenon. -/
theorem historical_creation_iff_exists_happy (R : Nat) :
    HistoricalCreationCertificate R ↔
      ∃ p : Nat, 1 ≤ p ∧ HappyCell (carry4 R p) (digit3 R p) := by
  constructor
  · rintro ⟨p, hp, hd, hcase⟩
    rcases hcase with h0 | ⟨h1, hdNext⟩
    · have hlt := carry4_lt_four_exact R p
      have hgood : carry4 R p = 0 ∨ carry4 R p = 3 := by
        omega
      exact ⟨p, hp, ⟨hd, hgood⟩⟩
    · have hlt := carry4_lt_four_exact R p
      have hC1 : carry4 R p = 1 := by
        omega
      have hCNext : carry4 R (p+1) = 3 := by
        rw [carry4_forward_exact R p, hC1, hd]
        norm_num [nextCarry]
      exact ⟨p+1, by omega, ⟨hdNext, Or.inr hCNext⟩⟩
  · rintro ⟨p, hp, ⟨hd, hgood⟩⟩
    refine ⟨p, hp, hd, Or.inl ?_⟩
    rcases hgood with h0 | h3
    · simp [h0]
    · simp [h3]

/-- Fully ontological replacement API.  A historical creation certificate is
exactly existence of a positive-position seven-axis witness carrying its full
infinite chaotic-control signature. -/
def AmbientInfiniteNavigation (R H : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧
    WitnessAt (axes R H p) ∧ InfiniteChaoticControlAt R 0 p

/-- Exact API inversion from historical creation syntax to the true ambient
GST Graph V2 existence-space statement. -/
theorem historical_creation_iff_ambient_infinite_navigation
    (R H : Nat) :
    HistoricalCreationCertificate R ↔ AmbientInfiniteNavigation R H := by
  constructor
  · intro hCreation
    obtain ⟨p, hp, hHappy⟩ :=
      (historical_creation_iff_exists_happy R).1 hCreation
    have hW : WitnessAt (axes R H p) :=
      (axes_witness_iff_happy R H p).2 hHappy
    have hControl : InfiniteChaoticControlAt R 0 p :=
      (axes_witness_iff_infinite_chaotic_control R H p).1 hW
    exact ⟨p, hp, hW, hControl⟩
  · rintro ⟨p, hp, hW, _hControl⟩
    have hHappy : HappyCell (carry4 R p) (digit3 R p) :=
      (axes_witness_iff_happy R H p).1 hW
    exact (historical_creation_iff_exists_happy R).2 ⟨p, hp, hHappy⟩

/-- Exact raw-arithmetic spelling of the historical contract. -/
theorem historical_creation_raw_iff (R : Nat) :
    (∃ p : Nat, 1 ≤ p ∧ R / 3^p % 3 = 2 ∧
      ((4 * (R % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * (R % 3^p)) / 3^p % 3 = 1 ∧
        R / 3^(p+1) % 3 = 2))) ↔
      HistoricalCreationCertificate R := by
  rfl

/-- The universal four-power target, now stated entirely in the true
seven-axis existence space.  The natural horizon `2*k` is retained as the
ambient z' boundary coordinate. -/
def FourPowerOntologicalChaoticControl : Prop :=
  ∀ k : Nat, 5 ≤ k → k ≠ 7 →
    AmbientInfiniteNavigation (4^k) (2*k)

/-- The ontological master target is logically exact: it is neither stronger
nor weaker than the historical universal creation family. -/
theorem four_power_ontological_master_iff_historical :
    FourPowerOntologicalChaoticControl ↔
      ∀ k : Nat, 5 ≤ k → k ≠ 7 → HistoricalCreationCertificate (4^k) := by
  constructor
  · intro h k hk5 hk7
    exact (historical_creation_iff_ambient_infinite_navigation
      (4^k) (2*k)).2 (h k hk5 hk7)
  · intro h k hk5 hk7
    exact (historical_creation_iff_ambient_infinite_navigation
      (4^k) (2*k)).1 (h k hk5 hk7)

#check ambient_witness_iff_crossing_positive
#check ambient_witness_iff_infinite_chaotic_control
#check historical_creation_iff_exists_happy
#check historical_creation_iff_ambient_infinite_navigation
#check four_power_ontological_master_iff_historical

end GSTGraphV2OntologicalChaoticControl
