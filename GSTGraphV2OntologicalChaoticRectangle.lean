import GSTGraphV2OntologicalChaoticControl
import GSTU2DPureDivergence83

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2OntologicalChaoticRectangle

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2NonEuclidean
open GSTGraphV2NonEuclideanLaws
open GSTU2DPureDivergence83
open GSTGraphV2OntologicalChaoticControl

/-- The genuine two-dimensional 8×3 divergence observable on the ontological
GST graph.  Horizontal index `j` advances the x4 chart phase; vertical index
`p` remains the true seven-axis ternary coordinate. -/
def ontologicalRectangle83 (E t N K : Nat) : Int :=
  weightedRectanglePrefix83
    (fun j p => (graph E (t+j) p).seven.carry)
    (fun j p => (graph E (t+j) p).seven.digit)
    N K

/-- If every physical cell in one horizontal orbit segment is non-Happy, its
reverse 8-density cannot become positive.  This is the horizontal half of the
ontological bad-rectangle exclusion. -/
theorem reverseDensity83_nonpositive_of_all_bad
    (C d : Nat → Nat) : ∀ N : Nat,
    (∀ j, j < N → C j < 4) →
    (∀ j, j < N → d j < 3) →
    (∀ j, j < N → ¬ HappyCell (C j) (d j)) →
    reverseDensity83 C d N ≤ 0 := by
  intro N
  induction N with
  | zero =>
      intro _hC _hd _hbad
      simp [reverseDensity83]
  | succ N ih =>
      intro hC hd hbad
      have ih' := ih
        (fun j hj => hC j (by omega))
        (fun j hj => hd j (by omega))
        (fun j hj => hbad j (by omega))
      have hlocal : density83 (C N) (d N) ≤ 0 :=
        density83_nonpositive_of_not_happy
          (C N) (d N)
          (hC N (by omega))
          (hd N (by omega))
          (hbad N (by omega))
      rw [reverseDensity83]
      omega

/-- If every cell of an N×K ontological rectangle is non-Happy, then the full
8-horizontal × 3-vertical weighted density is nonpositive. Positive density
therefore cannot be manufactured by ALT-minus / NULL / GST-plus bad cells. -/
theorem weightedRectanglePrefix83_nonpositive_of_all_bad
    (C d : Nat → Nat → Nat) (N : Nat) : ∀ K : Nat,
    (∀ j p, j < N → p < K → C j p < 4) →
    (∀ j p, j < N → p < K → d j p < 3) →
    (∀ j p, j < N → p < K → ¬ HappyCell (C j p) (d j p)) →
    weightedRectanglePrefix83 C d N K ≤ 0 := by
  intro K
  induction K with
  | zero =>
      intro _hC _hd _hbad
      simp [weightedRectanglePrefix83]
  | succ K ih =>
      intro hC hd hbad
      have ih' := ih
        (fun j p hj hp => hC j p hj (by omega))
        (fun j p hj hp => hd j p hj (by omega))
        (fun j p hj hp => hbad j p hj (by omega))
      have hcolumn :
          reverseDensity83 (fun j => C j K) (fun j => d j K) N ≤ 0 :=
        reverseDensity83_nonpositive_of_all_bad
          (fun j => C j K) (fun j => d j K) N
          (fun j hj => hC j K hj (by omega))
          (fun j hj => hd j K hj (by omega))
          (fun j hj => hbad j K hj (by omega))
      have hweight :
          (0 : Int) ≤ (((3^K : Nat) : Int)) := by positivity
      have hweighted :
          (((3^K : Nat) : Int)) *
              reverseDensity83 (fun j => C j K) (fun j => d j K) N ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hweight hcolumn
      rw [weightedRectanglePrefix83]
      omega

/-- One true ambient seven-axis witness at the leading horizontal phase forces
strictly positive density in every nonempty future 8×3 rectangle whose vertical
top reaches that witness. -/
theorem ambient_witness_forces_rectangle83_positive
    (E H t q N : Nat)
    (hN : 1 ≤ N)
    (hW : WitnessAt (physicalProjection E H t q)) :
    0 < ontologicalRectangle83 E t N (q+1) := by
  have hHappy :
      HappyCell (graph E t q).seven.carry
        (graph E t q).seven.digit :=
    (physical_happy_iff_ambient_witness E H t q).2 hW
  unfold ontologicalRectangle83
  apply weightedRectanglePrefix83_positive_of_top_leading_happy
    (C := fun j p => (graph E (t+j) p).seven.carry)
    (d := fun j p => (graph E (t+j) p).seven.digit)
    N q hN
  · intro j p _hj _hp
    exact graph_carry_lt_four E (t+j) p
  · intro j p _hj _hp
    exact graph_digit_lt_three E (t+j) p
  · simpa using hHappy

/-- Positivity of the full ontological 8×3 rectangle is an existence detector:
it certifies that some genuine seven-axis vertex in that rectangle lies in
NULL/GST+ with digit two. -/
theorem rectangle83_positive_contains_ambient_witness
    (E H t N K : Nat)
    (hpos : 0 < ontologicalRectangle83 E t N K) :
    ∃ j p, j < N ∧ p < K ∧
      WitnessAt (physicalProjection E H (t+j) p) := by
  by_contra hnone
  have hbad : ∀ j p, j < N → p < K →
      ¬ HappyCell (graph E (t+j) p).seven.carry
        (graph E (t+j) p).seven.digit := by
    intro j p hj hp hHappy
    apply hnone
    exact ⟨j, p, hj, hp,
      (physical_happy_iff_ambient_witness E H (t+j) p).1 hHappy⟩
  have hnonpos : ontologicalRectangle83 E t N K ≤ 0 := by
    unfold ontologicalRectangle83
    exact weightedRectanglePrefix83_nonpositive_of_all_bad
      (C := fun j p => (graph E (t+j) p).seven.carry)
      (d := fun j p => (graph E (t+j) p).seven.digit)
      N K
      (fun j p _hj _hp => graph_carry_lt_four E (t+j) p)
      (fun j p _hj _hp => graph_digit_lt_three E (t+j) p)
      hbad
  omega

/-- A compact host-graph consequence: every ambient witness generates, for all
future nonempty horizontal widths, a positive ontological rectangle; every one
of those positive rectangles in turn contains a true ambient witness. -/
theorem ambient_witness_generates_positive_rectangle_family
    (E H t q : Nat)
    (hW : WitnessAt (physicalProjection E H t q)) :
    ∀ N : Nat, 1 ≤ N →
      0 < ontologicalRectangle83 E t N (q+1) ∧
      ∃ j p, j < N ∧ p < q+1 ∧
        WitnessAt (physicalProjection E H (t+j) p) := by
  intro N hN
  have hpos := ambient_witness_forces_rectangle83_positive E H t q N hN hW
  exact ⟨hpos,
    rectangle83_positive_contains_ambient_witness E H t N (q+1) hpos⟩

#check reverseDensity83_nonpositive_of_all_bad
#check weightedRectanglePrefix83_nonpositive_of_all_bad
#check ambient_witness_forces_rectangle83_positive
#check rectangle83_positive_contains_ambient_witness
#check ambient_witness_generates_positive_rectangle_family

end GSTGraphV2OntologicalChaoticRectangle