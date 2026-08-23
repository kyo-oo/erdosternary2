import GSTGraphV2PerfectPowerAncestry
import GSTU2DCanonicalPhaseDensity
import GSTGraphV2UnifiedPowerRectangle
import GSTGraphV2UnifiedVerticalTelescope

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2PerfectPowerBlock

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTU2DCanonicalPhaseDensity
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope

/-- The canonical full energy and the exact horizontal perfect-power width. -/
def canonicalEnergy (s n : Nat) : Nat := 4^(3^(s+1) * n)
def canonicalWidth (s : Nat) : Nat := 3^s

/-- A Happy cell on any column of the main Graph-V2 sheet creates strictly
positive base-three weighted phase pressure below and including that row. -/
theorem graph_phase_prefix_positive_of_happy
    (E t q : Nat)
    (hHappy : HappyCell
      (graph E t q).seven.carry
      (graph E t q).seven.digit) :
    0 < weightedPhaseColumnPrefix
      (fun p => (graph E t p).seven.carry)
      (fun p => (graph E t p).seven.digit) (q+1) := by
  apply weightedPhaseColumnPrefix_positive_of_top_happy
  · intro p hp
    exact graph_carry_lt_four E t p
  · intro p hp
    exact graph_digit_lt_three E t p
  · exact hHappy

/-- Conversely, a genuinely bad Graph-V2 column has nonpositive weighted
phase pressure at every finite observation height.  No support or terminal
hypothesis appears: `K` is an arbitrary observation height. -/
theorem graph_phase_prefix_nonpositive_of_bad
    (E t K : Nat)
    (hBad : ∀ p, p < K → ¬ HappyCell
      (graph E t p).seven.carry
      (graph E t p).seven.digit) :
    weightedPhaseColumnPrefix
      (fun p => (graph E t p).seven.carry)
      (fun p => (graph E t p).seven.digit) K ≤ 0 := by
  induction K with
  | zero =>
      simp [weightedPhaseColumnPrefix]
  | succ K ih =>
      have ih' := ih (fun p hp => hBad p (by omega))
      have hlocal :
          phaseDensity
              (graph E t K).seven.carry
              (graph E t K).seven.digit ≤ 0 :=
        phaseDensity_nonpositive_of_not_happy
          (graph E t K).seven.carry
          (graph E t K).seven.digit
          (graph_carry_lt_four E t K)
          (graph_digit_lt_three E t K)
          (hBad K (by omega))
      have hw : (0 : Int) ≤ (((3^K : Nat) : Int)) := by positivity
      rw [weightedPhaseColumnPrefix]
      exact add_nonpos ih' (mul_nonpos_of_nonneg_of_nonpos hw hlocal)

/-- Exact reconstruction of the first `K` ternary digits.  This is the
arithmetic boundary identity needed to turn the phase-density divergence into
an equality of literal residues of the same perfect-power sheet. -/
theorem digit3_weighted_prefix_nat (R K : Nat) :
    Finset.sum (Finset.range K) (fun p => 3^p * digit3 R p) =
      R % 3^K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Nat.pow_succ]
      unfold digit3
      rw [Nat.mod_mul]

/-- Integer chart of the same exact ternary-prefix reconstruction. -/
theorem digit3_weighted_prefix_int (R K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * ((digit3 R p : Nat) : Int)) =
        ((R % 3^K : Nat) : Int) := by
  exact_mod_cast digit3_weighted_prefix_nat R K

/-- Graph digits are literal ternary digits of `4^t * E`; hence their weighted
prefix is exactly the corresponding residue of that one arithmetic energy. -/
theorem graph_digit_weighted_prefix_exact (E t K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * (((graph E t p).seven.digit : Nat) : Int)) =
        (((4^t * E) % 3^K : Nat) : Int) := by
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using
    digit3_weighted_prefix_int (4^t * E) K

/-- The exact phase-column divergence specialized to the main infinite graph.
This is the conservation equation used by the perfect-power regeneration step. -/
theorem graph_phase_column_exact (E t K : Nat) :
    weightedPhaseColumnPrefix
        (fun p => (graph E t p).seven.carry)
        (fun p => (graph E t p).seven.digit) K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (phaseDigitPotential (graph E (t+1) p).seven.digit -
           phaseDigitPotential (graph E t p).seven.digit)) +
      phaseCarryPotential (graph E t 0).seven.carry -
        (((3^K : Nat) : Int)) *
          phaseCarryPotential (graph E t K).seven.carry +
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          surviveI (graph E t p).seven.carry (graph E t p).seven.digit) := by
  apply phaseColumn_exact
  intro p hp
  exact ⟨graph_carry_lt_four E t p,
    graph_digit_lt_three E t p,
    (graph_cell_exact E t p).1,
    (graph_cell_exact E t p).2⟩

/-- Perfect-power ancestry can be used at the block level without changing any
physical Happy observable. -/
theorem canonical_power_origin_happy_iff
    (s n t p : Nat) :
    HappyCell
        (graph (canonicalEnergy s n) t p).seven.carry
        (graph (canonicalEnergy s n) t p).seven.digit ↔
      HappyCell
        (graph 1 (3^(s+1) * n + t) p).seven.carry
        (graph 1 (3^(s+1) * n + t) p).seven.digit := by
  simpa [canonicalEnergy] using
    GSTGraphV2PerfectPowerAncestry.power_origin_happy_iff
      (3^(s+1) * n) t p

#check graph_phase_prefix_positive_of_happy
#check graph_phase_prefix_nonpositive_of_bad
#check digit3_weighted_prefix_nat
#check graph_digit_weighted_prefix_exact
#check graph_phase_column_exact
#check canonical_power_origin_happy_iff
#print axioms graph_phase_prefix_positive_of_happy
#print axioms graph_phase_prefix_nonpositive_of_bad
#print axioms graph_phase_column_exact
#print axioms canonical_power_origin_happy_iff

end GSTGraphV2PerfectPowerBlock
