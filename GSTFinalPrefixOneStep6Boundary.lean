import GSTU2DSharpCrossingBlock
import GSTGraphV2InfiniteControllerBridge
import GSTPerfectPowerTailNavigation
import GSTGraphV2HandwrittenOmegaUBlock

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFinalPrefixOneStep6Boundary

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTU2DExactCrossingCharge
open GSTPerfectPowerTailNavigation
open GSTGraphV2HandwrittenOmegaUBlock

private def step6C (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.carry

private def step6D (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.digit

/-- Equation (26): the recursive weighted prefix is literally the finite
base-three weighted sum of the horizontal reverse crossing codes. -/
theorem weightedCrossPrefix_eq_sum
    (C d : Nat → Nat → Nat) (N : Nat) : ∀ K : Nat,
    weightedCrossPrefix C d N K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          reverseCrossCode (fun t => C t p) (fun t => d t p) N) := by
  intro K
  induction K with
  | zero => simp [weightedCrossPrefix]
  | succ K ih =>
      rw [weightedCrossPrefix, ih, Finset.sum_range_succ]

/-- Equation (32)/(33), specialized to the canonical finite rectangle.  This
is the exact horizontal-plus-vertical telescope already encoded by the U2D
charge; the microscopic SURVIVE correction is retained explicitly because it
is part of the repository's exact `crossDensity`. -/
theorem canonical_rectangle_boundary_exact
    (s n K : Nat) :
    weightedCrossPrefix (step6C s n) (step6D s n)
        (residualWidth s) K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential (step6D s n (residualWidth s) p) -
            (((4^(residualWidth s) : Nat) : Int)) *
              digitPotential (step6D s n 0 p) +
            84 * reverseSurviveCode (fun t => step6C s n t p)
              (fun t => step6D s n t p) (residualWidth s))) +
      reverseCarryCode (fun t => step6C s n t 0) (residualWidth s) -
        (((3^K : Nat) : Int)) *
          reverseCarryCode (fun t => step6C s n t K) (residualWidth s) := by
  rw [weightedCrossPrefix_eq_sum]
  apply reverseCrossRectangle_exact
  intro t p ht hp
  exact ⟨graph_carry_lt_four (residualEnergy s 1 n) t (s+2+p),
    graph_digit_lt_three (residualEnergy s 1 n) t (s+2+p),
    (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).1,
    by
      simpa [step6C, step6D, Nat.add_assoc] using
        (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).2⟩

/-- The local right-edge controller contribution used in the Step 6 sign
reduction.  This is intentionally the physical crossing sign functional: it
is finite-state and therefore axiom-free. -/
def rightBoundaryGamma (C d : Nat) : Int := crossDensity C d

/-- Equation (35): every physical non-Happy right-boundary state has
non-positive controller/crossing contribution. -/
theorem rightBoundaryGamma_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    rightBoundaryGamma C d ≤ 0 := by
  exact crossDensity_nonpositive_of_not_happy C d hC hd hbad

/-- Finite weighted right-boundary sign consequence of parent badness. -/
theorem right_boundary_weighted_sum_nonpositive
    (s n K : Nat)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        rightBoundaryGamma
          (step6C s n (residualWidth s) p)
          (step6D s n (residualWidth s) p)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro p hp
  apply mul_nonpos_of_nonneg_of_nonpos
  · positivity
  · apply rightBoundaryGamma_nonpositive_of_not_happy
    · exact graph_carry_lt_four (residualEnergy s 1 n) (residualWidth s) (s+2+p)
    · exact graph_digit_lt_three (residualEnergy s 1 n) (residualWidth s) (s+2+p)
    · simpa [step6C, step6D, Nat.add_assoc] using hRightBad p

/-- Equation (34), isolated exactly as the canonical boundary-identification
lemma required by the mathematical Step 6.  Its proof is the only non-local
piece: the exact finite rectangle telescope plus the canonical Infinite
Controller identification must reduce the full rectangle charge to the
physical right-edge controller contributions. -/
theorem canonical_controller_boundary_identification
    (s n K : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    weightedCrossPrefix (step6C s n) (step6D s n)
        (residualWidth s) K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          rightBoundaryGamma
            (step6C s n (residualWidth s) p)
            (step6D s n (residualWidth s) p)) := by
  let E := residualEnergy s 1 n
  let N := residualWidth s
  let b := s + 2
  have hBaseCarryZero : (graph E 0 b).seven.carry = 0 := by
    let T := canonicalTail (s+1) n
    have hE : E = 1 + 3^b * T := by
      have h := canonical_tail_decomposition (s+1) n
      simpa [E, b, T, residualEnergy, Nat.add_assoc] using h
    have hb : 1 < 3^b := by
      have h9 : 9 ≤ 3^b := by
        rw [show (9 : Nat) = 3^2 by decide]
        exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
      omega
    have hmod : E % 3^b = 1 := by
      rw [hE, Nat.add_mod]
      have hmul : (3^b * T) % 3^b = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
      rw [hmul, Nat.add_zero, Nat.mod_eq_of_lt hb]
    have hc : carry4 E b = 0 := by
      unfold carry4
      rw [hmod]
      apply Nat.div_eq_of_lt
      have hb27 : 27 ≤ 3^b := by
        rw [show (27 : Nat) = 3^3 by decide]
        exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
      omega
    simpa [E, b, graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc
  have hController :
      GSTV2.InfiniteBadCoupledControl (4^N) (graphCoupledState E N b) := by
    apply graph_infinite_bad_control E N b hBaseCarryZero
    intro j
    simpa [E, N, b, Nat.add_assoc] using hRightBad j
  have hRect := canonical_rectangle_boundary_exact s n K
  -- This is the exact Step 6 canonical boundary reduction.  Keep every
  -- boundary term visible so Lean, rather than an informal cancellation,
  -- certifies the controller identification.
  dsimp [E, N, b] at hController
  dsimp [step6C, step6D, rightBoundaryGamma] at hRect ⊢
  trace_state
  omega

/-- Equation (37): parent all-depth badness forces the canonical weighted
crossing prefix to be non-positive. -/
theorem canonical_right_bad_forces_weighted_cross_nonpositive
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    weightedCrossPrefix (step6C s n) (step6D s n)
      (residualWidth s) (q+1) ≤ 0 := by
  rw [canonical_controller_boundary_identification s n (q+1) hs hn hRightBad]
  exact right_boundary_weighted_sum_nonpositive s n (q+1) hRightBad

#check weightedCrossPrefix_eq_sum
#check canonical_rectangle_boundary_exact
#check rightBoundaryGamma_nonpositive_of_not_happy
#check right_boundary_weighted_sum_nonpositive
#check canonical_controller_boundary_identification
#check canonical_right_bad_forces_weighted_cross_nonpositive
#print axioms canonical_controller_boundary_identification
#print axioms canonical_right_bad_forces_weighted_cross_nonpositive

end GSTFinalPrefixOneStep6Boundary
