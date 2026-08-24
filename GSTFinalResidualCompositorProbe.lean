import GSTGraphV2ProductionLaws
import GSTU2DSharpCrossingBlock

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2Production
open GSTGraphV2ProductionLaws
open GSTU2DPureDivergence83
open GSTU2DExactCrossingCharge

namespace GSTFinalResidualCompositorProbe

/-- Hard unbounded residual family only: level one, origin trit one.  This probe
contains no legacy Omega termination and no generic perfect-power collision. -/
theorem residual_level_one_origin_one_probe
    (k m q : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm1 : m % 3 = 1)
    (hChild : HappyCell
      (GSTGraphV2InfiniteControl.graph
        (GSTGraphV2Production.residualEnergy 1 k m) 0 (k+2+q)).seven.carry
      (GSTGraphV2InfiniteControl.graph
        (GSTGraphV2Production.residualEnergy 1 k m) 0 (k+2+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (GSTGraphV2InfiniteControl.graph
        (GSTGraphV2Production.residualEnergy 1 k m) 3 (k+2+j)).seven.carry
      (GSTGraphV2InfiniteControl.graph
        (GSTGraphV2Production.residualEnergy 1 k m) 3 (k+2+j)).seven.digit) :
    False := by
  let E := GSTGraphV2Production.residualEnergy 1 k m
  let b := k + 2

  have hWidth := residual_level_one_width k m (b+q)
  have hParentExponent := residual_level_one_parent_exponent k m (b+q)
  have hEnergyStep := residual_level_one_origin_one_energy_step k m (b+q) hm1
  have hNeutral := residual_gate_neutral_tail 1 k m q (by decide) hk
  have hLeftPhased := residual_gate_left_is_phased_tail 1 k m q
  have hRightAbsolute := residual_right_absolute_state_exact 1 k m (b+q)

  have hPositive83 :
      0 < weightedRectanglePrefix83
        (fun t p =>
          (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
        (fun t p =>
          (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
        3 (q+1) := by
    apply weightedRectanglePrefix83_positive_of_top_leading_happy
    · decide
    · intro t p ht hp
      exact graph_carry_lt_four E t (b+p)
    · intro t p ht hp
      exact graph_digit_lt_three E t (b+p)
    · simpa [E, b, Nat.add_assoc] using hChild

  have hExact83 := density83_rectangle_exact
    (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
    (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
    3 (q+1)
    (by
      intro t p ht hp
      exact ⟨graph_carry_lt_four E t (b+p),
        graph_digit_lt_three E t (b+p),
        (graph_cell_exact E t (b+p)).1,
        by simpa [Nat.add_assoc] using (graph_cell_exact E t (b+p)).2⟩)

  have hCrossPositive :
      0 < GSTU2DExactCrossingCharge.weightedCrossPrefix
        (fun t p =>
          (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
        (fun t p =>
          (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
        3 (q+1) := by
    apply GSTU2DExactCrossingCharge.weightedCrossPrefix_positive_of_top_leading_happy
    · decide
    · intro t p ht hp
      exact graph_carry_lt_four E t (b+p)
    · intro t p ht hp
      exact graph_digit_lt_three E t (b+p)
    · intro t p ht hp
      exact (graph_cell_exact E t (b+p)).1
    · simpa [E, b, Nat.add_assoc] using hChild

  have hCrossExact := GSTU2DExactCrossingCharge.reverseCrossRectangle_exact
    (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
    (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
    3 (q+1)
    (by
      intro t p ht hp
      exact ⟨graph_carry_lt_four E t (b+p),
        graph_digit_lt_three E t (b+p),
        (graph_cell_exact E t (b+p)).1,
        by simpa [Nat.add_assoc] using (graph_cell_exact E t (b+p)).2⟩)

  trace_state
  omega

end GSTFinalResidualCompositorProbe
