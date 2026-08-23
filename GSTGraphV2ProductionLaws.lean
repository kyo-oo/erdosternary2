import GSTGraphV2Production
import GSTGraphV2HandwrittenExponentialLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2ProductionLaws

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2Production
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2HandwrittenExponentialCascade
open GSTGraphV2HandwrittenExponentialLTE

/-- The horizontal edge of the production lattice is the exact x4 digit edge. -/
theorem horizontal_digit_exact (E t p : Nat) :
    outDigit (cell E t p).seven.carry (cell E t p).seven.digit =
      (cell E (t+1) p).seven.digit := by
  simpa [GSTGraphV2Production.cell] using
    (GSTGraphV2InfiniteControl.graph_cell_exact E t p).1

/-- The vertical edge of the production lattice is the exact ternary carry edge. -/
theorem vertical_carry_exact (E t p : Nat) :
    nextCarry (cell E t p).seven.carry (cell E t p).seven.digit =
      (cell E t (p+1)).seven.carry := by
  simpa [GSTGraphV2Production.cell] using
    (GSTGraphV2InfiniteControl.graph_cell_exact E t p).2

/-- Equation I is literally one coordinate identity of each production cell. -/
theorem navigation_nullspace_flux_exact (E t p : Nat) :
    4 * ((cell E t p).absoluteEnergy % 3^p) =
      (cell E t p).navigationNullspace +
        3^p * (cell E t p).seven.carry := by
  simpa [GSTGraphV2Production.cell] using
    GSTGraphV2HandwrittenExponentialCascade.graph_navigation_nullspace_flux_exact
      E t p

/-- The full perfect-power cell and the re-phased U-tail cell are the same
physical arithmetic state in carry and information coordinates. -/
theorem origin_frame_phased_state_exact
    (t n K x p : Nat) :
    (originFrame t n K x p).full.seven.carry =
        (originFrame t n K x p).phasedTail.seven.carry ∧
      (originFrame t n K x p).full.seven.digit =
        (originFrame t n K x p).phasedTail.seven.digit := by
  have h :=
    GSTGraphV2HandwrittenExponentialCascade.graph_u_block_observables_exact
      t n K x p
  constructor
  · simpa [GSTGraphV2Production.originFrame,
      GSTGraphV2Production.originCoordinates,
      GSTGraphV2Production.cell] using h.1
  · simpa [GSTGraphV2Production.originFrame,
      GSTGraphV2Production.originCoordinates,
      GSTGraphV2Production.cell] using h.2.1

/-- At the canonical production cut, the unphased higher-level U tail is the
exact neutral NULL/zero-information state. -/
theorem canonical_cut_neutral_tail
    (s n q : Nat) (hs : 1 ≤ s) :
    let F := canonicalCutFrame s n q
    F.uFrame.neutralTail.seven.carry = 0 ∧
      F.uFrame.neutralTail.seven.digit = 0 ∧
      F.uFrame.neutralTail.seven.space = .null := by
  dsimp only
  have h := canonical_child_u_cut_neutral s n q hs
  simpa [GSTGraphV2Production.canonicalCutFrame,
    GSTGraphV2Production.canonicalCutRow,
    GSTGraphV2Production.originFrame,
    GSTGraphV2Production.originCoordinates,
    GSTGraphV2Production.cell] using h

/-- The right endpoint of every residual production rectangle is exactly the
absolute parent perfect-power sheet, in all observables needed by the proof. -/
theorem residual_right_absolute_state_exact
    (s k m p : Nat) :
    let F := residualFrame s k m p
    F.block.right.seven.carry =
        (cell 1 F.parentExponent p).seven.carry ∧
      F.block.right.seven.digit =
        (cell 1 F.parentExponent p).seven.digit ∧
      F.block.right.eventCode =
        (cell 1 F.parentExponent p).eventCode ∧
      F.block.right.uCharge =
        (cell 1 F.parentExponent p).uCharge ∧
      F.block.right.mixedCharge =
        (cell 1 F.parentExponent p).mixedCharge ∧
      F.block.right.crossingCharge =
        (cell 1 F.parentExponent p).crossingCharge ∧
      F.block.right.survive =
        (cell 1 F.parentExponent p).survive := by
  dsimp only
  have h := residual_parent_observables_exact s k m p
  simpa [GSTGraphV2Production.residualFrame,
    GSTGraphV2Production.residualRectangle,
    GSTGraphV2Production.rectangle,
    GSTGraphV2Production.residualEnergy,
    GSTGraphV2Production.cell] using h

/-- In the sole unbounded classifier level `s=1`, the parent block is exactly
three horizontal x4 edges. -/
theorem residual_level_one_width (k m p : Nat) :
    (residualFrame 1 k m p).parentWidth = 3 := by
  norm_num [GSTGraphV2Production.residualFrame,
    GSTGraphV2HandwrittenOmegaUBlock.residualWidth]

/-- The sole unbounded level therefore has the exact absolute exponent
`3 + 3^(k+1)*m` at its right endpoint. -/
theorem residual_level_one_parent_exponent (k m p : Nat) :
    (residualFrame 1 k m p).parentExponent =
      3 + 3^(k+1) * m := by
  dsimp [GSTGraphV2Production.residualFrame,
    GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent]
  rw [Nat.pow_add]
  ring

#check horizontal_digit_exact
#check vertical_carry_exact
#check navigation_nullspace_flux_exact
#check origin_frame_phased_state_exact
#check canonical_cut_neutral_tail
#check residual_right_absolute_state_exact
#check residual_level_one_width
#check residual_level_one_parent_exponent

#print axioms horizontal_digit_exact
#print axioms origin_frame_phased_state_exact
#print axioms canonical_cut_neutral_tail
#print axioms residual_right_absolute_state_exact

end GSTGraphV2ProductionLaws
