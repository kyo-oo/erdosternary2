import GSTGraphV2ProductionLaws
import GSTGraphV2InfiniteControllerBridge
import GSTFinalResidualEarliestGateBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2ProductionLaws

namespace GSTFinalResidualInfiniteLedgerProbe

/-- Focused all-Nat hard-family compositor probe.

No global-last gate, finite support horizon, residual termination, or terminal
NULL principle occurs here.  The child event is reindexed to the earliest
seed-zero Happy gate, retaining its complete bad lower prefix; the same
physical width-three rectangle is then read through the exact coupled
Past/Future ledger at that gate. -/
theorem residual_level_one_origin_one_infinite_ledger
    (k m q : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm1 : m % 3 = 1)
    (hChild : HappyCell
      (graph (GSTGraphV2Production.residualEnergy 1 k m) 0 (k+2+q)).seven.carry
      (graph (GSTGraphV2Production.residualEnergy 1 k m) 0 (k+2+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (GSTGraphV2Production.residualEnergy 1 k m) 3 (k+2+j)).seven.carry
      (graph (GSTGraphV2Production.residualEnergy 1 k m) 3 (k+2+j)).seven.digit) :
    False := by
  let E := GSTGraphV2Production.residualEnergy 1 k m
  let b := k + 2
  let st := GSTGraphV2InfiniteControllerBridge.graphCoupledState E 3 b

  have hBaseCarryZero : (graph E 0 b).seven.carry = 0 := by
    have hmod : E % 3^b = 1 := by
      have h := pow4_scaled_mod_next (k+1) m
      simpa [E, b, GSTGraphV2Production.residualEnergy,
        GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hc : carry4 E b = 0 := by
      unfold carry4
      rw [hmod]
      apply Nat.div_eq_of_lt
      have hb9 : 9 ≤ 3^b := by
        rw [show (9 : Nat) = 3^2 by decide]
        exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
      omega
    simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc

  have hChild' : HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit := by
    simpa [E, b, Nat.add_assoc] using hChild

  have hRightBad' : ∀ j, ¬ HappyCell
      (graph E 3 (b+j)).seven.carry
      (graph E 3 (b+j)).seven.digit := by
    intro j
    simpa [E, b, Nat.add_assoc] using hRightBad j

  have hControl : GSTV2.InfiniteBadCoupledControl (4^3) st := by
    dsimp [st]
    exact GSTGraphV2InfiniteControllerBridge.graph_infinite_bad_control
      E 3 b hBaseCarryZero hRightBad'

  have hEarliest :=
    GSTFinalResidualEarliestGateBridge.graph_exposed_tail_first_seedzero_control
      E 3 b q hBaseCarryZero hChild'
  dsimp only at hEarliest
  obtain ⟨q0, hGateDigit, hGateCarry, hBadPrefix, hCarryThreeBound⟩ := hEarliest

  have hInvariant : GSTV2.CoupledInvariant (4^3) st := by
    dsimp [st]
    exact GSTGraphV2InfiniteControllerBridge.graphCoupledState_invariant E 3 b

  have hLedger : GSTV2.InfiniteCoupledLedger (4^3) st :=
    GSTV2.infinite_coupled_ledger (4^3) st (by positivity) hInvariant

  have hLedgerAt := hLedger.pastSynchronized (q0+1)
  have hOrbitAt :=
    GSTGraphV2InfiniteControllerBridge.graphCoupledOrbit_exact E 3 b (q0+1)
  dsimp [st] at hLedgerAt hOrbitAt
  rw [hOrbitAt] at hLedgerAt

  have hParentBadAt := hControl.parentBadSuffix (q0+1)
  have hChildCarryAt := hControl.childCarryExact q0

  trace_state
  omega

end GSTFinalResidualInfiniteLedgerProbe
