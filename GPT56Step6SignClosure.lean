import GSTFinalPrefixOneStep6Boundary

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GPT56Step6SignClosure

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTU2DExactCrossingCharge
open GSTPerfectPowerTailNavigation
open GSTGraphV2HandwrittenOmegaUBlock
open GSTFinalPrefixOneStep6Infinite
open GSTFinalPrefixOneStep6Boundary

private def signC (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.carry

private def signD (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.digit

/-- Isolated all-depth Step-6 sign seam. -/
theorem step6_sign_closure
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    weightedCrossPrefix (signC s n) (signD s n)
      (residualWidth s) (q+1) ≤ 0 := by
  let E := residualEnergy s 1 n
  let N := residualWidth s
  let b := s + 2
  have hBaseCarryZero : (graph E 0 b).seven.carry = 0 := by
    simpa [E, N, b] using infinite_base_carry_zero s n hs
  have hController :
      GSTV2.InfiniteBadCoupledControl (4^N) (graphCoupledState E N b) := by
    apply graph_infinite_bad_control E N b hBaseCarryZero
    intro j
    simpa [E, N, b, Nat.add_assoc] using hRightBad j
  have hLedger :
      GSTV2.InfiniteCoupledLedger (4^N) (graphCoupledState E N b) := by
    simpa [E, N, b] using canonical_infinite_ledger s n
  have hAllDepth := canonical_controller_graph_all_depth s n
  have hPastFuture := canonical_past_future_synchronized_all_depth s n
  have hCancelled := canonical_controller_boundary_identification
    s n (q+1) hs hn hRightBad
  have hRight := right_boundary_weighted_sum_nonpositive
    s n (q+1) hRightBad
  dsimp [signC, signD, E, N, b] at hCancelled hRight ⊢
  trace_state
  omega

#check step6_sign_closure
#print axioms step6_sign_closure

end GPT56Step6SignClosure
