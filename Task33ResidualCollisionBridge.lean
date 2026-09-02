import GSTFinalResidualConnector
import GSTFinalResidualCollision

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task33ResidualCollisionBridge

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTU2DEventTransport
open GSTGraphV2HandwrittenOmegaUBlock

/-- The already-certified residual connector and the exact level-one collision
compose to rule out the sole unbounded origin-trit-one bad trace. -/
theorem residual_level_one_origin_one_bad_trace_impossible
    (k m : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm1 : m % 3 = 1)
    (hchild : GSTNavigationWitness (gstNavigationConstant (1+k) m))
    (hbad : GSTOmegaInfiniteBadTrace 1 k m) :
    False := by
  obtain ⟨q, hChild⟩ :=
    GSTFinalResidualConnector.residual_child_witness_to_left_happy
      1 k m (by decide) hk hchild
  have hRightBad :=
    GSTFinalResidualConnector.residual_bad_trace_to_right_bad
      1 k m (by decide) hk hbad
  apply GSTFinalResidualCollision.residual_level_one_origin_one_collision
    k m q hk hm hm1
  · simpa [GSTGraphV2Production.residualEnergy,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hChild
  · intro j
    simpa [GSTGraphV2Production.residualEnergy,
      GSTGraphV2HandwrittenOmegaUBlock.residualWidth,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRightBad j

#check residual_level_one_origin_one_bad_trace_impossible
#print axioms residual_level_one_origin_one_bad_trace_impossible

end Task33ResidualCollisionBridge
