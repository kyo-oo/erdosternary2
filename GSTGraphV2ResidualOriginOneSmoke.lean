import GSTGraphV2ProductionLaws

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTU2DEventTransport
open GSTGraphV2Production

/-- RED specification for the sole unbounded residual classifier family.
This is deliberately stated only in the pure Graph-V2 vocabulary: a certified
Happy child gate on the level-one residual sheet cannot coexist with a right
boundary that is bad at every generalized residual gate row. -/
theorem residual_origin_one_unbounded_smoke
    (k m j : Nat)
    (hk : 1 ≤ k)
    (hm1 : m % 3 = 1)
    (hChild : HappyCell
      (residualGateFrame 1 k m j).residual.block.left.seven.carry
      (residualGateFrame 1 k m j).residual.block.left.seven.digit)
    (hRightBad : ∀ r : Nat, ¬ HappyCell
      (residualFrame 1 k m (residualGateRow 1 k r)).block.right.seven.carry
      (residualFrame 1 k m (residualGateRow 1 k r)).block.right.seven.digit) :
    False := by
  exact GSTGraphV2ProductionLaws.residual_level_one_origin_one_collision
    k m j hk hm1 hChild hRightBad

#check residual_origin_one_unbounded_smoke
