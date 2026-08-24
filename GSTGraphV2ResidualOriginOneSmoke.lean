import GSTGraphV2ProductionLaws

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-- RED specification for the only unbounded residual classifier family.
A child Navigation witness at level `1+k` with origin trit one cannot coexist
with an all-depth bad residual parent trace at level one. -/
theorem residual_origin_one_unbounded_smoke
    (k m : Nat)
    (hk : 1 ≤ k)
    (hm : 1 ≤ m)
    (hm1 : m % 3 = 1)
    (hchild : GSTNavigationWitness (gstNavigationConstant (1+k) m))
    (hbad : GSTOmegaInfiniteBadTrace 1 k m) : False := by
  exact GSTGraphV2ProductionLaws.residual_level_one_origin_one_collision
    k m hk hm hm1 hchild hbad

#check residual_origin_one_unbounded_smoke
