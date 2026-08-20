import ErdosTernary2
import «ker07-snapshot».branches.«15_sol_new__physical-phase-crossing-surgery».CanonicalResidualInfiniteSupportBridgeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- RED production seam: the old `h_creation_for_4pow` route is intentionally
not used.  This theorem records the exact all-depth replacement contract. -/
theorem gst_infinite_control_production_smoke
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hn3 : n % 3 ≠ 0)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hbad : GSTOmegaInfiniteBadTrace s 1 n) :
    InfiniteTernarySupportS n := by
  exact gst_canonical_residual_infinite_support_bridge
    s n hs hn hn3 hchild hbad
