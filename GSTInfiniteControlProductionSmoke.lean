import ErdosTernary2
import «ker07-snapshot».branches.«15_sol_new__physical-phase-crossing-surgery».CanonicalResidualInfiniteSupportBridgeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- The exact production target.  This is a proposition/interface, not an
assumption silently inserted into the final proof. -/
def GSTInfiniteControlProductionTarget : Prop :=
  GSTCanonicalResidualInfiniteSupportBridgeS

/-- Consumer smoke: once the new V2 bridge is proved, it immediately eliminates
the live residual prefix-one bad trace.  The obsolete `h_creation_for_4pow`
route is not referenced anywhere in this file. -/
theorem gst_infinite_control_consumer_smoke
    (hbridge : GSTInfiniteControlProductionTarget)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hn3 : n % 3 ≠ 0)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) :
    ¬ GSTOmegaInfiniteBadTrace s 1 n := by
  exact gst_residual_prefix_one_no_bad_of_infinite_support_bridgeS
    hbridge s n hs hn hn3 hchild

#check GSTInfiniteControlProductionTarget
#check gst_infinite_control_consumer_smoke
#print axioms gst_infinite_control_consumer_smoke
