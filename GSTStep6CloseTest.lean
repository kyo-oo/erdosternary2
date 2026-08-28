import GSTStep6Close

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open GSTInfiniteV2
open GSTV2
open GSTStep6Close

/-- Exact regression target for the dedicated Step-6 tactic.  This is the
production logical seam: child Navigation against complete prefix-one parent
badness. -/
theorem gst_step6_close_regression
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gpt56PhaseT s n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  gst_step6_close

#print axioms gst_step6_close_regression
