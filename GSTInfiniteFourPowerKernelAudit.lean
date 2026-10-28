import GSTInfiniteFourPowerNavigation
import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-! Explicit unconditional proof audit. Do not silently import a gate
 hypothesis: ask Lean to typecheck the strongest theorem as written. -/

-- The apparent published "all k >= 8" Happy-Gate theorem.
example (k : Nat) (hk : 8 ≤ k) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTU2DEventTransport.HappyCell
        (GSTCanonicalSevenAxisBridge.carry4 (4^k) p)
        (GSTCanonicalSevenAxisBridge.digit3 (4^k) p) := by
  exact GSTInfiniteFourPowerNavigation.four_power_happy_ge_three k hk

#print axioms GSTInfiniteFourPowerNavigation.power_three_step_collision
#print axioms GSTInfiniteFourPowerNavigation.four_power_happy_ge_three
#print axioms GSTInfiniteFourPowerNavigation.gst_four_power_navigation_universal
