import ErdosTernary2
import GSTV2InfiniteCore

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST infinity control: proof-strength audit

This file does NOT insert an axiom or assume the missing bridge as a theorem.
It proves that the existing residual infinite-support forcing proposition has
exactly the strength of the desired prefix-one Ω termination proposition.

Hence finite support and Omega energy conservation are useful, but proving
that a complete residual bad trace creates infinite *origin support* is the
load-bearing missing arrow.
-/

namespace GSTInfinityBridgeAudit

/-- The actual residual prefix-one Omega-termination target. -/
def PrefixOneOmegaTermination : Prop :=
  ∀ s n : Nat,
    1 ≤ s →
    1 ≤ n →
    n % 3 ≠ 0 →
    GSTNavigationWitness (gstNavigationConstant (s+1) n) →
    ¬ GSTOmegaInfiniteBadTrace s 1 n

/-- The "infinite-support bridge" is equivalent to Ω termination because the
ordinary natural origin is already known to have finite ternary support. -/
theorem infinite_support_bridge_iff_prefix_one_termination :
    GSTCanonicalResidualInfiniteSupportBridgeS ↔
      PrefixOneOmegaTermination := by
  constructor
  · intro hbridge s n hs hn hn3 hchild
    exact gst_residual_prefix_one_no_bad_of_infinite_support_bridgeS
      hbridge s n hs hn hn3 hchild
  · intro hterm s n hs hn hn3 hchild hbad
    exact False.elim (hterm s n hs hn hn3 hchild hbad)

/-- The Omega moving-future coordinate terminates for every finite child.
This is true *independently* of whether the parent ever reaches Happy. -/
theorem omega_child_future_zero_unconditionally (s k n : Nat) :
    (gstOmega s k n (gstNavigationConstant (s+k) n)).descent = 0 := by
  exact gst_omega_descent_terminates_at_child_value s k n

/-- The exact finite-support fact: no natural origin has infinitely many
nonzero ternary trits. This is the correct endpoint contradiction. -/
theorem origin_support_finite_unconditionally (n : Nat) :
    ¬ InfiniteTernarySupportS n :=
  natural_not_infinite_ternary_supportS n

#print axioms infinite_support_bridge_iff_prefix_one_termination
#print axioms omega_child_future_zero_unconditionally
#print axioms origin_support_finite_unconditionally

end GSTInfinityBridgeAudit
