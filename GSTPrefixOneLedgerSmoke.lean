import GSTPrefixOneInfiniteAdapterSmoke
import GSTInfiniteCoupledLedger

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTV2

/-- Canonical prefix-one all-depth Past/Future synchronization.  This is the
production form of "information changes shape but is not destroyed": the
emitted parent information, the live horizontal residue, and the emitted
child information are one exact conserved packet at every depth. -/
theorem gpt56_prefix_one_past_synchronization
    (s n K : Nat) (hs : 1 ≤ s) :
    (gpt56PrefixOneInitialState s n).parentPast (gpt56PrefixOneA s) K +
        3^K *
          (GSTV2.coupledOrbit (gpt56PrefixOneA s)
            (gpt56PrefixOneInitialState s n) K).childResidue =
      (gpt56PrefixOneInitialState s n).childResidue +
        gpt56PrefixOneA s *
          (gpt56PrefixOneInitialState s n).childPast K := by
  exact GSTV2.coupledOrbit_past_synchronization
    (gpt56PrefixOneA s) (gpt56PrefixOneInitialState s n)
    (Nat.pow_pos (by decide))
    (gpt56_prefix_one_initial_invariant s n hs) K

#print axioms gpt56_prefix_one_past_synchronization
