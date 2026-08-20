import GSTPrefixOneGateAdapterSmoke
import GSTInfiniteGateTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTV2

/-- The canonical prefix-one collision does not stop at the child's certified
Happy Gate.  The same all-depth controller transports that information into a
nonzero latent carry at the next coordinate while retaining the complete
parent bad suffix and the exact shared invariant. -/
theorem gpt56_prefix_one_child_gate_becomes_latent_information
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) :
    ∃ j,
      GSTV2.LatentGateTransfer
        (gpt56PrefixOneA s) (gpt56PrefixOneInitialState s n) j := by
  have hcontrol := gpt56_prefix_one_infinite_bad_control s n hs hBad
  obtain ⟨j, hHappy⟩ :=
    gpt56_prefix_one_controller_realizes_child_gate s n hs hBad hchild
  refine ⟨j, ?_⟩
  exact GSTV2.coupled_happy_transports_information
    (gpt56PrefixOneA s) (gpt56PrefixOneInitialState s n) j
    hcontrol hHappy

#print axioms gpt56_prefix_one_child_gate_becomes_latent_information
