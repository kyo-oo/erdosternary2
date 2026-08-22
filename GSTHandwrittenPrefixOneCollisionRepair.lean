import GSTPrefixOneSpacetimeIncidenceControl
import GSTHandwrittenBigNSignedKernel
import «ker07-snapshot».branches.«15_sol_new__physical-phase-crossing-surgery».ResidualNullPrefixFourCutScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-- RED production theorem.  Canonical terminal and forced second-trit
branches are discharged before entering the remaining physical BIG-N split. -/
theorem gpt56_prefix_one_collision_bigN
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let X := c s / 3 + A*T
  obtain ⟨q, N, hd2, hC, hN, hbig, heq, hkernel, hseeded⟩ :=
    gpt56_prefix_one_live_bigN_full_equation_packet
      s n hs hn hchild hBad
  have hsplit := gpt56_information_bigN_vs_parent_segmentS
    s T q N hd2 hbig
  rcases hsplit with hinside | hafter
  · -- Remaining inside-width collision branch.
    omega
  · -- Remaining after-width collision branch.
    have hendpoint : gstDigitS (A*T) q = 2 := by
      simpa [A] using hafter.2
    omega

#check gpt56_prefix_one_collision_bigN
