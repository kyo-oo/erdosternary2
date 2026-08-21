import GSTHandwrittenBigNSignedKernel
import «ker07-snapshot».branches.«16_sol_latest__5c579-final-bigN-right-chord-atomic».ResidualNullPrefixFourCutScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-- RED production theorem.  Canonical terminal and forced second-trit
branches are discharged before entering the remaining physical BIG-N split. -/
theorem gpt56_prefix_one_collision_bigN
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  -- Exact canonical terminal: n = 1 is impossible under a complete
  -- prefix-one bad trace at every positive level.
  by_cases hn_one : n = 1
  · subst n
    exact gst_residual_null_origin_one_bad_impossible_allS s hs hBad

  -- At levels s >= 2, a residual NULL branch cannot expose a second
  -- ordinary origin trit equal to one.  This removes the 11_3 descent
  -- branch kernel-cleanly before the horizontal collision analysis.
  by_cases hs_one : s = 1
  · skip
  · have hs2 : 2 ≤ s := by omega
    by_cases hn_mod1 : n % 3 = 1
    · by_cases hnext_one : (n / 3) % 3 = 1
      · exact gst_residual_null_second_trit_one_impossibleS
          s n hs2 hn hn_mod1 hnext_one hBad
      · skip
    · skip

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
