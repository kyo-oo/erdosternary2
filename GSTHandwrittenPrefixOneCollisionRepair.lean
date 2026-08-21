import GSTHandwrittenBigNSignedKernel

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-- RED production theorem.  All handwritten data have already been reduced to
one physical BIG-N packet.  The only split left is whether the first BIG1 lies
inside the complete horizontal parent segment or strictly after it. -/
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
  · -- BIG-N occurs inside the exact binary width of the parent multiplier.
    -- The next surgery consumes the finite DESTROY boundary and the signed
    -- kernel packet against the retained seed-one bad parent state.
    omega
  · -- The parent multiplier segment ends before BIG-N.  Hence its endpoint
    -- is still BIG2; combine this endpoint with the conserved affine packet.
    have hendpoint : gstDigitS (A*T) q = 2 := by
      simpa [A] using hafter.2
    omega

#check gpt56_prefix_one_collision_bigN
