import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/--
Exact recursive packet for the prefix-one residual branch `n ≡ 1 (mod 3)`.

A hypothetical complete phase-one bad trace cannot terminate at this origin
trit.  The ordinary origin strictly descends to `u = n/3`, the regenerated
parent remains a complete seeded bad trace with the full affine offset kept,
and the child Navigation constant satisfies its exact one-trit recurrence.
-/
theorem gst_prefix_one_residual_bad_descends_new
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hn1 : n % 3 = 1)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∃ u : Nat,
      u = n / 3 ∧
      1 ≤ u ∧
      u < n ∧
      GSTSeededBadTraceS 0
        ((gstCanonicalPrefixOffsetS s + GSTCanonicalBlockS s) / 3 +
          GSTCanonicalBlockS s *
            GSTHardPrefixOneTailS
              gstNavigationConstant gstCanonicalPrefixOffsetS (s+1) u) ∧
      gstNavigationConstant (s+1) n =
        gstNavigationConstant (s+1) 1 +
          3 * 4^(3^(s+1)) * gstNavigationConstant (s+2) u := by
  let u := n / 3

  have hu : 1 ≤ u := by
    dsimp [u]
    exact gst_residual_null_bad_forces_deeper_originS s n hs hn hn1 hBad

  have hred := gst_residual_null_branch_reductionS
    s n hs hn hn1 hBad
  dsimp only at hred

  have hrec := gst_residual_null_child_recurrenceS s n hs hn1
  dsimp only at hrec

  refine ⟨u, rfl, hu, ?_, ?_, ?_⟩
  · simpa [u] using hred.1
  · simpa [u] using hred.2.1
  · simpa [u] using hrec
