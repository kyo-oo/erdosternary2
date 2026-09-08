import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- A monolith Navigation witness is exactly a concrete seed-zero Happy cell
in the arithmetic language used by the retained-offset recursion. -/
theorem gst_navigation_witness_to_seeded_zero_happy_new
    (R : Nat) (hNav : GSTNavigationWitness R) :
    ∃ q, GSTSeededHappyS 0 R q := by
  obtain ⟨q, hd, hspace⟩ := hNav
  have hmod : gstCarry R q % 3 = 0 :=
    gstGoodSpace_carry_mod3_zero R q hspace
  have hlt : gstCarry R q < 4 := by
    cases q with
    | zero =>
        simp [gstCarry, Nat.mod_one]
    | succ q =>
        exact gstCarry_lt_four R (q+1) (by omega)
  have hcarry : gstCarry R q = 0 ∨ gstCarry R q = 3 := by
    omega
  refine ⟨q, ?_⟩
  constructor
  · simpa [gstDigitS, gstDigit] using hd
  · simpa [gstAffineMulCarryS, gstCarryS, gstCarry] using hcarry

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
