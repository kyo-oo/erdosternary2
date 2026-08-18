import ErdosTernary2
import CanonicalOriginTritForcingScratch
import CanonicalResidualInfiniteSupportBridgeScratch

/- CI probe for the isolated 2026-08-18 GST V2 atomic surgery branch.
   No axiom, sorry, admit, native_decide, or proof shortcut is introduced. -/

/-- Exact reduced generator.  Instead of asking directly for infinite origin
support, ask only for arbitrarily deep finite canonical prefix cuts that are
already a good BIG2 state.  The Aug-18 origin-cut theorem then forces the
corresponding ordinary origin trit to be nonzero. -/
def GSTCanonicalGoodBig2PrefixCutsUnboundedS : Prop :=
  ∀ s n,
    1 ≤ s →
    1 ≤ n →
    n % 3 ≠ 0 →
    GSTNavigationWitness (gstNavigationConstant (s+1) n) →
    GSTSeededBadTraceS 1
      (GSTHardPrefixOneTailS
        gstNavigationConstant gstCanonicalPrefixOffsetS s n) →
    ∀ K, ∃ q,
      K ≤ q ∧
      (gstCarryS
          (gstNavigationConstant s ((1 + 3*n) % 3^(q+1))) (q+1) = 0 ∨
       gstCarryS
          (gstNavigationConstant s ((1 + 3*n) % 3^(q+1))) (q+1) = 3) ∧
      gstDigitS
        (gstNavigationConstant s ((1 + 3*n) % 3^(q+1))) (q+1) = 2

/-- The reduced generator is sufficient for the exact locked residual bridge.
This proof is only plumbing: Omega badness is converted to the exact hard-tail
bad trace, every generated good prefix forces a nonzero ordinary origin trit,
and the result is precisely InfiniteTernarySupportS. -/
theorem gst_canonical_residual_infinite_support_bridge_of_good_prefix_cutsS
    (hcuts : GSTCanonicalGoodBig2PrefixCutsUnboundedS) :
    GSTCanonicalResidualInfiniteSupportBridgeS := by
  intro s n hs hn hn3 hchild hOmega
  have hseededS : ∀ j,
      GSTBadPairS
        (gstAffineMulCarryS 4 1
          (gstPrefixOneUPotentialTailS s n) j)
        (gstDigitS (gstPrefixOneUPotentialTailS s n) j) :=
    gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hOmega
  have hbad : GSTSeededBadTraceS 1
      (GSTHardPrefixOneTailS
        gstNavigationConstant gstCanonicalPrefixOffsetS s n) := by
    intro j
    have hj := hseededS j
    simpa [gst_prefix_one_u_tail_eq_hard_tailS] using hj
  intro K
  obtain ⟨q, hKq, hcarry, hbig2⟩ :=
    hcuts s n hs hn hn3 hchild hbad K
  refine ⟨q, hKq, ?_⟩
  have hnz :=
    gst_prefix_one_bad_good_big2_prefix_forces_origin_nonzeroS
      s n q hs hbad hcarry hbig2
  simpa [ternaryOriginDigitS, gstDigitS] using hnz

#check gst_canonical_residual_infinite_support_bridge_of_good_prefix_cutsS
#check gst_last_child_gate_right_chordS

example (n : Nat) : n = n := rfl
