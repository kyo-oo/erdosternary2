import GSTHandwrittenBigNSignedKernel

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-!
# Canonical energy retained at the live BIG-N boundary

The former collision packet remembered the child gate, its first BIG1
coordinate, the three-world code, the signed kernel, and the parent bad trace.
It did not retain the equation that distinguishes the canonical child from an
arbitrary natural.  That omission is mathematically material: the corresponding
affine child-to-parent transport is false for arbitrary naturals.

This packet keeps the exact perfect-power energy in the same theorem object.
It asserts no transport conclusion and introduces no interface assumption.
-/

/-- The live BIG-N packet together with the exact perfect-power equation for
the child Navigation Constant. -/
theorem gpt56_prefix_one_live_bigN_full_energy_packet
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let X := c s / 3 + A*T
    (∃ q N,
      gstDigit T q = 2 ∧
      (gstCarry T q = 0 ∨ gstCarry T q = 3) ∧
      1 ≤ N ∧
      GSTInformationEqualsBigNS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N ∧
      gstBig1ProjectedPathCodeS
        (fun r => GSTPhysicalKernel.binaryColumnCarry T q r)
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N =
          5 * Finset.sum (Finset.range (N-1)) (fun j => 2^j * 3^j) +
            4 * (2^(N-1) * 3^(N-1)) ∧
      Finset.sum (Finset.range N)
        (fun r => GSTPhysicalKernel.signedKernelTwice
          (GSTPhysicalKernel.binaryColumnCarry T q r)
          (GSTPhysicalKernel.binaryColumnDigit T q r)) =
            7 * ((N : Int) - 3) ∧
      GSTSeededAffineBadTrace 1 X) ∧
    4^(3^(s+1) * n) = 1 + 3^(s+2) * T := by
  dsimp only
  constructor
  · simpa only using
      gpt56_prefix_one_live_bigN_full_equation_packet
        s n hs hn hchild hBad
  · exact gst_navigation_decomposition (s+1) n (by omega)

#check gpt56_prefix_one_live_bigN_full_energy_packet
#print axioms gpt56_prefix_one_live_bigN_full_energy_packet
