import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/--
Unconditional prefix-one bad reflection.

The proof factors the finite natural origin exactly as
`1 + 3*n = 1 + 3^k*m` with `m % 3 ≠ 0`, transports a hypothetical
child Navigation witness through the forced zero prefix, and closes the
remaining residual Ω bad branch directly through the pre-master residual
boundary termination sectors.  No four-power creation master is used.
-/
theorem gst_prefix_one_bad_reflection_new :
    GSTPrefixOneBadReflection := by
  intro s n hs hn
  dsimp only
  intro hParent

  let T := gstNavigationConstant (s + 1) n

  have hOmega1 : GSTOmegaInfiniteBadTrace s 1 n := by
    apply (gst_omega_infiniteBadTrace_iff_seededAffine s 1 n).2
    simpa [GSTSeededAffineBadTrace, Nat.pow_one, c_mod3 s hs] using hParent

  have hNoParent :
      ¬ GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) :=
    gst_prefix_one_no_parent_navigation_of_omega_bad_atomic
      s n hs hn hOmega1

  change ∀ j, GSTBadPair (gstCarry T j) (gstDigit T j)
  by_contra hNotBadChild

  have hChild : GSTNavigationWitness T := by
    exact (gstNavigationWitness_iff_not_badTrace T).2 hNotBadChild

  let b := 1 + 3*n
  have hbgt : 1 < b := by
    dsimp [b]
    omega
  have hbmod : b % 3 = 1 := by
    dsimp [b]
    omega

  obtain ⟨k, m, hk, hbeq, hmb, hm3⟩ :=
    generalized_cascade_terminates b hbgt hbmod
  have hm : 1 ≤ m := by
    by_contra hm0
    have hmz : m = 0 := by omega
    rw [hmz] at hm3
    simp at hm3

  have hkshape : k = (k - 1) + 1 := by omega
  have hpowstep : 3^k = 3^((k-1)+1) :=
    congrArg (fun t : Nat => 3^t) hkshape
  have hpow : 3^k = 3^(k-1) * 3 := by
    calc
      3^k = 3^((k-1)+1) := hpowstep
      _ = 3^(k-1) * 3 := by rw [Nat.pow_succ]
  have hnmul : n = 3^(k-1) * m := by
    dsimp [b] at hbeq
    rw [hpow] at hbeq
    have hfactor : (3^(k-1) * 3) * m = 3 * (3^(k-1) * m) := by
      ac_rfl
    rw [hfactor] at hbeq
    omega

  have hChildScaled :
      GSTNavigationWitness
        (3^(k-1) * gstNavigationConstant ((s+1)+(k-1)) m) := by
    rw [← gst_navigation_constant_mul3_pow_atomic
      (s+1) (k-1) m (by omega)]
    simpa [T, hnmul] using hChild

  have hChildResidual0 :
      GSTNavigationWitness (gstNavigationConstant ((s+1)+(k-1)) m) :=
    gstNavigationWitness_of_mul_three_pow_atomic
      (k-1) (gstNavigationConstant ((s+1)+(k-1)) m) hChildScaled

  have hidx : (s+1)+(k-1) = s+k := by omega
  have hChildResidual :
      GSTNavigationWitness (gstNavigationConstant (s+k) m) := by
    simpa [hidx] using hChildResidual0

  have hNoParentResidual :
      ¬ GSTNavigationWitness (gstNavigationConstant s (1 + 3^k*m)) := by
    rw [← hbeq]
    simpa [b] using hNoParent

  have hOmega : GSTOmegaInfiniteBadTrace s k m := by
    intro j
    change GSTOmegaGatePolynomial (gstOmega s k m j) ≠ 0
    intro hzero
    have hgate :=
      (gst_omega_gate_polynomial_zero_iff (gstOmega s k m j)).1 hzero
    have hprojection := gst_omega_parent_projection s k m j hs
    apply hNoParentResidual
    rcases hgate.2 with h0 | h3
    · have hd :
          gstDigit (gstNavigationConstant s (1+3^k*m)) (k+j) = 2 := by
        rw [hprojection.1]
        exact hgate.1
      have hc :
          gstCarry (gstNavigationConstant s (1+3^k*m)) (k+j) = 0 := by
        rw [hprojection.2]
        exact h0
      exact gstNavigationWitness_of_digit_carry_zero _ (k+j) hd hc
    · have hd :
          gstDigit (gstNavigationConstant s (1+3^k*m)) (k+j) = 2 := by
        rw [hprojection.1]
        exact hgate.1
      have hc :
          gstCarry (gstNavigationConstant s (1+3^k*m)) (k+j) = 3 := by
        rw [hprojection.2]
        exact h3
      exact gstNavigationWitness_of_digit_carry_three _ (k+j) hd hc

  by_cases hclosed : GSTOriginClosed s k (m % 3)
  · have hParentNav :
        GSTNavigationWitness (gstNavigationConstant s (1 + 3^k*m)) :=
      gst_navigation_constant_origin_closed_witness
        s k m (m % 3) hs hm hm3 rfl hclosed
    exact hNoParentResidual hParentNav

  have hrange : m % 3 = 1 ∨ m % 3 = 2 := by
    have hlt : m % 3 < 3 := Nat.mod_lt _ (by decide)
    omega
  have hboundary := gst_origin_not_closed_boundary
    s k (m % 3) hs hk hrange hclosed
  have htermination : ¬ GSTOmegaInfiniteBadTrace s k m := by
    rcases hboundary with ⟨rfl, hcase⟩ | ⟨rfl, hcase⟩ | hstable
    · exact gst_omega_termination_s1 k m hk hm hm3
        (Or.inl ⟨rfl, hcase⟩) hChildResidual
    · exact gst_omega_termination_s3 k m hk hm hm3
        (Or.inr (Or.inl ⟨rfl, hcase⟩)) hChildResidual
    · exact gst_omega_termination_stable s k m hstable.1 hstable.2.1
        hk hm hm3 (Or.inr (Or.inr hstable)) hChildResidual
  exact htermination hOmega

#print axioms gst_prefix_one_bad_reflection_new