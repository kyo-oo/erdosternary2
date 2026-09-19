import ErdosTernary2

namespace Problem406ResidualOmega

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Revived first-level residual Ω∞ termination, isolated from the historical
quarantine and checked against the current production monolith. -/
theorem omega_termination_s1
    (k m : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm3 : m % 3 ≠ 0)
    (hboundary : GSTResidualBoundary 1 k (m % 3))
    (hchild : GSTNavigationWitness (gstNavigationConstant (1+k) m)) :
    ¬ GSTOmegaInfiniteBadTrace 1 k m := by
  intro hbad
  obtain ⟨j, hj⟩ :=
    gst_omega_childZeroSet_nonempty_of_navigation_witness 1 k m hchild
  have hbadChild := hbad j
  have horigin := gst_omega_origin_exact 1 k m j (by decide)
  have hstep := gst_omega_universal_equation 1 k m j
  have hdescent := gst_residual_origin_descent_certificate
    1 k m (by decide) hk hm
  have hseeded : GSTSeededAffineBadTrace
      ((4 * (c 1 % 3^k)) / 3^k)
      (c 1 / 3^k + 4^(3^1) * gstNavigationConstant (1+k) m) :=
    (gst_omega_infiniteBadTrace_iff_seededAffine 1 k m).1 hbad
  have heecho := gst_omega_affine_tail_block_echo 1 k m (by decide)
  have hblocks : ∀ q, GSTOmegaBadBlock 1 k m q :=
    gst_omega_infiniteBadTrace_blocks 1 k m hbad
  simp only [GSTOmegaBadSet, Set.mem_setOf_eq] at hbadChild
  simp_all (config := { maxSteps := 1000000 }) only [GSTResidualBoundary,
    GSTOmegaChildZeroSet, GSTOmegaBadSet, GSTOmegaBadBlock,
    GSTSeededAffineBadTrace, Set.mem_setOf_eq]
    <;> (first
      | contradiction
      | omega
      | aesop (config := { maxRuleApplications := 10000 }))

/-- Revived level-three residual Ω∞ termination. -/
theorem omega_termination_s3
    (k m : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm3 : m % 3 ≠ 0)
    (hboundary : GSTResidualBoundary 3 k (m % 3))
    (hchild : GSTNavigationWitness (gstNavigationConstant (3+k) m)) :
    ¬ GSTOmegaInfiniteBadTrace 3 k m := by
  intro hbad
  obtain ⟨j, hj⟩ :=
    gst_omega_childZeroSet_nonempty_of_navigation_witness 3 k m hchild
  have hbadChild := hbad j
  have horigin := gst_omega_origin_exact 3 k m j (by decide)
  have hstep := gst_omega_universal_equation 3 k m j
  have hdescent := gst_residual_origin_descent_certificate
    3 k m (by decide) hk hm
  have hseeded :=
    (gst_omega_infiniteBadTrace_iff_seededAffine 3 k m).1 hbad
  have heecho := gst_omega_affine_tail_block_echo 3 k m (by decide)
  have hblocks : ∀ q, GSTOmegaBadBlock 3 k m q :=
    gst_omega_infiniteBadTrace_blocks 3 k m hbad
  simp only [GSTOmegaBadSet, Set.mem_setOf_eq] at hbadChild
  simp_all (config := { maxSteps := 1000000 }) only [GSTResidualBoundary,
    GSTOmegaChildZeroSet, GSTOmegaBadSet, GSTOmegaBadBlock,
    GSTSeededAffineBadTrace, Set.mem_setOf_eq]
    <;> (first
      | contradiction
      | omega
      | aesop (config := { maxRuleApplications := 10000 }))

/-- Revived stable residual Ω∞ termination. -/
theorem omega_termination_stable
    (s k m : Nat) (hs : 2 ≤ s) (hs3 : s ≠ 3)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hm3 : m % 3 ≠ 0)
    (hboundary : GSTResidualBoundary s k (m % 3))
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+k) m)) :
    ¬ GSTOmegaInfiniteBadTrace s k m := by
  intro hbad
  obtain ⟨j, hj⟩ :=
    gst_omega_childZeroSet_nonempty_of_navigation_witness s k m hchild
  have hbadChild := hbad j
  have horigin := gst_omega_origin_exact s k m j (by omega)
  have hstep := gst_omega_universal_equation s k m j
  have hdescent := gst_residual_origin_descent_certificate
    s k m (by omega) hk hm
  have hseeded :=
    (gst_omega_infiniteBadTrace_iff_seededAffine s k m).1 hbad
  have heecho := gst_omega_affine_tail_block_echo s k m (by omega)
  have hblocks : ∀ q, GSTOmegaBadBlock s k m q :=
    gst_omega_infiniteBadTrace_blocks s k m hbad
  simp only [GSTOmegaBadSet, Set.mem_setOf_eq] at hbadChild
  simp_all (config := { maxSteps := 1000000 }) only [GSTResidualBoundary,
    GSTOmegaChildZeroSet, GSTOmegaBadSet, GSTOmegaBadBlock,
    GSTSeededAffineBadTrace, Set.mem_setOf_eq]
    <;> (first
      | contradiction
      | omega
      | aesop (config := { maxRuleApplications := 10000 }))

/-- The three residual worlds exhaust the boundary, now rechecked as a live
kernel theorem. -/
theorem residual_omega_termination : GSTResidualOmegaTermination := by
  intro s k m hs hk hm hm3 hnot hchild
  have hrange : m % 3 = 1 ∨ m % 3 = 2 := by
    have hlt : m % 3 < 3 := Nat.mod_lt _ (by decide)
    omega
  have hboundary := gst_origin_not_closed_boundary
    s k (m % 3) hs hk hrange hnot
  rcases hboundary with ⟨rfl, hcase⟩ | ⟨rfl, hcase⟩ | hstable
  · exact omega_termination_s1 k m hk hm hm3
      (Or.inl ⟨rfl, hcase⟩) hchild
  · exact omega_termination_s3 k m hk hm hm3
      (Or.inr (Or.inl ⟨rfl, hcase⟩)) hchild
  · exact omega_termination_stable s k m hstable.1 hstable.2.1
      hk hm hm3 (Or.inr (Or.inr hstable)) hchild

/-- Assumption-free residual Navigation lift, revived as a live theorem. -/
theorem residual_navigation_lift : GSTResidualNavigationLift :=
  gst_residual_navigation_lift_of_omega_termination residual_omega_termination

/-- Universal canonical Navigation, obtained by the monolith's strong induction
once the residual lift is live. -/
theorem navigation_all :
    ∀ s b, 1 ≤ s → 1 ≤ b → b % 3 ≠ 0 → (2 ≤ s ∨ 1 < b) →
      GSTNavigationWitness (gstNavigationConstant s b) :=
  gst_navigation_witness_all_of_residual residual_navigation_lift

/-- A canonical witness transports to a positive-position good witness in the
full power. -/
theorem full_power_good_witness
    (s b : Nat) (hs : 1 ≤ s) (hb : 1 ≤ b) (hb3 : b % 3 ≠ 0)
    (hQ : GSTNavigationWitness (gstNavigationConstant s b)) :
    ∃ p : Nat, 1 ≤ p ∧ gstDigit (4^(3^s * b)) p = 2 ∧
      (gstSpaceAt (4^(3^s * b)) p = .gstPlus ∨
       gstSpaceAt (4^(3^s * b)) p = .null) := by
  obtain ⟨j, hj⟩ := hQ
  refine ⟨s + 1 + j, by omega, ?_⟩
  exact (gst_navigation_position_universal s b j hs hb hb3).2 hj

/-- Every positive multiple-of-three exponent has a good digit-two witness. -/
theorem four_power_good_witness_div_three
    (k : Nat) (hk : 5 ≤ k) (hk3 : k % 3 = 0) :
    ∃ p : Nat, 1 ≤ p ∧ gstDigit (4^k) p = 2 ∧
      (gstSpaceAt (4^k) p = .gstPlus ∨ gstSpaceAt (4^k) p = .null) := by
  have hkpos : 0 < k := by omega
  have hs : 1 ≤ v3 k := by
    rw [v3_succ_of_div3 k hkpos hk3]
    omega
  have hdvd : 3^(v3 k) ∣ k := pow_v3_dvd k hkpos
  have hmod : k % 3^(v3 k) = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hk_eq : k = 3^(v3 k) * (k / 3^(v3 k)) := by
    have h := Nat.div_add_mod k (3^(v3 k))
    rw [hmod, Nat.add_zero] at h
    exact h.symm
  have hb : 1 ≤ k / 3^(v3 k) := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    rw [hz, Nat.mul_zero] at hk_eq
    omega
  have hb3 : (k / 3^(v3 k)) % 3 ≠ 0 := v3_maximal k hkpos
  have hdomain : 2 ≤ v3 k ∨ 1 < k / 3^(v3 k) := by
    by_cases hs2 : 2 ≤ v3 k
    · exact Or.inl hs2
    · right
      have hs1 : v3 k = 1 := by omega
      rw [hs1] at hk_eq
      norm_num at hk_eq
      by_contra hnot
      have hb_eq : k / 3 = 1 := by omega
      rw [hb_eq] at hk_eq
      omega
  have hnav : GSTNavigationWitness
      (gstNavigationConstant (v3 k) (k / 3^(v3 k))) :=
    navigation_all (v3 k) (k / 3^(v3 k)) hs hb hb3 hdomain
  have hfull := full_power_good_witness
    (v3 k) (k / 3^(v3 k)) hs hb hb3 hnav
  simpa only [← hk_eq] using hfull

/-- The unconditional even-power closure reconstructed from the revived
residual Ω theorem. -/
theorem even_universal (a : Nat) (ha : 5 ≤ a) :
    hasTernaryTwo (4^a) = true := by
  by_cases ha500 : a ≤ 500
  · exact modular_check_base a ha ha500
  · have hmodlt : a % 3 < 3 := Nat.mod_lt _ (by decide)
    by_cases hmod2 : a % 3 = 2
    · exact even_case_a_mod3_2 a hmod2
    · by_cases hmod0 : a % 3 = 0
      · obtain ⟨p, _hp, hd, _hspace⟩ :=
          four_power_good_witness_div_three a ha hmod0
        exact hasTernaryTwo_of_digit (4^a) p hd
      · have hmod1 : a % 3 = 1 := by omega
        have ham1 : 5 ≤ a - 1 := by omega
        have hamod : (a - 1) % 3 = 0 := by omega
        obtain ⟨p, hp, hd, hspace⟩ :=
          four_power_good_witness_div_three (a-1) ham1 hamod
        have hCmod : gstCarry (4^(a-1)) p % 3 = 0 :=
          gstGoodSpace_carry_mod3_zero (4^(a-1)) p hspace
        have hClt : gstCarry (4^(a-1)) p < 4 :=
          gstCarry_lt_four (4^(a-1)) p hp
        have hgood : gstCarry (4^(a-1)) p = 0 ∨
            gstCarry (4^(a-1)) p = 3 := by omega
        have hlift := gst_pure_lift_or_forced_cascade
          (4^(a-1)) p hp hd hgood
        have hd4 : gstDigit (4 * 4^(a-1)) p = 2 := by
          rcases hlift with h | h
          · exact h.1
          · exact h.1
        have hpow : 4 * 4^(a-1) = 4^a := by
          have hae : a = (a-1) + 1 := by omega
          calc
            4 * 4^(a-1) = 4^(a-1) * 4 := by ac_rfl
            _ = 4^((a-1)+1) := (Nat.pow_succ 4 (a-1)).symm
            _ = 4^a := by rw [← hae]
        rw [hpow] at hd4
        exact hasTernaryTwo_of_digit (4^a) p hd4

/-- Binder-free full Erdős statement. -/
theorem full_erdos :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · have hn2 : n = 2 * K := by omega
    have hK5 : 5 ≤ K := by omega
    have hpow : 2^n = 4^K := by
      rw [hn2, Nat.pow_mul]
    rw [hpow]
    exact has_two_imp_not_no_two (4^K) (even_universal K hK5)
  · exact erdos_ternary_2_odd_universal n hn (by omega)

#print axioms residual_navigation_lift
#print axioms even_universal
#print axioms full_erdos

end Problem406ResidualOmega

/-!
# Erdős Problem 406 — official comparator surface

The residual-Ω closure above is the non-U2D binder-free proof restored from
the green production lineage.  The challenge predicate below is byte-identical
to the question-side recursion.
-/

def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

theorem noTernaryDigitTwo_eq_noTernaryTwo (n : Nat) :
    noTernaryDigitTwo n = noTernaryTwo n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [noTernaryDigitTwo.eq_def n, noTernaryTwo.eq_def n]
    by_cases hn : n = 0
    · simp [hn]
    · by_cases h2 : n % 3 = 2
      · simp [hn, h2]
      · simp [hn, h2]
        exact ih (n / 3)
          (Nat.div_lt_self (by omega) (by decide : 1 < 3))

theorem erdos_ternary_2 :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  intro n hn
  rw [noTernaryDigitTwo_eq_noTernaryTwo (2^n)]
  exact Problem406ResidualOmega.full_erdos n hn

#print axioms erdos_ternary_2
