import ErdosTernary2
import GSTTheAct

namespace GSTResidualOmegaRevival

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Live first residual world.  The monolith already kernel-compiles the exact
Omega-state termination theorem; this module exposes that theorem directly
instead of duplicating its fragile elaboration script. -/
theorem omega_termination_s1
    (k m : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm3 : m % 3 ≠ 0)
    (hboundary : GSTResidualBoundary 1 k (m % 3))
    (hchild : GSTNavigationWitness (gstNavigationConstant (1+k) m)) :
    ¬ GSTOmegaInfiniteBadTrace 1 k m :=
  gst_omega_termination_s1 k m hk hm hm3 hboundary hchild

/-- Live level-three residual world, exported from the compiled monolith theorem. -/
theorem omega_termination_s3
    (k m : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm3 : m % 3 ≠ 0)
    (hboundary : GSTResidualBoundary 3 k (m % 3))
    (hchild : GSTNavigationWitness (gstNavigationConstant (3+k) m)) :
    ¬ GSTOmegaInfiniteBadTrace 3 k m :=
  gst_omega_termination_s3 k m hk hm hm3 hboundary hchild

/-- Live stable residual world for levels at least two other than three. -/
theorem omega_termination_stable
    (s k m : Nat) (hs : 2 ≤ s) (hs3 : s ≠ 3)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hm3 : m % 3 ≠ 0)
    (hboundary : GSTResidualBoundary s k (m % 3))
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+k) m)) :
    ¬ GSTOmegaInfiniteBadTrace s k m :=
  gst_omega_termination_stable s k m hs hs3 hk hm hm3 hboundary hchild

/-- The exact residual Ω termination theorem, now theorem-backed with no custom
hypothesis and no duplicated elaboration path. -/
theorem omega_termination : GSTResidualOmegaTermination :=
  gst_residual_omega_termination

/-- Assumption-free residual Navigation lift obtained from exact Ω termination. -/
theorem residual_navigation_lift : GSTResidualNavigationLift :=
  gst_residual_navigation_lift_of_omega_termination omega_termination

/-- Universal canonical Navigation, obtained by the monolith's existing
strong induction once the unconditional residual lift is supplied. -/
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
      have hb' : 1 ≤ k / 3 := by
        simpa [hs1] using hb
      have hsmall : 1 < k / 3 := by
        have hk5 : 5 ≤ k := by omega
        omega
      simpa only [hs1, Nat.pow_one] using hsmall
  have hnav : GSTNavigationWitness
      (gstNavigationConstant (v3 k) (k / 3^(v3 k))) :=
    navigation_all (v3 k) (k / 3^(v3 k)) hs hb hb3 hdomain
  have hfull := full_power_good_witness
    (v3 k) (k / 3^(v3 k)) hs hb hb3 hnav
  simpa only [← hk_eq] using hfull

/-- The unconditional even-power closure supplied by the theorem-backed
residual Navigation chain. -/
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

/-- Binder-free THE ACT. -/
theorem the_act : GSTTheAct.the_act := by
  intro K hK
  exact has_two_imp_not_no_two (4^K) (even_universal K (by omega))

/-- Binder-free full Erdős statement. -/
theorem full_erdos :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  GSTTheAct.full_erdos_of_the_act the_act

#print axioms omega_termination_s1
#print axioms omega_termination_s3
#print axioms omega_termination_stable
#print axioms omega_termination
#print axioms residual_navigation_lift
#print axioms even_universal
#print axioms the_act
#print axioms full_erdos

end GSTResidualOmegaRevival
