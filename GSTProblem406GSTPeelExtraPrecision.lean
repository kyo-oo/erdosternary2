import GSTProblem406GSTPeelFixedPoint

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Two additional exact physical noncollision trits from GST peel precision

The nonlinear fixed point identity peel1(x)-x=3*x*(2*x+1)^2
has TWO EXTRA ternary orders of 3-adic accuracy along the finite
all-one exponent approximants s_m=(3^m-1)/2.

Prove, for every natural m, the stronger exact physical congruence

  affineOrbit(s_m) ≡ s_m  (mod 3^(m+2)).

Consequently the genuine power 4^(s_m) has no ternary digit 2 in
the first m+2 nontrivial rows, even though s_m can be arbitrarily
large. These are physical delayed SURVIVORS, not global bad exponents.
-/

namespace GSTProblem406GSTPeelExtraPrecision

open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel
open GSTProblem406GSTPeelFixedPoint

/-- The special all-one source is fixed by GST peel1 not just modulo
3^m but modulo the stronger 3^(m+2). -/
theorem peel1_allones_two_extra_trits (m : Nat) :
    peel1 (ternaryOnes m)%3^(m+2)=ternaryOnes m%3^(m+2) := by
  cases m with
  | zero =>
      norm_num [ternaryOnes,peel1]
  | succ m =>
      rw [peel1_exact_nonarchimedean_fixedpoint,
          ternaryOnes_identity (m+1)]
      have hpow1 : 3^(m+1) = 3^m*3 := by rw [pow_succ]
      have hpow3 : 3^((m+1)+2) = 3^m*27 := by
        rw [show (m+1)+2=m+3 by omega,pow_add]
        norm_num
      have hdvd :
          3^((m+1)+2) ∣
            3*ternaryOnes (m+1)*(3^(m+1))^2 := by
        refine ⟨ternaryOnes (m+1)*3^m, ?_⟩
        rw [hpow1,hpow3]
        ring
      have hzero :
          (3*ternaryOnes (m+1)*(3^(m+1))^2) % 3^((m+1)+2) = 0 :=
        Nat.mod_eq_zero_of_dvd hdvd
      rw [Nat.add_mod,hzero]
      simp

/-- Cross-scale original perfect-power lift with TWO extra exact
3-adic trits, uniformly all m. -/
theorem physical_allones_two_extra_affine_congruence (m : Nat) :
    affineOrbit (ternaryOnes m)%3^(m+2) =
      ternaryOnes m%3^(m+2) := by
  induction m with
  | zero =>
      norm_num [ternaryOnes,affineOrbit]
  | succ m ih =>
      have hpoly :
          peel1 (affineOrbit (ternaryOnes m)) ≡
            peel1 (ternaryOnes m) [MOD 3^(m+2)] := by
        change peel1 (affineOrbit (ternaryOnes m)) % 3^(m+2) =
          peel1 (ternaryOnes m) % 3^(m+2)
        simp [peel1,Nat.add_mod,Nat.mul_mod,Nat.pow_mod,ih]
      have hfixed :
          peel1 (ternaryOnes m) ≡ ternaryOnes m [MOD 3^(m+2)] :=
        peel1_allones_two_extra_trits m
      have htotal := hpoly.trans hfixed
      have hadd := (htotal.mul_left' 3).add_left 1
      change (1+3*peel1 (affineOrbit (ternaryOnes m)))%
          (3*3^(m+2)) = (1+3*ternaryOnes m)%(3*3^(m+2))
        at hadd
      calc
        affineOrbit (ternaryOnes (m+1))%3^((m+1)+2) =
            (1+3*peel1 (affineOrbit (ternaryOnes m)))%
              (3*3^(m+2)) := by
          rw [ternaryOnes,affineOrbit_three_mul_add_one,
              show (m+1)+2=(m+2)+1 by omega,pow_succ]
          ring
        _ = (1+3*ternaryOnes m)%(3*3^(m+2)) := hadd
        _ = ternaryOnes (m+1)%3^((m+1)+2) := by
          rw [ternaryOnes,
              show (m+1)+2=(m+2)+1 by omega,pow_succ]
          ring

/-- Every one of the first m+2 NONTRIVIAL ternary source positions
is zero or one, hence cannot be a shared two with its real neighbor. -/
theorem physical_allones_first_m_plus_two_source_not_two
    (m j : Nat) (hj : j < m + 2) :
    digit3 (4^(ternaryOnes m)) (j+1) ≠ 2 := by
  have hdiv : 3^(j+1) ∣ 3^(m+2) :=
    Nat.pow_dvd_pow 3 (by omega)
  have hmod :
      affineOrbit (ternaryOnes m)%3^(j+1) =
        ternaryOnes m%3^(j+1) := by
    calc
      affineOrbit (ternaryOnes m)%3^(j+1) =
          (affineOrbit (ternaryOnes m)%3^(m+2))%3^(j+1) :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (ternaryOnes m%3^(m+2))%3^(j+1) := by
        rw [physical_allones_two_extra_affine_congruence m]
      _ = ternaryOnes m%3^(j+1) := Nat.mod_mod_of_dvd _ hdiv
  have hsame :
      digit3 (4^(ternaryOnes m)) (j+1) =
        digit3 (ternaryOnes m) j := by
    rw [four_pow_digit_affine_shift]
    exact digit3_eq_of_mod_next _ _ j hmod
  rw [hsame]
  by_cases hlow : j < m
  · rw [ternaryOnes_digit_one m j hlow]
    decide
  · have hpow : 3^m ≤ 3^j := by
      gcongr
      omega
    have hlt : ternaryOnes m < 3^j :=
      lt_of_lt_of_le (ternaryOnes_lt_pow m) hpow
    unfold digit3
    rw [Nat.div_eq_of_lt hlt]
    decide

/-- Every all-one physical exponent survives two additional trits
past its ternary exponent length. -/
theorem physical_allones_survives_m_plus_two_rows (m : Nat) :
    ∀ j : Nat, 1≤j → j ≤ m + 2 →
      ¬ (digit3 (4^(ternaryOnes m)) j = 2 ∧
         digit3 (4^(ternaryOnes m+1)) j = 2) := by
  intro j hj1 hjm hhit
  have hj : j - 1 < m + 2 := by omega
  have hsource :=
    physical_allones_first_m_plus_two_source_not_two m (j-1) hj
  have hshape : j-1+1=j := by omega
  rw [hshape] at hsource
  exact hsource hhit.1

#print axioms peel1_allones_two_extra_trits
#print axioms physical_allones_two_extra_affine_congruence
#print axioms physical_allones_first_m_plus_two_source_not_two
#print axioms physical_allones_survives_m_plus_two_rows

end GSTProblem406GSTPeelExtraPrecision
