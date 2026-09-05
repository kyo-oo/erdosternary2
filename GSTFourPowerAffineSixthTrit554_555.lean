import GSTFourPowerAffineSixthTrit545_546

namespace GoldbachStatementTernary

/-- Direct sixth-trit constructor for exponent residue `554 mod 729`.

The affine prefix is `512 mod 729`, whose first two ternary digits (low first)
are `2,2`.  A bad channel starting in state `1` is therefore forced to state
`3` after the first digit, and state `3` cannot consume the second digit `2`.
-/
theorem commonTwo_of_mod729_fiveFiveFour {N : ℕ}
    (hmod : N % 729 = 554) :
    CommonTwo N := by
  have hA : affineOrbit N % 729 = 512 := by
    rw [affineOrbit_mod_three_pow_six_eq_of_mod]
    simp [hmod]
  by_contra hno
  have hbad1 : BadChannel (affineOrbit N) 1 :=
    (not_commonTwo_iff_badChannel_one N).mp hno
  have hmod3_0 : affineOrbit N % 3 = 2 := by
    omega
  obtain ⟨h0, hnew0⟩ :=
    (badChannel_one_iff (A := affineOrbit N)).mp hbad1
  have hnew0' : BadChannel ((affineOrbit N - 2) / 3) 3 := by
    rcases hnew0 with h1 | h3
    · omega
    · exact h3
  have hmod9 : affineOrbit N % 9 = 8 := by
    omega
  have hmod3_1 : ((affineOrbit N - 2) / 3) % 3 = 2 := by
    omega
  obtain ⟨hc, _⟩ :=
    (badChannel_three_iff (A := (affineOrbit N - 2) / 3)).mp hnew0'
  omega

/-- Residue `554 mod 729` produces an actual physical Happy row. -/
theorem physical_happy_of_mod729_fiveFiveFour {N : ℕ}
    (hmod : N % 729 = 554) :
    ∃ q : ℕ, 1 ≤ q ∧
      HappyCell (carry4 (4^N) q) (digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy
    (commonTwo_of_mod729_fiveFiveFour hmod)

/-- Direct sixth-trit constructor for exponent residue `555 mod 729`.

The affine prefix is `591 mod 729`, whose first two ternary digits (low first)
are `0,2`.  State `1` is forced to state `0` by the first digit, and state `0`
cannot consume the following digit `2`.
-/
theorem commonTwo_of_mod729_fiveFiveFive {N : ℕ}
    (hmod : N % 729 = 555) :
    CommonTwo N := by
  have hA : affineOrbit N % 729 = 591 := by
    rw [affineOrbit_mod_three_pow_six_eq_of_mod]
    simp [hmod]
  by_contra hno
  have hbad1 : BadChannel (affineOrbit N) 1 :=
    (not_commonTwo_iff_badChannel_one N).mp hno
  have hmod3_0 : affineOrbit N % 3 = 0 := by
    omega
  obtain ⟨h0, hnew0⟩ :=
    (badChannel_one_iff (A := affineOrbit N)).mp hbad1
  have hnew0' : BadChannel (affineOrbit N / 3) 0 := by
    rcases hnew0 with h1 | h3
    · exact h1
    · omega
  have hmod9 : affineOrbit N % 9 = 6 := by
    omega
  have hmod3_1 : (affineOrbit N / 3) % 3 = 2 := by
    omega
  obtain ⟨hc, _⟩ :=
    (badChannel_zero_iff (A := affineOrbit N / 3)).mp hnew0'
  omega

/-- Residue `555 mod 729` produces an actual physical Happy row. -/
theorem physical_happy_of_mod729_fiveFiveFive {N : ℕ}
    (hmod : N % 729 = 555) :
    ∃ q : ℕ, 1 ≤ q ∧
      HappyCell (carry4 (4^N) q) (digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy
    (commonTwo_of_mod729_fiveFiveFive hmod)

/-- Task-3.3-shaped direct relocation for target residue `554 mod 729`.
The source Happy witness is deliberately not transported: the target row is
constructed afresh from the affine bad-channel contradiction. -/
theorem four_power_happy_propagates_of_next_mod729_fiveFiveFour
    {K : ℕ}
    (_h : ∃ p : ℕ, 1 ≤ p ∧
      HappyCell (carry4 (4^K) p) (digit3 (4^K) p))
    (hmod : (K + 1) % 729 = 554) :
    ∃ q : ℕ, 1 ≤ q ∧
      HappyCell (carry4 (4^(K+1)) q) (digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFiveFour (N := K + 1) hmod

/-- Task-3.3-shaped direct relocation for target residue `555 mod 729`. -/
theorem four_power_happy_propagates_of_next_mod729_fiveFiveFive
    {K : ℕ}
    (_h : ∃ p : ℕ, 1 ≤ p ∧
      HappyCell (carry4 (4^K) p) (digit3 (4^K) p))
    (hmod : (K + 1) % 729 = 555) :
    ∃ q : ℕ, 1 ≤ q ∧
      HappyCell (carry4 (4^(K+1)) q) (digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFiveFive (N := K + 1) hmod

end GoldbachStatementTernary
