import GSTProblem406HalfExponentEscape

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact FIRST original physical HGate on delayed half-exponent family

For each m>=8 and K=(3^m-1)/2, the first same-row two in the
original actual powers 4^K and 4^(K+1) is at row m+9.
This is a pointwise theorem over an unbounded infinite family, not
an assumption of the universal gate.
-/

namespace GSTProblem406HalfExponentFirstGate

open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit
open GSTProblem406HalfExponentEscape

theorem halfIndex_succ (m : Nat) :
    halfIndex (m+1)=1+3*halfIndex m := by
  change halfIndex m+3^m=1+3*halfIndex m
  have h := halfIndex_twice_plus_one m
  omega

/-- Every low ternary digit of (3^m-1)/2 is exactly one. -/
theorem halfIndex_digit_one :
    ∀ m j : Nat, j<m → digit3 (halfIndex m) j=1 := by
  intro m
  induction m with
  | zero =>
      intro j hj
      omega
  | succ m ih =>
      intro j hj
      cases j with
      | zero =>
          rw [halfIndex_succ]
          norm_num [digit3]
      | succ j =>
          rw [halfIndex_succ]
          have hs := GSTCanonicalTailStateIso.prefix_slice_digit_exact
            1 1 (halfIndex m) j (by norm_num : 1 < 3^1)
          have hi := ih j (by omega)
          simpa [GSTCanonicalTailStateIso.digit3,
            GSTFourPowerDirectResidue.digit3,
            Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs.trans hi

private theorem digit_eq_from_prefix (p R S j : Nat)
    (hj : j < p) (hmod : R%3^p=S%3^p) :
    digit3 R j = digit3 S j := by
  have hdiv : 3^(j+1) ∣ 3^p := Nat.pow_dvd_pow 3 (by omega)
  apply digit3_eq_of_mod_next
  calc
    R%3^(j+1) = (R%3^p)%3^(j+1) :=
      (Nat.mod_mod_of_dvd _ hdiv).symm
    _ = (S%3^p)%3^(j+1) := by rw [hmod]
    _ = S%3^(j+1) := Nat.mod_mod_of_dvd _ hdiv

/-- Below the exponent-prefix cut, the physical affine source
has the literal digit one; this is a theorem about 4^K. -/
theorem half_physical_source_low_one (m j : Nat) (hj : j < m) :
    digit3 (affineOrbit (halfIndex m)) j=1 := by
  have hh := halfIndex_twice_plus_one m
  have hsmall : halfIndex m < 3^m := by omega
  have hmod : affineOrbit (halfIndex m)%3^m=halfIndex m%3^m := by
    rw [physical_half_affine_decomposition]
    simp [Nat.add_mod,Nat.mul_mod]
  exact (digit_eq_from_prefix m _ _ j hj hmod).trans
    (halfIndex_digit_one m j hj)

/-- The untruncated all-scale source post-prefix digit law. -/
theorem half_source_postcut_digit (m j : Nat) :
    digit3 (affineOrbit (halfIndex m)) (m+j) =
      digit3 (antiCoeff m/2) j := by
  have hh := halfIndex_twice_plus_one m
  have hsmall : halfIndex m < 3^m := by omega
  rw [physical_half_affine_decomposition]
  have hs := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    m (halfIndex m) (antiCoeff m/2) j hsmall
  simpa [GSTCanonicalTailStateIso.digit3,
    GSTFourPowerDirectResidue.digit3,
    Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs

/-- The original neighbor post-prefix is the exact 4e+1 channel. -/
theorem half_neighbor_postcut_digit (m j : Nat) :
    digit3 (affineOrbit (halfIndex m+1)) (m+j) =
      digit3 (4*(antiCoeff m/2)+1) j := by
  have hpos : 0<3^m := by positivity
  have hsmall : 3^m-1 < 3^m := by omega
  rw [physical_half_neighbor_decomposition]
  have hs := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    m (3^m-1) (4*(antiCoeff m/2)+1) j hsmall
  simpa [GSTCanonicalTailStateIso.digit3,
    GSTFourPowerDirectResidue.digit3,
    Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs

/-- The first eight trits of the two stabilized exact quotient
residues have no simultaneous two. -/
theorem constant_pair_no_common_before_eight
    (j : Nat) (hj : j<8) :
    ¬ (digit3 14049 j=2 ∧ digit3 16831 j=2) := by
  interval_cases j <;> norm_num [digit3] at *

/-- Exact first-gate exclusion after the low-prefix part, below
the critical ninth postcut digit. -/
theorem half_no_postcut_pair_before_eight
    (m j : Nat) (hm : 8 ≤ m) (hj : j<8) :
    ¬ (digit3 (affineOrbit (halfIndex m)) (m+j)=2 ∧
       digit3 (affineOrbit (halfIndex m+1)) (m+j)=2) := by
  rw [half_source_postcut_digit,half_neighbor_postcut_digit]
  have hE : (antiCoeff m/2)%19683=14049 :=
    antiCoeff_half_mod m hm
  have hN : (4*(antiCoeff m/2)+1)%19683=16831 :=
    antiCoeff_neighbor_half_mod m hm
  have hS : digit3 (antiCoeff m/2) j=digit3 14049 j := by
    apply digit_eq_from_prefix 9 _ _ j (by omega)
    norm_num at hE ⊢
    exact hE
  have hT : digit3 (4*(antiCoeff m/2)+1) j=digit3 16831 j := by
    apply digit_eq_from_prefix 9 _ _ j (by omega)
    norm_num at hN ⊢
    exact hN
  rw [hS,hT]
  exact constant_pair_no_common_before_eight j hj

/-- No affine source-neighbor collision at any location below m+8,
including the arbitrarily long m-digit literal-one prefix. -/
theorem half_no_affine_pair_before_ninth
    (m j : Nat) (hm : 8 ≤ m) (hj : j < m+8) :
    ¬ (digit3 (affineOrbit (halfIndex m)) j=2 ∧
       digit3 (affineOrbit (halfIndex m+1)) j=2) := by
  by_cases hlow : j < m
  · intro h
    have h1 := half_physical_source_low_one m j hlow
    omega
  · have hshape : j=m+(j-m) := by omega
    rw [hshape]
    exact half_no_postcut_pair_before_eight m (j-m) hm (by omega)

/-- Actual first common-two position in the ORIGINAL powers, including
the compulsory low-one physical row. -/
theorem half_exponents_first_gate_exact
    (m : Nat) (hm : 8 ≤ m) :
    (digit3 (4^(halfIndex m)) (m+9)=2 ∧
     digit3 (4^(halfIndex m+1)) (m+9)=2) ∧
    (∀ p : Nat, p < m+9 →
      ¬ (digit3 (4^(halfIndex m)) p=2 ∧
         digit3 (4^(halfIndex m+1)) p=2)) := by
  constructor
  · have hs := physical_half_source_ninth_digit m hm
    have hn := physical_half_neighbor_ninth_digit m hm
    constructor
    · have h := (four_pow_digit_affine_shift (halfIndex m) (m+8)).trans hs
      simpa [Nat.add_assoc] using h
    · have h := (four_pow_digit_affine_shift (halfIndex m+1) (m+8)).trans hn
      simpa [Nat.add_assoc] using h
  · intro p hp
    cases p with
    | zero =>
        intro h
        have hzero := pow4_mod3_one (halfIndex m)
        unfold digit3 at h
        norm_num at hzero
        omega
    | succ j =>
        intro h
        have hs := (four_pow_digit_affine_shift (halfIndex m) j).symm
        have hn := (four_pow_digit_affine_shift (halfIndex m+1) j).symm
        have hpair :
            digit3 (affineOrbit (halfIndex m)) j=2 ∧
            digit3 (affineOrbit (halfIndex m+1)) j=2 := by
          constructor
          · rw [← four_pow_digit_affine_shift]
            simpa [Nat.succ_eq_add_one] using h.1
          · rw [← four_pow_digit_affine_shift]
            simpa [Nat.succ_eq_add_one] using h.2
        exact half_no_affine_pair_before_ninth m j hm (by omega) hpair

#print axioms halfIndex_digit_one
#print axioms half_no_affine_pair_before_ninth
#print axioms half_exponents_first_gate_exact
end GSTProblem406HalfExponentFirstGate
