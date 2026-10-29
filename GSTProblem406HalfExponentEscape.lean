import GSTFourPowerAffineOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST physical half-exponent first gate: 3-adic anti-LTE source

For the actual perfect-power exponents H_m=(3^m-1)/2, prove
a new exact coefficient recurrence, stabilize its physical quotient
modulo 3^9, and extract an original same-row 2 for all m>=8.

No hGate premise, no generic arbitrary source and no custom axiom.
-/
namespace GSTProblem406HalfExponentEscape

open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit

/-- The integer exponent (3^m-1)/2 defined by an exact recurrence. -/
def halfIndex : Nat → Nat
  | 0 => 0
  | m+1 => halfIndex m + 3^m

theorem halfIndex_twice_plus_one : ∀ m : Nat,
    2 * halfIndex m + 1 = 3^m
  | 0 => by decide
  | m+1 => by
      have ih := halfIndex_twice_plus_one m
      simp only [halfIndex, Nat.pow_succ]
      omega

/-- The exact nonnegative 3-adic quotient
(2^(3^m)+1)/3^(m+1), with no massive division in the definition. -/
def antiCoeff : Nat → Nat
  | 0 => 1
  | m+1 =>
      let d := antiCoeff m
      d + 3^(m+1) * d^2 * (3^m * d - 1)

theorem antiCoeff_pos : ∀ m : Nat, 0 < antiCoeff m
  | 0 => by decide
  | m+1 => by
      have ih := antiCoeff_pos m
      change 0 < antiCoeff m +
        3^(m+1)*(antiCoeff m)^2*(3^m*antiCoeff m-1)
      omega

/-- Noncircular all-scale anti-LTE identity. -/
theorem antiCoeff_exact : ∀ m : Nat,
    2^(3^m)+1 = 3^(m+1) * antiCoeff m
  | 0 => by decide
  | m+1 => by
      let S := 2^(3^m)
      let T := 3^(m+1)
      let d := antiCoeff m
      have ih : S+1 = T*d := antiCoeff_exact m
      have hd : 0 < d := antiCoeff_pos m
      have hpos : 1 ≤ 3^m*d := by
        have hp : 0 < 3^m := by positivity
        dsimp [d] at hd
        omega
      have hsubtract : (3^m*d-1)+1=3^m*d :=
        Nat.sub_add_cancel hpos
      have hT : T=3*3^m := by
        dsimp [T]
        rw [pow_succ]
        ring
      have hcube :
          S^3+1+3*T^2*d^2 = T^3*d^3+3*T*d := by
        calc
          S^3+1+3*T^2*d^2 =
            S^3+1+3*(S+1)^2 := by rw [ih]; ring
          _ = (S+1)^3+3*(S+1) := by ring
          _ = T^3*d^3+3*T*d := by rw [ih]; ring
      have hnext :
          3^(m+2)*antiCoeff (m+1) =
            3*T*d + 3*T^2*d^2*(3^m*d-1) := by
        have hdef : antiCoeff (m+1) =
            d+T*d^2*(3^m*d-1) := rfl
        rw [hdef]
        have hpow : 3^(m+2)=3*T := by
          dsimp [T]
          rw [show m+2=(m+1)+1 by omega, pow_succ]
          ring
        rw [hpow]
        ring
      have hlink :
          3*T*d + 3*T^2*d^2*(3^m*d-1)+3*T^2*d^2 =
            T^3*d^3+3*T*d := by
        calc
          3*T*d + 3*T^2*d^2*(3^m*d-1)+3*T^2*d^2 =
            3*T*d + 3*T^2*d^2*((3^m*d-1)+1) := by ring
          _ = 3*T*d+3*T^2*d^2*(3^m*d) := by rw [hsubtract]
          _ = T^3*d^3+3*T*d := by rw [hT]; ring
      have hraw : S^3+1=3^(m+2)*antiCoeff (m+1) := by
        omega
      calc
        2^(3^(m+1))+1 = S^3+1 := by
          dsimp [S]
          rw [pow_succ, pow_mul]
        _ = 3^((m+1)+1)*antiCoeff (m+1) := by
          convert hraw using 1 <;> congr 1 <;> omega

/-- The anti-LTE coefficient stabilizes at every resolution
3^w once the scale m is at least w-1. -/
theorem antiCoeff_step_mod (m w : Nat) (hw : w ≤ m+1) :
    antiCoeff (m+1)%3^w = antiCoeff m%3^w := by
  have hdiv : 3^w ∣ 3^(m+1) := Nat.pow_dvd_pow 3 hw
  change
    (antiCoeff m+3^(m+1)*(antiCoeff m)^2*
      (3^m*antiCoeff m-1))%3^w = antiCoeff m%3^w
  have hz : (3^(m+1)*(antiCoeff m)^2*
      (3^m*antiCoeff m-1))%3^w=0 := by
    exact Nat.mod_eq_zero_of_dvd
      (dvd_mul_of_dvd_left hdiv _)
  rw [Nat.add_mod, hz]
  simp

/-- Once m>=8, the nine-trit anti-LTE fingerprint is constant. -/
theorem antiCoeff_mod_nine_stable (t : Nat) :
    antiCoeff (8+t)%3^9=antiCoeff 8%3^9 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h := antiCoeff_step_mod (8+t) 9 (by omega)
      rw [show 8+(t+1)=(8+t)+1 by omega, h]
      exact ih

/-- Exact finite 3-adic base coefficient. -/
theorem antiCoeff_eight_mod : antiCoeff 8%19683=8416 := by
  native_decide

/-- The stable integer quotient fingerprint for every large m. -/
theorem antiCoeff_all_large_mod (m : Nat) (hm : 8 ≤ m) :
    antiCoeff m%19683=8416 := by
  obtain ⟨t,rfl⟩ : ∃ t : Nat, m=8+t := ⟨m-8,by omega⟩
  have h := antiCoeff_mod_nine_stable t
  norm_num at h ⊢
  rw [h]
  exact antiCoeff_eight_mod

/-- The original perfect power is exactly the physical anti-LTE source,
not a generic 3-adic surrogate. -/
theorem physical_antiCoeff_exact (m : Nat) :
    2 * 4^(halfIndex m)+1=3^(m+1)*antiCoeff m := by
  calc
    2*4^(halfIndex m)+1 =
        2^(2*halfIndex m+1)+1 := by
      rw [pow_succ, pow_mul]
      norm_num
    _ = 2^(3^m)+1 := by rw [halfIndex_twice_plus_one m]
    _ = 3^(m+1)*antiCoeff m := antiCoeff_exact m

/-- From the exact physical identity, the anti-LTE quotient is odd. -/
theorem antiCoeff_odd (m : Nat) : antiCoeff m%2=1 := by
  have heq := physical_antiCoeff_exact m
  have hpow : 3^(m+1)%2=1 := by
    rw [Nat.pow_mod]
    norm_num
  have hodd : (3^(m+1)*antiCoeff m)%2=1 := by omega
  rw [Nat.mul_mod,hpow] at hodd
  omega

/-- The exact original 4-power affine coordinate decomposes into
m literal low ternary ones, followed by the physical quotient d_m/2. -/
theorem physical_half_affine_decomposition (m : Nat) :
    affineOrbit (halfIndex m) =
      halfIndex m + 3^m*(antiCoeff m/2) := by
  have hsource := physical_antiCoeff_exact m
  have hpower := four_pow_eq_one_plus_three_affineOrbit (halfIndex m)
  rw [hpower] at hsource
  have hp : 3^(m+1)=3*3^m := by rw [pow_succ]; ring
  rw [hp] at hsource
  have hA : 2*affineOrbit (halfIndex m)+1=3^m*antiCoeff m := by
    omega
  have hh := halfIndex_twice_plus_one m
  have hdodd := antiCoeff_odd m
  have hddecomp : antiCoeff m=2*(antiCoeff m/2)+1 := by
    have h := Nat.mod_add_div (antiCoeff m) 2
    rw [hdodd] at h
    omega
  rw [hddecomp] at hA
  omega

/-- The next actual 4-power affine coordinate has exactly the
neighbor tail 4*(d_m/2)+1 above m low ternary twos. -/
theorem physical_half_neighbor_decomposition (m : Nat) :
    affineOrbit (halfIndex m+1) =
      (3^m-1)+3^m*(4*(antiCoeff m/2)+1) := by
  have hh := halfIndex_twice_plus_one m
  have hsplit := physical_half_affine_decomposition m
  rw [affineOrbit_succ, hsplit]
  have hpos : 1 ≤ 3^m := by positivity
  omega

/-- The certified nine-trit source quotient residue is 14049. -/
theorem antiCoeff_half_mod (m : Nat) (hm : 8 ≤ m) :
    (antiCoeff m/2)%19683=14049 := by
  have hmod := antiCoeff_all_large_mod m hm
  have hodd := antiCoeff_odd m
  omega

/-- Its actual source-neighbor quotient residue is 16831. -/
theorem antiCoeff_neighbor_half_mod (m : Nat) (hm : 8 ≤ m) :
    (4*(antiCoeff m/2)+1)%19683=16831 := by
  have hmod := antiCoeff_half_mod m hm
  omega

/-- Actual physical affine source digit from the quotient fingerprint. -/
theorem physical_half_source_ninth_digit (m : Nat) (hm : 8 ≤ m) :
    digit3 (affineOrbit (halfIndex m)) (m+8)=2 := by
  have hh := halfIndex_twice_plus_one m
  have hsmall : halfIndex m < 3^m := by omega
  rw [physical_half_affine_decomposition]
  have hslice := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    m (halfIndex m) (antiCoeff m/2) 8 hsmall
  have hmod := antiCoeff_half_mod m hm
  have hdigit : digit3 (antiCoeff m/2) 8 = 2 := by
    apply (digit3_eq_of_mod_next
      (antiCoeff m/2) 14049 8 ?_).trans
      (by norm_num [digit3])
    simpa only [show (3:Nat)^(8+1)=19683 by norm_num] using hmod
  simpa [GSTCanonicalTailStateIso.digit3,
    GSTFourPowerDirectResidue.digit3, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using hslice.trans hdigit

/-- Actual physical affine neighbor digit at the identical position. -/
theorem physical_half_neighbor_ninth_digit (m : Nat) (hm : 8 ≤ m) :
    digit3 (affineOrbit (halfIndex m+1)) (m+8)=2 := by
  have hpos : 1 ≤ 3^m := by positivity
  have hsmall : 3^m-1<3^m := by omega
  rw [physical_half_neighbor_decomposition]
  have hslice := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    m (3^m-1) (4*(antiCoeff m/2)+1) 8 hsmall
  have hmod := antiCoeff_neighbor_half_mod m hm
  have hdigit : digit3 (4*(antiCoeff m/2)+1) 8=2 := by
    apply (digit3_eq_of_mod_next
      (4*(antiCoeff m/2)+1) 16831 8 ?_).trans
      (by norm_num [digit3])
    simpa only [show (3:Nat)^(8+1)=19683 by norm_num] using hmod
  simpa [GSTCanonicalTailStateIso.digit3,
    GSTFourPowerDirectResidue.digit3, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using hslice.trans hdigit

/-- UNCONDITIONAL physical hGate-body witness on every real
H_m=(3^m-1)/2, m>=8, at exact row m+9. -/
theorem original_common_two_half_exponents
    (m : Nat) (hm : 8 ≤ m) :
    GSTFourPowerDirectExistence.CommonTwo (halfIndex m) := by
  refine ⟨m+9,by omega,?_,?_⟩
  · have h := physical_half_source_ninth_digit m hm
    convert (four_pow_digit_affine_shift (halfIndex m) (m+8)).trans h using 1 <;> omega
  · have h := physical_half_neighbor_ninth_digit m hm
    convert (four_pow_digit_affine_shift (halfIndex m+1) (m+8)).trans h using 1 <;> omega

#print axioms antiCoeff_exact
#print axioms antiCoeff_mod_nine_stable
#print axioms antiCoeff_eight_mod
#print axioms physical_half_affine_decomposition
#print axioms original_common_two_half_exponents
end GSTProblem406HalfExponentEscape
