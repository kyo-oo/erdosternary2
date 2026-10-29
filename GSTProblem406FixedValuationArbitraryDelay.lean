import GSTFourPowerAffineOntologicalCompleteness

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Arbitrarily late physical CommonTwo even at FIXED exponent 3-adic depth

For every prescribed finite horizon B we construct an actual exponent
K>=5 with K%27=4, so v3(2*K+1)=2 exactly, and with no pair
of simultaneous ternary twos in physical rows 1,...,B.

This defeats any proposed proof of the universal hGate that extracts
a collision within m+C from the sharp fixedpoint residual
m=v3(2*K+1), for a universal constant C. It does NOT construct
an all-depth bad natural exponent, and it does NOT refute CommonTwo.
-/

namespace GSTProblem406FixedValuationArbitraryDelay

open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineOntologicalCompleteness

private theorem digit3_four_ne_two (j : Nat) :
    digit3 4 j ≠ 2 := by
  by_cases hj : j < 2
  · interval_cases j <;> norm_num [digit3]
  · have hpow : 3^2 <= 3^j :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    have hlt : 4 < 3^j := by norm_num at hpow; omega
    unfold digit3
    rw [Nat.div_eq_of_lt hlt]
    decide

private theorem digit_prefix_eq
    (p R S j : Nat) (hj : j < p)
    (hmod : R%3^p=S%3^p) :
    digit3 R j = digit3 S j := by
  have hdiv : 3^(j+1) ∣ 3^p :=
    Nat.pow_dvd_pow 3 (by omega)
  apply digit3_eq_of_mod_next
  calc
    R%3^(j+1) = (R%3^p)%3^(j+1) :=
      (Nat.mod_mod_of_dvd _ hdiv).symm
    _ = (S%3^p)%3^(j+1) := by rw [hmod]
    _ = S%3^(j+1) := Nat.mod_mod_of_dvd _ hdiv

/-- A real exponent in the SAME fixed residue K==4 (mod27)
can avoid a simultaneous two beyond any prescribed finite
physical row horizon B. -/
theorem arbitrary_delay_with_fixed_v3_two
    (B : Nat) :
    ∃ K : Nat, 5<=K ∧
      (2*K+1)%27=9 ∧
      ∀ j : Nat, j<B → digit3 (4^K) (j+1) ≠ 2 := by
  let p : Nat := B+3
  obtain ⟨k0,hk0,hcoord⟩ :=
    every_arbitrary_coordinate_has_physical_prefix p 4
  let K := k0+3^p
  have hlarge : 5<=K := by
    have hpow : 3^3 <= 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [p]; omega)
    dsimp [K]
    norm_num at hpow
    omega
  have hrem : K%3^p=k0%3^p := by
    dsimp [K]
    simp [Nat.add_mod]
  have hA :
      affineOrbit K %3^p=4%3^p := by
    have hh :=
      (affineOrbit_residue_eq_iff_exponent_residue_eq p K k0).mpr hrem
    exact hh.trans hcoord
  have hdiv27 : 3^3 ∣ 3^p :=
    Nat.pow_dvd_pow 3 (by dsimp [p]; omega)
  have hlow :
      affineOrbit K%3^3=4%3^3 := by
    calc
      affineOrbit K%3^3 = (affineOrbit K%3^p)%3^3 :=
        (Nat.mod_mod_of_dvd _ hdiv27).symm
      _ = (4%3^p)%3^3 := by rw [hA]
      _ = 4%3^3 := Nat.mod_mod_of_dvd _ hdiv27
  have hfour : affineOrbit 4%3^3=4%3^3 := by
    norm_num [affineOrbit]
  have hK27 : K%27=4 := by
    have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 3 K 4).mp
      (hlow.trans hfour.symm)
    norm_num at h ⊢
    exact h
  have hval : (2*K+1)%27=9 := by omega
  refine ⟨K,hlarge,hval,?_⟩
  intro j hj
  have hjp : j < p := by dsimp [p]; omega
  have hsource :=
    digit_prefix_eq p (affineOrbit K) 4 j hjp hA
  have hp := four_pow_digit_affine_shift K j
  rw [hp,hsource]
  exact digit3_four_ne_two j

#print axioms arbitrary_delay_with_fixed_v3_two

end GSTProblem406FixedValuationArbitraryDelay
