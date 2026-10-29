import GSTProblem406HalfExponentEscape
import GSTWorldtraceBlockLift

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST exact half-exponent multiplier coefficient

At m>=8, the original physical source coefficient
4^H_m * LTEcoeff_m has a stable nine-digit fingerprint 8416,
where H_m=(3^m-1)/2.

Proves the exact uniform coefficient needed to discharge the
original physical hGate on many multiplier-residue classes.
-/

namespace GSTProblem406HalfMultiplierArithmetic

open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit
open GSTProblem406HalfExponentEscape

private theorem canonical_coefficient_step_mod (m w : Nat)
    (hw : w ≤ m+1) :
    GSTCanonicalTailLTE.lteCoeff (m+1)%3^w =
      GSTCanonicalTailLTE.lteCoeff m%3^w := by
  let c := GSTCanonicalTailLTE.lteCoeff m
  change (c+3^(m+1)*c^2+3^(2*m+1)*c^3)%3^w=c%3^w
  have hd1 : 3^w ∣ 3^(m+1) := Nat.pow_dvd_pow 3 hw
  have hd2 : 3^w ∣ 3^(2*m+1) := Nat.pow_dvd_pow 3 (by omega)
  have hz1 : (3^(m+1)*c^2)%3^w=0 :=
    Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd1 _)
  have hz2 : (3^(2*m+1)*c^3)%3^w=0 :=
    Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd2 _)
  rw [Nat.add_mod,Nat.add_mod,hz1,hz2]
  simp

private theorem canonical_coefficient_mod_stable (t : Nat) :
    GSTCanonicalTailLTE.lteCoeff (8+t)%3^9 =
      GSTCanonicalTailLTE.lteCoeff 8%3^9 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h := canonical_coefficient_step_mod (8+t) 9 (by omega)
      rw [show 8+(t+1)=(8+t)+1 by omega,h]
      exact ih

/-- Kernel-evaluated finite canonical LTE coefficient at scale eight. -/
theorem canonical_coefficient_eight_mod :
    GSTCanonicalTailLTE.lteCoeff 8%19683=2851 := by
  decide

/-- Every canonical GST LTE coefficient at m>=8 has the
same exact nine-digit residue. -/
theorem canonical_coefficient_all_large_mod (m : Nat) (hm : 8 ≤ m) :
    GSTCanonicalTailLTE.lteCoeff m%19683=2851 := by
  obtain ⟨t,rfl⟩ : ∃t:Nat,m=8+t := ⟨m-8,by omega⟩
  have h := canonical_coefficient_mod_stable t
  norm_num at h ⊢
  rw [h]
  exact canonical_coefficient_eight_mod

/-- The physical multiplicand 4^H_m is a 3-adic half-negative
unit at the exact nine-trit resolution. -/
theorem physical_half_power_mod (m : Nat) (hm : 8 ≤ m) :
    4^(halfIndex m)%19683=9841 := by
  have hphys := physical_antiCoeff_exact m
  have hdiv : (19683:Nat) ∣ 3^(m+1) := by
    have hp : 3^9 ∣ 3^(m+1) := Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^9=19683 by norm_num] using hp
  have hzero : (2*4^(halfIndex m)+1)%19683=0 := by
    rw [hphys]
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hdiv _)
  omega

/-- Exact original physical multiplicative block coefficient
modulo 3^9. The residue is the same 8416 as the anti-LTE
coefficient, for ALL m>=8. -/
theorem physical_multiplier_coefficient_mod (m : Nat) (hm : 8 ≤ m) :
    (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m))%19683=8416 := by
  have hc := canonical_coefficient_all_large_mod m hm
  have hw := physical_half_power_mod m hm
  calc
    (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m))%19683 =
      ((GSTCanonicalTailLTE.lteCoeff m%19683)*
        (4^(halfIndex m)%19683))%19683 :=
        Nat.mul_mod _ _ _
    _ = (2851*9841)%19683 := by rw [hc,hw]
    _ = 8416 := by decide

#print axioms canonical_coefficient_eight_mod
#print axioms canonical_coefficient_all_large_mod
#print axioms physical_half_power_mod
#print axioms physical_multiplier_coefficient_mod

end GSTProblem406HalfMultiplierArithmetic
