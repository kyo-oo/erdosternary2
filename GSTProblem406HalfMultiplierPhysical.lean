import GSTProblem406HalfMultiplierArithmetic
import GSTWorldtraceBlockLift

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# One original-source GST nine-trit block for ALL upper exponent multipliers

For K=halfIndex m+u*3^m, m>=8, these are exact physical
powers, not a digit controller surrogate:
 source quotient mod3^9 = (14049+8416u) mod3^9
 neighbor quotient mod3^9 = (4*(14049+8416u)+1) mod3^9.
The certified finite-state Good9 predicate gives a precise physical
CommonTwo row for every such multiplier.
-/
namespace GSTProblem406HalfMultiplierPhysical

open GSTProblem406HalfExponentEscape
open GSTProblem406HalfMultiplierArithmetic
open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit

private theorem power_quotient_affine (K m : Nat) :
    4^K/3^(m+1)=affineOrbit K/3^m := by
  let N := 3^m
  let A := affineOrbit K
  have hN : 0<N := by dsimp [N]; positivity
  have hr : A%N < N := Nat.mod_lt _ hN
  have hshape : 4^K=(1+3*(A%N))+(3*N)*(A/N) := by
    have ha : A=A%N+N*(A/N) :=
      (Nat.mod_add_div A N).symm
    calc
      4^K=1+3*A := four_pow_eq_one_plus_three_affineOrbit K
      _ = 1+3*(A%N+N*(A/N)) := by rw [← ha]
      _ = (1+3*(A%N))+(3*N)*(A/N) := by ring
  have hlow : 1+3*(A%N)<3*N := by omega
  have hpow : 3^(m+1)=3*N := by
    dsimp [N]
    rw [pow_succ]
    ring
  rw [hshape,hpow,Nat.add_mul_div_left _ _ (by omega:0<3*N)]
  rw [Nat.div_eq_of_lt hlow]
  dsimp only [A,N]
  omega

private theorem half_power_source_quotient (m : Nat) :
    4^(halfIndex m)/3^(m+1)=antiCoeff m/2 := by
  rw [power_quotient_affine,physical_half_affine_decomposition]
  have hsmall : halfIndex m < 3^m := by
    have h := halfIndex_twice_plus_one m
    omega
  rw [Nat.add_mul_div_left _ _ (by positivity : 0<3^m)]
  rw [Nat.div_eq_of_lt hsmall]
  omega

private theorem half_power_neighbor_quotient (m : Nat) :
    4^(halfIndex m+1)/3^(m+1)=4*(antiCoeff m/2)+1 := by
  rw [power_quotient_affine,physical_half_neighbor_decomposition]
  have hsmall : 3^m-1<3^m := by
    have hp : 0<3^m := by positivity
    omega
  rw [Nat.add_mul_div_left _ _ (by positivity : 0<3^m)]
  rw [Nat.div_eq_of_lt hsmall]
  omega

/-- Exact original physical source quotient nine-trit readback
for all m>=8 and every unbounded natural u. -/
theorem half_multiplier_source_nine
    (m u : Nat) (hm : 8 ≤ m) :
    (4^(halfIndex m+u*3^m)/3^(m+1))%19683 =
      (14049+8416*u)%19683 := by
  have hblock :=
    GSTWorldtraceBlockLift.pow4_whole_block_lift
      (halfIndex m) u m 9 (by omega) (by omega)
  have hbase := half_power_source_quotient m
  have hco := physical_multiplier_coefficient_mod m hm
  have he := antiCoeff_half_mod m hm
  have hsum :
      (antiCoeff m/2+u*
         (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m)))%19683 =
      (14049+8416*u)%19683 := by
    have hC : GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m) ≡
        8416 [MOD 19683] := hco
    have hE : antiCoeff m/2 ≡ 14049 [MOD 19683] := he
    have h := (hC.mul_left u).add hE
    change
      (u*(GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m))+
        antiCoeff m/2)%19683 = (u*8416+14049)%19683 at h
    simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_assoc] using h
  calc
    (4^(halfIndex m+u*3^m)/3^(m+1))%19683 =
      (4^(halfIndex m)/3^(m+1)+
        u*GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m))%19683 := by
          simpa only [show (3:Nat)^9=19683 by decide] using hblock
    _ = (antiCoeff m/2+u*
         (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m)))%19683 := by
          rw [hbase]
          congr 1
          ring
    _ = (14049+8416*u)%19683 := hsum

/-- The neighbor quotient is the exact 4x+1 translate of the
source residue, not a different arbitrarily chosen coordinate. -/
theorem half_multiplier_neighbor_nine
    (m u : Nat) (hm : 8 ≤ m) :
    (4^((halfIndex m+u*3^m)+1)/3^(m+1))%19683 =
      (4*(14049+8416*u)+1)%19683 := by
  have hblock :=
    GSTWorldtraceBlockLift.pow4_whole_block_lift
      (halfIndex m+1) u m 9 (by omega) (by omega)
  have hbase := half_power_neighbor_quotient m
  have hsource := half_multiplier_source_nine m u hm
  have hsourceSUM :
      (antiCoeff m/2+u*
        (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m)))%19683 =
      (14049+8416*u)%19683 := by
    have hC : GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m) ≡
        8416 [MOD 19683] :=
      physical_multiplier_coefficient_mod m hm
    have hE : antiCoeff m/2 ≡ 14049 [MOD 19683] :=
      antiCoeff_half_mod m hm
    have h := (hC.mul_left u).add hE
    change
      (u*(GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m))+
        antiCoeff m/2)%19683 = (u*8416+14049)%19683 at h
    simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_assoc] using h
  have hN :
      (4*(antiCoeff m/2+u*
        (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m)))+1)%19683 =
      (4*(14049+8416*u)+1)%19683 := by
    have h : 4*(antiCoeff m/2+u*
        (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m))) ≡
      4*(14049+8416*u) [MOD 19683] :=
        (show (antiCoeff m/2+u*
          (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m))) ≡
            14049+8416*u [MOD 19683] from hsourceSUM).mul_left 4
    have h' := h.add_left 1
    change
      (1+4*(antiCoeff m/2+u*
        (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m))))%19683 =
      (1+4*(14049+8416*u))%19683 at h'
    simpa only [Nat.add_comm] using h'
  have hfour : 4^(halfIndex m+1)=4*4^(halfIndex m) := by
    rw [pow_succ]
    ring
  have heqExp : (halfIndex m+u*3^m)+1 =
      (halfIndex m+1)+u*3^m := by omega
  calc
    (4^((halfIndex m+u*3^m)+1)/3^(m+1))%19683 =
      (4^((halfIndex m+1)+u*3^m)/3^(m+1))%19683 := by
        rw [heqExp]
    _ = (4^(halfIndex m+1)/3^(m+1)+u*
      GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m+1))%19683 := by
        simpa only [show (3:Nat)^9=19683 by decide] using hblock
    _ = (4*(antiCoeff m/2+u*
        (GSTCanonicalTailLTE.lteCoeff m*4^(halfIndex m)))+1)%19683 := by
        rw [hbase,hfour]
        congr 1
        ring
    _ = (4*(14049+8416*u)+1)%19683 := hN

/-- Original nine-trit finite physical multiplier gate certificate.
It is explicitly decidable in u modulo 3^9, and never assumes hGate. -/
def NineGood (u : Nat) : Prop :=
  ∃ j : Nat, j<9 ∧
    digit3 (14049+8416*u) j=2 ∧
    digit3 (4*(14049+8416*u)+1) j=2

private theorem digit_preserved_from_nine
    (R S j : Nat) (hj : j<9)
    (hmod : R%19683=S%19683) :
    digit3 R j=digit3 S j := by
  have hdiv : 3^(j+1) ∣ 19683 := by
    have hh : 3^(j+1) ∣ 3^9 := Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^9=19683 by decide] using hh
  apply digit3_eq_of_mod_next
  calc
    R%3^(j+1) = (R%19683)%3^(j+1) :=
      (Nat.mod_mod_of_dvd _ hdiv).symm
    _ = (S%19683)%3^(j+1) := by rw [hmod]
    _ = S%3^(j+1) := Nat.mod_mod_of_dvd _ hdiv

private theorem postcut_digit (P m j : Nat) :
    digit3 P (m+1+j)=digit3 (P/3^(m+1)) j := by
  unfold digit3
  have hp : 3^(m+1+j)=3^(m+1)*3^j := by rw [pow_add]
  rw [hp,← Nat.div_div_eq_div_mul]

/-- UNCONDITIONAL original physical CommonTwo for all natural u
with the explicit nine-digit arithmetic certificate, at every
arbitrarily large scale m>=8. -/
theorem half_multiplier_original_common_two
    (m u : Nat) (hm : 8 ≤ m) (hgood : NineGood u) :
    GSTFourPowerDirectExistence.CommonTwo
      (halfIndex m+u*3^m) := by
  obtain ⟨j,hj,hs,hn⟩ := hgood
  let K := halfIndex m+u*3^m
  refine ⟨m+1+j,by omega,?_,?_⟩
  · rw [postcut_digit]
    have h := half_multiplier_source_nine m u hm
    exact (digit_preserved_from_nine
      (4^K/3^(m+1)) (14049+8416*u) j hj (by simpa [K] using h)).trans hs
  · rw [postcut_digit]
    have h := half_multiplier_neighbor_nine m u hm
    exact (digit_preserved_from_nine
      (4^(K+1)/3^(m+1)) (4*(14049+8416*u)+1) j hj
      (by simpa [K] using h)).trans hn

#print axioms half_multiplier_source_nine
#print axioms half_multiplier_neighbor_nine
#print axioms half_multiplier_original_common_two
end GSTProblem406HalfMultiplierPhysical
