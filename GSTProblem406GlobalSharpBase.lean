import GSTFourPowerAffinePrefixIsometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST exact source residual for the ENTIRE K == 4 (mod 9) physical class

This is a quantified congruence on actual finite natural exponents.
It is the 3^5-window algebraic base case for the general sharp
valuation v3(A_K-K) = v3(2*K+1)+2, where v3(2*K+1)>=2.

The finite Fin(243) certificate is exhaustive over exponent
residue classes, NOT a scan over only K<243. Exact affine orbit
periodicity transports all classes to every integer K.
-/

namespace GSTProblem406GlobalSharpBase

open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry

private theorem all_finite_classes :
    ∀ r : Fin 243, r.val%9=4 →
      affineOrbit r.val%243 =
        (r.val+81*((2*r.val+1)/9))%243 := by
  decide

/-- For EVERY natural K ==4 (mod 9), the actual physical affine
source differs from K by the exact normalized expected residue at
modulus 3^5. The statement has NO custom universal gate hypothesis. -/
theorem physical_residual_mod243
    (K : Nat) (hK : K%9=4) :
    affineOrbit K %243 =
      (K+81*((2*K+1)/9))%243 := by
  let r : Nat := K%243
  have hr : r<243 := Nat.mod_lt _ (by decide)
  have hr9 : r%9=4 := by
    have hdiv : 9 ∣ 243 := by decide
    have h := Nat.mod_mod_of_dvd K hdiv
    dsimp [r]
    simpa only [hK] using h
  have hp : affineOrbit K%243=affineOrbit r%243 := by
    have hres : K%243=r%243 := by
      dsimp [r]
      simp
    have h :=
      (affineOrbit_residue_eq_iff_exponent_residue_eq 5 K r).mpr
        (by simpa only [show (3:Nat)^5=243 by decide] using hres)
    simpa only [show (3:Nat)^5=243 by decide] using h
  have hf :
      affineOrbit r%243 =
        (r+81*((2*r+1)/9))%243 :=
    all_finite_classes ⟨r,hr⟩ hr9
  have hdecomp : K = r+243*(K/243) := by
    have h := Nat.mod_add_div K 243
    dsimp [r]
    omega
  have hq : (2*K+1)/9=(2*r+1)/9+54*(K/243) := by
    omega
  have htotal :
      K+81*((2*K+1)/9) =
        (r+81*((2*r+1)/9))+243*19*(K/243) := by
    omega
  have hrhs :
      (K+81*((2*K+1)/9))%243 =
        (r+81*((2*r+1)/9))%243 := by
    rw [htotal]
    simp [Nat.add_mod,Nat.mul_mod]
  exact (hp.trans hf).trans hrhs.symm

#print axioms all_finite_classes
#print axioms physical_residual_mod243

end GSTProblem406GlobalSharpBase
