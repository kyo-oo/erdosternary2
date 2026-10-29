import GSTProblem406GSTPeelExtraPrecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Sharp GST nonlinear-peel escape for physical ternary-one exponents

Earlier GSTPeelExtraPrecision proves that A_(s_m) and s_m agree
modulo 3^(m+2), where 2*s_m+1=3^m and A_K=(4^K-1)/3.
Here we establish the precise first failure of that congruence:
A_(s_m)=s_m+3^(m+2)*d_m, with d_m == 1 (mod 3), all m>=2.

This is a fully finite exact theorem for true physical 4-power
exponents, not a proof of universal CommonTwo and not a
hypothesis replacing the original hGate.
-/

namespace GSTProblem406SharpPeelResidual

open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel
open GSTProblem406GSTPeelFixedPoint
open GSTProblem406GSTPeelExtraPrecision

/-- Exact divided difference of the GST ternary-one peel polynomial. -/
def peelGain (s delta : Nat) : Nat :=
  4 + 24*s + 36*s^2 + 12*delta + 36*s*delta + 12*delta^2

theorem peel1_add_delta (s delta : Nat) :
    peel1 (s+delta)=peel1 s+delta*peelGain s delta := by
  unfold peel1 peelGain
  ring

/-- The exact nonlinear gain is always congruent to one modulo 3. -/
theorem peelGain_mod_three (s delta : Nat) :
    peelGain s delta % 3 = 1 := by
  simp [peelGain,Nat.add_mod,Nat.mul_mod]

private theorem scales_for_sharp_step (m : Nat) (hm : 2<=m) :
    3^m=3^(m-1)*3 ∧
    3^(m+2)=3^(m-1)*27 ∧
    3^((m+1)+2)=3^(m-1)*81 := by
  have em : m=(m-1)+1 := by omega
  constructor
  · conv_lhs => rw [em]
    rw [pow_succ]
  constructor
  · have e : m+2=(m-1)+3 := by omega
    rw [e,pow_add]
    norm_num
  · have e : (m+1)+2=(m-1)+4 := by omega
    rw [e,pow_add]
    norm_num

/-- Exact GST residual step. The extra correction term is divisible
by 3 because m>=2, so the normalized 3-adic unit persists. -/
theorem sharp_peel_step
    (m d : Nat) (hm : 2<=m)
    (h : affineOrbit (ternaryOnes m) =
      ternaryOnes m+3^(m+2)*d) :
    affineOrbit (ternaryOnes (m+1)) =
      ternaryOnes (m+1)+3^((m+1)+2)*
        (d*peelGain (ternaryOnes m) (3^(m+2)*d)+
          3^(m-1)*ternaryOnes m) := by
  obtain ⟨hp1,hp2,hp3⟩ := scales_for_sharp_step m hm
  have hs : 2*ternaryOnes m+1=3^m :=
    ternaryOnes_identity m
  have hnext : ternaryOnes (m+1)=3*ternaryOnes m+1 := rfl
  have horbit :
      affineOrbit (ternaryOnes (m+1)) =
        1+3*peel1 (affineOrbit (ternaryOnes m)) := by
    rw [hnext,affineOrbit_three_mul_add_one]
  calc
    affineOrbit (ternaryOnes (m+1)) =
        1+3*peel1
          (ternaryOnes m+3^(m+2)*d) := by rw [horbit,h]
    _ = 1+3*(ternaryOnes m+
          3*ternaryOnes m*(2*ternaryOnes m+1)^2+
          (3^(m+2)*d)*
            peelGain (ternaryOnes m) (3^(m+2)*d)) := by
          rw [peel1_add_delta,peel1_exact_nonarchimedean_fixedpoint]
    _ = ternaryOnes (m+1)+3^((m+1)+2)*
        (d*peelGain (ternaryOnes m) (3^(m+2)*d)+
          3^(m-1)*ternaryOnes m) := by
          rw [hs,hnext,hp1,hp2,hp3]
          ring

/-- A fully explicit *unit* residual, at every finite natural scale.
This states the sharp valuation without a p-adic completion or any axiom. -/
theorem exact_unit_residual (t : Nat) :
    ∃ d : Nat,
      affineOrbit (ternaryOnes (t+2)) =
        ternaryOnes (t+2)+3^((t+2)+2)*d ∧
      d%3=1 := by
  induction t with
  | zero =>
      refine ⟨1,?_,by decide⟩
      norm_num [ternaryOnes,affineOrbit]
  | succ t ih =>
      obtain ⟨d,hdshape,hdunit⟩ := ih
      let m : Nat := t+2
      let d' : Nat :=
        d*peelGain (ternaryOnes m) (3^(m+2)*d)+
          3^(m-1)*ternaryOnes m
      have hshape :
          affineOrbit (ternaryOnes (m+1)) =
          ternaryOnes (m+1)+3^((m+1)+2)*d' :=
        sharp_peel_step m d (by dsimp [m]) hdshape
      have hU : (3^(m-1))%3=0 := by
        have e : m-1=t+1 := by dsimp [m]; omega
        rw [e,pow_succ]
        simp
      have hunit : d'%3=1 := by
        dsimp [d']
        rw [Nat.add_mod,Nat.mul_mod]
        rw [peelGain_mod_three,hU,hdunit]
      refine ⟨d',?_,hunit⟩
      simpa [m,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hshape

/-- Arbitrary m>=2, exact physical residual has a 3-adic unit
coefficient. In particular v_3(A_(s_m)-s_m)=m+2. -/
theorem exact_unit_residual_all_m
    (m : Nat) (hm : 2<=m) :
    ∃ d : Nat,
      affineOrbit (ternaryOnes m) =
        ternaryOnes m+3^(m+2)*d ∧
      d%3=1 := by
  have h : m-2+2=m := by omega
  simpa only [h] using (exact_unit_residual (m-2))

#print axioms peel1_add_delta
#print axioms peelGain_mod_three
#print axioms sharp_peel_step
#print axioms exact_unit_residual
#print axioms exact_unit_residual_all_m

end GSTProblem406SharpPeelResidual
