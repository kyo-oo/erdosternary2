import GSTFourPowerMultiscaleRenormalization
import GSTFourPowerAffineRenormalizedOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

namespace GSTFourPowerThirdWaveMultiscaleBridge

open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineRenormalizedOrbit
open GSTFourPowerMultiscaleRenormalization

/-- Scale zero is exactly the historical affine orbit. -/
theorem scaleOrbit_zero_eq_affineOrbit (q : Nat) :
    scaleOrbit 0 q = affineOrbit q := by
  induction q with
  | zero =>
      simp [scaleOrbit, affineOrbit]
  | succ q ih =>
      rw [scaleOrbit_zero_succ, affineOrbit_succ, ih]

/-- Scale one is exactly the renormalized orbit used by the third-wave analysis. -/
theorem scaleOrbit_one_eq_renormOrbit (q : Nat) :
    scaleOrbit 1 q = renormOrbit q := by
  induction q with
  | zero =>
      simp [scaleOrbit, renormOrbit, GSTFourPowerAffineExponentPeel.peel0,
        affineOrbit]
  | succ q ih =>
      rw [scaleOrbit_one_succ, renormOrbit_succ, ih]

/-- The zero child of one ternary exponent digit is the exact cross-scale
conjugacy from scale zero to scale one. -/
theorem affineOrbit_three_mul_multiscale (q : Nat) :
    affineOrbit (3*q) = 3 * scaleOrbit 1 q := by
  rw [← scaleOrbit_zero_eq_affineOrbit]
  exact scaleOrbit_three_mul 0 q

/-- Exact scale-one form of the exponent child 3q+1. -/
theorem affineOrbit_three_mul_add_one_multiscale (q : Nat) :
    affineOrbit (3*q+1) = 1 + 12 * scaleOrbit 1 q := by
  rw [show 3*q+1 = (3*q)+1 by omega, affineOrbit_succ,
    affineOrbit_three_mul_multiscale]
  ring

/-- Exact scale-one form of the exponent child 3q+2. -/
theorem affineOrbit_three_mul_add_two_multiscale (q : Nat) :
    affineOrbit (3*q+2) = 5 + 48 * scaleOrbit 1 q := by
  rw [show 3*q+2 = (3*q+1)+1 by omega, affineOrbit_succ,
    affineOrbit_three_mul_add_one_multiscale]
  ring

/-- Removing the exponent trit from the 3q child lands literally on scale one. -/
theorem tail3_affineOrbit_three_mul_multiscale (q : Nat) :
    tail3 (affineOrbit (3*q)) = scaleOrbit 1 q := by
  rw [affineOrbit_three_mul_multiscale]
  simp [tail3]

/-- Removing the exponent trit from the 3q+1 child lands on the first affine
edge over scale one. -/
theorem tail3_affineOrbit_three_mul_add_one_multiscale (q : Nat) :
    tail3 (affineOrbit (3*q+1)) = 4 * scaleOrbit 1 q := by
  rw [affineOrbit_three_mul_add_one_multiscale]
  unfold tail3
  omega

/-- Removing the exponent trit from the 3q+2 child lands on the second affine
edge over scale one. -/
theorem tail3_affineOrbit_three_mul_add_two_multiscale (q : Nat) :
    tail3 (affineOrbit (3*q+2)) = 16 * scaleOrbit 1 q + 1 := by
  rw [affineOrbit_three_mul_add_two_multiscale]
  unfold tail3
  omega

/-- The branch-zero classifier expressed entirely through the multiscale orbit. -/
theorem noCommonTwo_three_mul_scale_iff (q : Nat) :
    (¬ CommonTwo (3*q)) ↔ BadChannel 0 (scaleOrbit 1 q) := by
  simpa [scaleOrbit_one_eq_renormOrbit] using
    (GSTFourPowerAffineRenormalizedOrbit.noCommonTwo_three_mul_renorm_iff q)

/-- The branch-one classifier expressed entirely through the multiscale orbit. -/
theorem noCommonTwo_three_mul_add_one_scale_iff (q : Nat) :
    (¬ CommonTwo (3*q+1)) ↔ BadChannel 1 (4 * scaleOrbit 1 q) := by
  simpa [scaleOrbit_one_eq_renormOrbit] using
    (GSTFourPowerAffineRenormalizedOrbit.noCommonTwo_three_mul_add_one_renorm_iff q)

/-- The branch-two classifier expressed entirely through the multiscale orbit. -/
theorem noCommonTwo_three_mul_add_two_scale_iff (q : Nat) :
    (¬ CommonTwo (3*q+2)) ↔ BadChannel 3 (16 * scaleOrbit 1 q + 1) := by
  simpa [scaleOrbit_one_eq_renormOrbit] using
    (GSTFourPowerAffineRenormalizedOrbit.noCommonTwo_three_mul_add_two_renorm_iff q)

/-- Exact exponent form of the remaining third-wave closure. -/
def ThirdWaveNoCommonDescent : Prop :=
  (∀ q : Nat, ¬ CommonTwo (3*q) → ¬ CommonTwo q) ∧
  (∀ q : Nat, ¬ CommonTwo (3*q+1) → ¬ CommonTwo q) ∧
  (∀ q : Nat, ¬ CommonTwo (3*q+2) → ¬ CommonTwo q)

/-- Same closure expressed on the canonical scale-zero/scale-one coordinates. -/
def MultiscaleBranchBadDescent : Prop :=
  (∀ q : Nat,
    BadChannel 0 (scaleOrbit 1 q) →
      BadChannel 1 (scaleOrbit 0 q)) ∧
  (∀ q : Nat,
    BadChannel 1 (4 * scaleOrbit 1 q) →
      BadChannel 1 (scaleOrbit 0 q)) ∧
  (∀ q : Nat,
    BadChannel 3 (16 * scaleOrbit 1 q + 1) →
      BadChannel 1 (scaleOrbit 0 q))

/-- The direct exponent closure and the multiscale bad-channel closure are
literally the same theorem after the exact scale conjugacies. -/
theorem thirdWaveNoCommonDescent_iff_multiscale :
    ThirdWaveNoCommonDescent ↔ MultiscaleBranchBadDescent := by
  constructor
  · intro h
    unfold ThirdWaveNoCommonDescent at h
    unfold MultiscaleBranchBadDescent
    constructor
    · intro q hBad
      have hNoChild : ¬ CommonTwo (3*q) :=
        (noCommonTwo_three_mul_scale_iff q).2 hBad
      have hNoParent := h.1 q hNoChild
      have hp : BadChannel 1 (affineOrbit q) :=
        (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).1 hNoParent
      simpa [scaleOrbit_zero_eq_affineOrbit] using hp
    · constructor
      · intro q hBad
        have hNoChild : ¬ CommonTwo (3*q+1) :=
          (noCommonTwo_three_mul_add_one_scale_iff q).2 hBad
        have hNoParent := h.2.1 q hNoChild
        have hp : BadChannel 1 (affineOrbit q) :=
          (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).1 hNoParent
        simpa [scaleOrbit_zero_eq_affineOrbit] using hp
      · intro q hBad
        have hNoChild : ¬ CommonTwo (3*q+2) :=
          (noCommonTwo_three_mul_add_two_scale_iff q).2 hBad
        have hNoParent := h.2.2 q hNoChild
        have hp : BadChannel 1 (affineOrbit q) :=
          (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).1 hNoParent
        simpa [scaleOrbit_zero_eq_affineOrbit] using hp
  · intro h
    unfold MultiscaleBranchBadDescent at h
    unfold ThirdWaveNoCommonDescent
    constructor
    · intro q hNoChild
      have hb : BadChannel 0 (scaleOrbit 1 q) :=
        (noCommonTwo_three_mul_scale_iff q).1 hNoChild
      have hp := h.1 q hb
      have hp' : BadChannel 1 (affineOrbit q) := by
        simpa [scaleOrbit_zero_eq_affineOrbit] using hp
      exact (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).2 hp'
    · constructor
      · intro q hNoChild
        have hb : BadChannel 1 (4 * scaleOrbit 1 q) :=
          (noCommonTwo_three_mul_add_one_scale_iff q).1 hNoChild
        have hp := h.2.1 q hb
        have hp' : BadChannel 1 (affineOrbit q) := by
          simpa [scaleOrbit_zero_eq_affineOrbit] using hp
        exact (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).2 hp'
      · intro q hNoChild
        have hb : BadChannel 3 (16 * scaleOrbit 1 q + 1) :=
          (noCommonTwo_three_mul_add_two_scale_iff q).1 hNoChild
        have hp := h.2.2 q hb
        have hp' : BadChannel 1 (affineOrbit q) := by
          simpa [scaleOrbit_zero_eq_affineOrbit] using hp
        exact (GSTFourPowerAffineClassifierBridge.noCommonTwo_iff_badChannel_one q).2 hp'


/-- Cubing upgrades one ternary digit of relative precision.  If two powers
agree modulo 3^(p+1) up to the coefficient e*3^p, then after tripling both
exponents (and adding the same a) that coefficient survives unchanged one
level higher. -/
theorem cubic_reference_transport
    (n h p e a : Nat) (hp : 1 ≤ p)
    (H :
      4^n % 3^(p+1) =
        (4^h + e * 3^p) % 3^(p+1)) :
    4^(3*n+a) % 3^(p+2) =
      (4^(3*h+a) + e * 3^(p+1)) % 3^(p+2) := by
  cases p with
  | zero => omega
  | succ k =>
      let T : Nat := 3^k
      have hP : 3^(Nat.succ k) = 3 * T := by
        dsimp [T]
        rw [Nat.pow_succ]
        ring
      have hP1 : 3^(Nat.succ k + 1) = 9 * T := by
        calc
          3^(Nat.succ k + 1) = 3^(Nat.succ (Nat.succ k)) := by congr 1 <;> omega
          _ = 3^(Nat.succ k) * 3 := by rw [Nat.pow_succ]
          _ = (3 * T) * 3 := by rw [hP]
          _ = 9 * T := by ring
      have hP2 : 3^(Nat.succ k + 2) = 27 * T := by
        calc
          3^(Nat.succ k + 2) = 3^(Nat.succ (Nat.succ (Nat.succ k))) := by
            congr 1 <;> omega
          _ = 3^(Nat.succ (Nat.succ k)) * 3 := by rw [Nat.pow_succ]
          _ = (9 * T) * 3 := by
            rw [show 3^(Nat.succ (Nat.succ k)) = 9 * T by
              calc
                3^(Nat.succ (Nat.succ k)) = 3^(Nat.succ k + 1) := by
                  congr 1 <;> omega
                _ = 9 * T := hP1]
          _ = 27 * T := by ring
      rw [hP1] at H
      rw [hP, hP2]
      let A : Nat := 4^n
      let H0 : Nat := 4^h
      let B : Nat := H0 + e * (3 * T)
      let L : Nat := 9 * T
      let N : Nat := 27 * T
      let r : Nat := A % L
      let qa : Nat := A / L
      let qb : Nat := B / L
      have hremB : B % L = r := by
        simpa [A, H0, B, L, r] using H.symm
      have hA : A = r + L * qa := by
        simpa [r, qa] using (Nat.mod_add_div A L).symm
      have hB : B = r + L * qb := by
        calc
          B = B % L + L * (B / L) := (Nat.mod_add_div B L).symm
          _ = r + L * qb := by rw [hremB]; rfl
      have hcube (q : Nat) :
          (r + L*q)^3 =
            r^3 + N * (r^2*q + 9*r*T*q^2 + 27*T^2*q^3) := by
        dsimp [L, N]
        ring
      have hAcube : A^3 % N = r^3 % N := by
        rw [hA, hcube, Nat.add_mul_mod_self_left]
      have hBcube : B^3 % N = r^3 % N := by
        rw [hB, hcube, Nat.add_mul_mod_self_left]
      have hH0mod : H0 % 3 = 1 := by
        simpa [H0] using pow4_mod3_one h
      let u : Nat := H0 / 3
      have hH0 : H0 = 1 + 3*u := by
        calc
          H0 = H0 % 3 + 3 * (H0 / 3) := (Nat.mod_add_div H0 3).symm
          _ = 1 + 3*u := by rw [hH0mod]; rfl
      have hBspecial :
          ∃ Q : Nat, B^3 =
            (H0^3 + 9*T*e) + N*Q := by
        refine ⟨2*e*u + 3*e*u^2 + e^2*T*H0 + e^3*T^2, ?_⟩
        change (H0 + e*(3*T))^3 =
          (H0^3 + 9*T*e) +
            27*T*(2*e*u + 3*e*u^2 + e^2*T*H0 + e^3*T^2)
        rw [hH0]
        ring
      have hBtarget :
          B^3 % N = (H0^3 + 9*T*e) % N := by
        obtain ⟨Q, hQ⟩ := hBspecial
        rw [hQ, Nat.add_mul_mod_self_left]
      have hcubeTarget :
          A^3 % N = (H0^3 + 9*T*e) % N := by
        exact hAcube.trans (hBcube.symm.trans hBtarget)
      let C : Nat := 4^a
      have hmul :
          (A^3 * C) % N =
            ((H0^3 + 9*T*e) * C) % N := by
        calc
          (A^3 * C) % N = ((A^3 % N) * (C % N)) % N := by
            rw [Nat.mul_mod]
          _ = (((H0^3 + 9*T*e) % N) * (C % N)) % N := by
            rw [hcubeTarget]
          _ = ((H0^3 + 9*T*e) * C) % N := by
            rw [Nat.mul_mod]
      have hCmod : C % 3 = 1 := by
        simpa [C] using pow4_mod3_one a
      let v : Nat := C / 3
      have hC : C = 1 + 3*v := by
        calc
          C = C % 3 + 3 * (C / 3) := (Nat.mod_add_div C 3).symm
          _ = 1 + 3*v := by rw [hCmod]; rfl
      have hprod :
          (H0^3 + 9*T*e) * C =
            (H0^3*C + 9*T*e) + N*(e*v) := by
        dsimp [N]
        rw [hC]
        ring
      have hmul' :
          (A^3 * C) % N =
            (H0^3*C + 9*T*e) % N := by
        rw [hmul, hprod, Nat.add_mul_mod_self_left]
      have hpowA : A^3 * C = 4^(3*n+a) := by
        dsimp [A, C]
        rw [show 3*n+a = n*3+a by omega, Nat.pow_add, Nat.pow_mul]
      have hpowH : H0^3 * C = 4^(3*h+a) := by
        dsimp [H0, C]
        rw [show 3*h+a = h*3+a by omega, Nat.pow_add, Nat.pow_mul]
      rw [← hpowA, ← hpowH]
      simpa [N] using hmul'



/-- Cubic-cone closure.  A scale-s exponent with current trit two is an
immediate common-two exponent whenever both reference powers stay below row
s+1.  This kills an expanding cone of the ternary exponent tree at every
positive scale. -/
theorem cubic_cone_commonTwo
    (s b r : Nat) (hs : 1 ≤ s) (hb : b % 3 = 2)
    (hsmall : 4^(r+1) < 3^(s+1)) :
    CommonTwo (3^s * b + r) := by
  have hbdec : b = 3 * (b / 3) + 2 := by
    have h := Nat.div_add_mod b 3
    rw [hb] at h
    omega
  have hK :
      3^s * b + r =
        r + 2 * 3^s + 3^(s+1) * (b / 3) := by
    rw [hbdec, Nat.pow_succ]
    ring
  have hrle : 4^r ≤ 4^(r+1) := by
    rw [Nat.pow_succ]
    omega
  have hsmall0 : 4^r < 3^(s+1) := lt_of_le_of_lt hrle hsmall
  have hd0 : digit3 (4^r) (s+1) = 0 := by
    unfold digit3
    rw [Nat.div_eq_of_lt hsmall0]
    simp
  have hd1 : digit3 (4^(r+1)) (s+1) = 0 := by
    unfold digit3
    rw [Nat.div_eq_of_lt hsmall]
    simp
  have hp :=
    GSTFourPowerExponentTritObstruction.pow4_shared_trit_pair
      s r 2 (b / 3) (by norm_num : (2:Nat) < 3)
  refine ⟨s+1, by omega, ?_, ?_⟩
  · rw [hK, hp.1, hd0]
  · rw [hK, hp.2, hd1]


#print axioms scaleOrbit_zero_eq_affineOrbit
#print axioms scaleOrbit_one_eq_renormOrbit
#print axioms affineOrbit_three_mul_multiscale
#print axioms tail3_affineOrbit_three_mul_add_two_multiscale
#print axioms thirdWaveNoCommonDescent_iff_multiscale

end GSTFourPowerThirdWaveMultiscaleBridge
