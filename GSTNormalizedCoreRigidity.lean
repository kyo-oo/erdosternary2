import GSTWorldtraceTowerWindow
import GSTWorldtraceCoeffStability

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST normalized-core and exact uniform coefficient transport

Two unconditional mathematical consequences of the already kernel-verified
GST / Worldtrace tower-read and coefficient recurrence.
All quantified exponents remain arbitrary natural numbers. The finite
core certificate is an external, separately checked arithmetic assertion.
No unconditional Erdős conclusion is claimed here.
-/

namespace GSTNormalizedCoreRigidity

open GSTCanonicalTailLTE
open GSTFourPowerDirectResidue
open GSTWorldtraceTowerWindow
open GSTWorldtraceCoeffStability

/-- Every finite coefficient band stabilizes after its initial scale.
This generalizes the previous eighteen-trit fixed-band lemma to ANY band. -/
theorem coefficient_stabilization_any_band
    (b s : Nat) (hbs : b ≤ s) :
    lteCoeff s % 3^(b+1) = lteCoeff b % 3^(b+1) := by
  have hstep (t : Nat) (hbt : b ≤ t) :
      lteCoeff (t+1) % 3^(b+1) = lteCoeff t % 3^(b+1) := by
    have hdiv : 3^(b+1) ∣ 3^(t+1) :=
      Nat.pow_dvd_pow 3 (by omega)
    calc
      lteCoeff (t+1) % 3^(b+1) =
          (lteCoeff (t+1) % 3^(t+1)) % 3^(b+1) :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (lteCoeff t % 3^(t+1)) % 3^(b+1) := by
        rw [coeff_step_mod]
      _ = lteCoeff t % 3^(b+1) := Nat.mod_mod_of_dvd _ hdiv
  have hbase : ∀ v : Nat,
      lteCoeff (b+v) % 3^(b+1) =
        lteCoeff b % 3^(b+1) := by
    intro v
    induction v with
    | zero => rfl
    | succ v ih =>
        rw [show b+(v+1) = (b+v)+1 by omega]
        exact (hstep (b+v) (by omega)).trans ih
  rw [show s=b+(s-b) by omega]
  exact hbase (s-b)

/-- Uniform GST transfer: an exact 30-trit certificate for u*c29
produces an actual ternary-two digit in 4^(u*3^s) at all s >= 29. -/
theorem fixed_coefficient_digit_transports_unconditionally
    (u s k : Nat) (hs : 29 ≤ s) (hk : k < 30)
    (hcert : digit3 (u * lteCoeff 29) k = 2) :
    digit3 (4^(u*3^s)) (s+1+k) = 2 := by
  have hcoeff :
      lteCoeff s % 3^30 = lteCoeff 29 % 3^30 :=
    coefficient_stabilization_any_band 29 s hs
  have hmul :
      (u*lteCoeff s) % 3^30 =
      (u*lteCoeff 29) % 3^30 := by
    calc
      (u*lteCoeff s) % 3^30 =
          ((u%3^30)*(lteCoeff s%3^30))%3^30 :=
            Nat.mul_mod _ _ _
      _ = ((u%3^30)*(lteCoeff 29%3^30))%3^30 := by rw [hcoeff]
      _ = (u*lteCoeff 29)%3^30 := (Nat.mul_mod _ _ _).symm
  have hdiv : 3^(k+1) ∣ 3^30 := Nat.pow_dvd_pow 3 (by omega)
  have hmod :
      (u*lteCoeff s) % 3^(k+1) =
      (u*lteCoeff 29) % 3^(k+1) := by
    calc
      (u*lteCoeff s) % 3^(k+1) =
          ((u*lteCoeff s)%3^30)%3^(k+1) :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((u*lteCoeff 29)%3^30)%3^(k+1) := by rw [hmul]
      _ = (u*lteCoeff 29)%3^(k+1) :=
            Nat.mod_mod_of_dvd _ hdiv
  have hread :
      digit3 (u*lteCoeff s) k = digit3 (u*lteCoeff 29) k :=
    digit3_eq_of_mod_next _ _ _ hmod
  calc
    digit3 (4^(u*3^s)) (s+1+k) =
        digit3 (u*lteCoeff s) k :=
          tower_digit_read_from_block s u k (by omega)
    _ = digit3 (u*lteCoeff 29) k := hread
    _ = 2 := hcert

/-- A valuation factor in the multiplier is exactly a shift in GST scale.
The lemma prevents treating 3-divisible multipliers as new 3-free cores. -/
theorem valuation_factor_absorbs_into_scale
    (u v s : Nat) :
    4^((u*3^v)*3^s) = 4^(u*3^(s+v)) := by
  congr 1
  rw [pow_add]
  ring

/-- Every normalized core satisfying a finite window certificate fires at
all sufficiently large scales, even when its multiplier contains 3^v. -/
theorem normalized_core_certificate_transport
    (u v s k : Nat)
    (hs : 29 ≤ s+v) (hk : k < 30)
    (hcert : digit3 (u*lteCoeff 29) k = 2) :
    digit3 (4^((u*3^v)*3^s)) ((s+v)+1+k) = 2 := by
  rw [valuation_factor_absorbs_into_scale]
  exact fixed_coefficient_digit_transports_unconditionally
    u (s+v) k hs hk hcert

#print axioms coefficient_stabilization_any_band
#print axioms fixed_coefficient_digit_transports_unconditionally
#print axioms valuation_factor_absorbs_into_scale
#print axioms normalized_core_certificate_transport

end GSTNormalizedCoreRigidity
