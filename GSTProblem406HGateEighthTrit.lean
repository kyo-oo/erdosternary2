import GSTProblem406ExceptionalSevenTower
import GSTProblem406HGateCoreClass
import GSTFourPowerThirdWave

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Eighth-trit exact physical HGate extension (genuine four-power sources)

This module directly supplies the original thirdWave/CommonTwo body on
previously uncovered multiplier residues; no theorem about a shifted
generic source is substituted for the literal pair of powers of four.

The result does not assert universal thirdWave. Its value is in
expanding the verified original HGate input domain, and in preserving
a strictly origin-exact proof architecture.
-/

namespace GSTProblem406HGateEighthTrit

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTProblem406HGateCoreClass

/-- The Worldtrace LTE coefficient is frozen modulo the eight-trit
window for every physical scale L ≥ 9. Reuses the checked stronger
ten-trit coefficient theorem. -/
theorem coeff_mod6561_2851 (L : Nat) (hL : 9 ≤ L) :
    GSTCanonicalTailLTE.lteCoeff L % 6561 = 2851 := by
  have hlarge :=
    GSTProblem406ExceptionalSevenTower.coeff_mod59049 L hL
  have hdiv : 6561 ∣ 59049 := by decide
  calc
    GSTCanonicalTailLTE.lteCoeff L % 6561 =
      (GSTCanonicalTailLTE.lteCoeff L % 59049) % 6561 :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
    _ = 42217 % 6561 := by rw [hlarge]
    _ = 2851 := by decide

/-- Exactly reduce each actual source-neighbor postcut quotient
to the frozen eight-trit Worldtrace coefficient. -/
private theorem coefficient_product_mod6561
    (L u M m : Nat) (hL : 9 ≤ L)
    (hm : (2851*M)%6561=m) :
    (u*GSTCanonicalTailLTE.lteCoeff L*M)%6561=(m*u)%6561 := by
  have hc : (GSTCanonicalTailLTE.lteCoeff L*M)%6561=m := by
    calc
      (GSTCanonicalTailLTE.lteCoeff L*M)%6561 =
        ((GSTCanonicalTailLTE.lteCoeff L%6561)*(M%6561))%6561 :=
          Nat.mul_mod _ _ _
      _ = (2851*M)%6561 := by
          rw [coeff_mod6561_2851 L hL]
          simpa using (Nat.mul_mod 2851 M 6561).symm
      _ = m := hm
  calc
    (u*GSTCanonicalTailLTE.lteCoeff L*M)%6561 =
        (u*(GSTCanonicalTailLTE.lteCoeff L*M))%6561 := by ring
    _ = (u*m)%6561 := by
      calc
        (u*(GSTCanonicalTailLTE.lteCoeff L*M))%6561 =
          ((u%6561)*((GSTCanonicalTailLTE.lteCoeff L*M)%6561))%6561 :=
            Nat.mul_mod _ _ _
        _ = ((u%6561)*m)%6561 := by rw [hc]
        _ = (u*m)%6561 := by
              simpa using (Nat.mul_mod u m 6561).symm
    _ = (m*u)%6561 := by ac_rfl

/-- A source-neighbor physical pair certificate in the eighth
postcut trit, on the multiplier residue modulo 3^8. -/
def EighthPhysicalClass (r : Nat) : Prop :=
  digit3 (1585*r) 7=2 ∧ digit3 (6340*r) 7=2

/-- Every multiplier in this genuine physical eighth-trit class
produces a same-position digit two in 4^K and 4^(K+1).
The witness is p=L+8, not a shifted-exponent surrogate. -/
theorem commonTwo_eighth_physical_class
    (L u : Nat) (hL : 9 ≤ L)
    (hu : EighthPhysicalClass (u%6561)) :
    CommonTwo (4+u*3^L) := by
  have hpair := hu
  have hsource_mod : digit3 (1585*u) 7 =
      digit3 (1585*(u%6561)) 7 := by
    apply digit3_eq_of_mod_next
    change (1585*u)%6561=(1585*(u%6561))%6561
    simp [Nat.mul_mod]
  have hneighbor_mod : digit3 (6340*u) 7 =
      digit3 (6340*(u%6561)) 7 := by
    apply digit3_eq_of_mod_next
    change (6340*u)%6561=(6340*(u%6561))%6561
    simp [Nat.mul_mod]
  have hsource : digit3 (1585*u) 7=2 := by
    rw [hsource_mod]
    exact hpair.1
  have hneighbor : digit3 (6340*u) 7=2 := by
    rw [hneighbor_mod]
    exact hpair.2
  have hreadsource :
      digit3 (u*GSTCanonicalTailLTE.lteCoeff L*256) 7 =
        digit3 (1585*u) 7 := by
    apply digit3_eq_of_mod_next
    simpa only [show (3:Nat)^(7+1)=6561 by decide] using
      (coefficient_product_mod6561 L u 256 1585 hL (by norm_num))
  have hreadneighbor :
      digit3 (u*GSTCanonicalTailLTE.lteCoeff L*1024) 7 =
        digit3 (6340*u) 7 := by
    apply digit3_eq_of_mod_next
    simpa only [show (3:Nat)^(7+1)=6561 by decide] using
      (coefficient_product_mod6561 L u 1024 6340 hL (by norm_num))
  apply two_wave_any_width_certificate_to_CommonTwo L u 8 7
    (by omega) (by decide) (by omega) (by decide)
  · rw [hreadsource]
    exact hsource
  · rw [hreadneighbor]
    exact hneighbor

/-- A concrete new class, not requiring any hypothesis about
the universal HGate. -/
theorem seed37_eighth_class : EighthPhysicalClass 37 := by
  norm_num [EighthPhysicalClass, digit3]

/-- This residue has no earlier hit in the first seven postcut rows
of the exact frozen coefficient pair. -/
theorem seed37_no_earlier_postcut_hit :
    ∀ j : Fin 7,
      ¬ (digit3 (37*2851*256) j.val=2 ∧
         digit3 (37*2851*1024) j.val=2) := by
  decide

theorem original_thirdWave_eighth_physical_class
    (L u : Nat) (hL : 9 ≤ L)
    (hu : EighthPhysicalClass (u%6561)) :
    GSTFourPowerThirdWave.thirdWave (4+u*3^L) := by
  exact (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
    (commonTwo_eighth_physical_class L u hL hu)

theorem original_thirdWave_seed37
    (L u : Nat) (hL : 9 ≤ L)
    (hu : u % 6561 = 37) :
    GSTFourPowerThirdWave.thirdWave (4+u*3^L) := by
  apply original_thirdWave_eighth_physical_class L u hL
  simpa only [hu] using seed37_eighth_class

#print axioms coeff_mod6561_2851
#print axioms seed37_eighth_class
#print axioms seed37_no_earlier_postcut_hit
#print axioms commonTwo_eighth_physical_class
#print axioms original_thirdWave_eighth_physical_class
#print axioms original_thirdWave_seed37

end GSTProblem406HGateEighthTrit
