import GSTFourPowerAffineSixthTrit545_546

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit554_555

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_512_of_exponent_554
    (N : Nat) (hN : N % 729 = 554) :
    affineOrbit N % 729 = 512 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 554).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` (least-significant trit first) kills a hypothetical bad
channel: `1 -> 3`, then trit `2` is impossible from state `3`. -/
private theorem commonTwo_of_mod729_pattern_22_554
    (N : Nat) (hAmod : affineOrbit N % 729 = 512) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  rw [badChannel_three_iff, hd1] at hbad1
  simpa using hbad1

theorem commonTwo_of_mod729_fiveFiveFour
    (N : Nat) (hN : N % 729 = 554) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_554 N
    (affineOrbit_mod729_eq_512_of_exponent_554 N hN)

theorem physical_happy_of_mod729_fiveFiveFour
    (N : Nat) (hN : N % 729 = 554) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveFiveFour N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveFiveFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 554) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFiveFour (K+1) hNext

private theorem affineOrbit_mod729_eq_591_of_exponent_555
    (N : Nat) (hN : N % 729 = 555) :
    affineOrbit N % 729 = 591 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 555).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` kills a hypothetical bad channel: `1 -> 0`, then trit `2`
is impossible from state `0`. -/
private theorem commonTwo_of_mod729_pattern_02_555
    (N : Nat) (hAmod : affineOrbit N % 729 = 591) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  rw [badChannel_zero_iff, hd1] at hbad1
  simpa using hbad1

theorem commonTwo_of_mod729_fiveFiveFive
    (N : Nat) (hN : N % 729 = 555) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_555 N
    (affineOrbit_mod729_eq_591_of_exponent_555 N hN)

theorem physical_happy_of_mod729_fiveFiveFive
    (N : Nat) (hN : N % 729 = 555) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveFiveFive N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveFiveFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 555) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFiveFive (K+1) hNext

#check commonTwo_of_mod729_fiveFiveFour
#check physical_happy_of_mod729_fiveFiveFour
#check four_power_happy_propagates_of_next_mod729_fiveFiveFour
#check commonTwo_of_mod729_fiveFiveFive
#check physical_happy_of_mod729_fiveFiveFive
#check four_power_happy_propagates_of_next_mod729_fiveFiveFive
#print axioms commonTwo_of_mod729_fiveFiveFour
#print axioms physical_happy_of_mod729_fiveFiveFour
#print axioms four_power_happy_propagates_of_next_mod729_fiveFiveFour
#print axioms commonTwo_of_mod729_fiveFiveFive
#print axioms physical_happy_of_mod729_fiveFiveFive
#print axioms four_power_happy_propagates_of_next_mod729_fiveFiveFive

end GSTFourPowerAffineSixthTrit554_555
