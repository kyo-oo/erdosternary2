import GSTFourPowerAffineSixthTrit536_538

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit545_546

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_557_of_exponent_545
    (N : Nat) (hN : N % 729 = 545) :
    affineOrbit N % 729 = 557 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 545).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` (least-significant trit first) kills a hypothetical bad
channel: `1 -> 3`, then trit `2` is impossible from state `3`. -/
private theorem commonTwo_of_mod729_pattern_22
    (N : Nat) (hAmod : affineOrbit N % 729 = 557) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveFourFive
    (N : Nat) (hN : N % 729 = 545) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22 N
    (affineOrbit_mod729_eq_557_of_exponent_545 N hN)

theorem physical_happy_of_mod729_fiveFourFive
    (N : Nat) (hN : N % 729 = 545) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveFourFive N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveFourFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 545) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFourFive (K+1) hNext

private theorem affineOrbit_mod729_eq_42_of_exponent_546
    (N : Nat) (hN : N % 729 = 546) :
    affineOrbit N % 729 = 42 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 546).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` kills a hypothetical bad channel: `1 -> 0`, then trit `2`
is impossible from state `0`. -/
private theorem commonTwo_of_mod729_pattern_02
    (N : Nat) (hAmod : affineOrbit N % 729 = 42) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveFourSix
    (N : Nat) (hN : N % 729 = 546) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02 N
    (affineOrbit_mod729_eq_42_of_exponent_546 N hN)

theorem physical_happy_of_mod729_fiveFourSix
    (N : Nat) (hN : N % 729 = 546) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveFourSix N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveFourSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 546) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFourSix (K+1) hNext

#check commonTwo_of_mod729_fiveFourFive
#check physical_happy_of_mod729_fiveFourFive
#check four_power_happy_propagates_of_next_mod729_fiveFourFive
#check commonTwo_of_mod729_fiveFourSix
#check physical_happy_of_mod729_fiveFourSix
#check four_power_happy_propagates_of_next_mod729_fiveFourSix
#print axioms commonTwo_of_mod729_fiveFourFive
#print axioms physical_happy_of_mod729_fiveFourFive
#print axioms four_power_happy_propagates_of_next_mod729_fiveFourFive
#print axioms commonTwo_of_mod729_fiveFourSix
#print axioms physical_happy_of_mod729_fiveFourSix
#print axioms four_power_happy_propagates_of_next_mod729_fiveFourSix

end GSTFourPowerAffineSixthTrit545_546
