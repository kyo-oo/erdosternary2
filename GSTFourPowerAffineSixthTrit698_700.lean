import GSTFourPowerAffineSixthTrit692_694

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit698_700

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_35_of_exponent_698
    (N : Nat) (hN : N % 729 = 698) : affineOrbit N % 729 = 35 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 698).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_22_698
    (N : Nat) (hAmod : affineOrbit N % 729 = 35) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixNineEight (N : Nat) (hN : N % 729 = 698) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_698 N (affineOrbit_mod729_eq_35_of_exponent_698 N hN)

theorem physical_happy_of_mod729_sixNineEight
    (N : Nat) (hN : N % 729 = 698) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixNineEight N hN)

theorem four_power_happy_propagates_of_next_mod729_sixNineEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 698) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixNineEight (K+1) hNext

private theorem affineOrbit_mod729_eq_141_of_exponent_699
    (N : Nat) (hN : N % 729 = 699) : affineOrbit N % 729 = 141 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 699).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_02_699
    (N : Nat) (hAmod : affineOrbit N % 729 = 141) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixNineNine (N : Nat) (hN : N % 729 = 699) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_699 N (affineOrbit_mod729_eq_141_of_exponent_699 N hN)

theorem physical_happy_of_mod729_sixNineNine
    (N : Nat) (hN : N % 729 = 699) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixNineNine N hN)

theorem four_power_happy_propagates_of_next_mod729_sixNineNine
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 699) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixNineNine (K+1) hNext

private theorem affineOrbit_mod729_eq_565_of_exponent_700
    (N : Nat) (hN : N % 729 = 700) : affineOrbit N % 729 = 565 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 700).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_122_700
    (N : Nat) (hAmod : affineOrbit N % 729 = 565) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  rw [badChannel_three_iff, hd2] at hbad2
  simpa using hbad2

theorem commonTwo_of_mod729_sevenZeroZero (N : Nat) (hN : N % 729 = 700) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_122_700 N (affineOrbit_mod729_eq_565_of_exponent_700 N hN)

theorem physical_happy_of_mod729_sevenZeroZero
    (N : Nat) (hN : N % 729 = 700) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenZeroZero N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenZeroZero
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 700) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenZeroZero (K+1) hNext

#check commonTwo_of_mod729_sixNineEight
#check commonTwo_of_mod729_sixNineNine
#check commonTwo_of_mod729_sevenZeroZero
#check physical_happy_of_mod729_sixNineEight
#check physical_happy_of_mod729_sixNineNine
#check physical_happy_of_mod729_sevenZeroZero
#check four_power_happy_propagates_of_next_mod729_sixNineEight
#check four_power_happy_propagates_of_next_mod729_sixNineNine
#check four_power_happy_propagates_of_next_mod729_sevenZeroZero
#print axioms commonTwo_of_mod729_sixNineEight
#print axioms commonTwo_of_mod729_sixNineNine
#print axioms commonTwo_of_mod729_sevenZeroZero
#print axioms physical_happy_of_mod729_sixNineEight
#print axioms physical_happy_of_mod729_sixNineNine
#print axioms physical_happy_of_mod729_sevenZeroZero
#print axioms four_power_happy_propagates_of_next_mod729_sixNineEight
#print axioms four_power_happy_propagates_of_next_mod729_sixNineNine
#print axioms four_power_happy_propagates_of_next_mod729_sevenZeroZero

end GSTFourPowerAffineSixthTrit698_700
