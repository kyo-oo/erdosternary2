import GSTFourPowerAffineSixthTrit683_690

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit692_694

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_524_of_exponent_692
    (N : Nat) (hN : N % 729 = 692) : affineOrbit N % 729 = 524 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 692).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_201102_692
    (N : Nat) (hAmod : affineOrbit N % 729 = 524) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_zero_iff, hd5] at hbad5
  simpa using hbad5

theorem commonTwo_of_mod729_sixNineTwo (N : Nat) (hN : N % 729 = 692) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_201102_692 N (affineOrbit_mod729_eq_524_of_exponent_692 N hN)

theorem physical_happy_of_mod729_sixNineTwo
    (N : Nat) (hN : N % 729 = 692) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixNineTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_sixNineTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 692) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixNineTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_639_of_exponent_693
    (N : Nat) (hN : N % 729 = 693) : affineOrbit N % 729 = 639 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 693).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_002_693
    (N : Nat) (hAmod : affineOrbit N % 729 = 639) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  rw [badChannel_zero_iff, hd2] at hbad2
  simpa using hbad2

theorem commonTwo_of_mod729_sixNineThree (N : Nat) (hN : N % 729 = 693) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_002_693 N (affineOrbit_mod729_eq_639_of_exponent_693 N hN)

theorem physical_happy_of_mod729_sixNineThree
    (N : Nat) (hN : N % 729 = 693) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixNineThree N hN)

theorem four_power_happy_propagates_of_next_mod729_sixNineThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 693) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixNineThree (K+1) hNext

private theorem affineOrbit_mod729_eq_370_of_exponent_694
    (N : Nat) (hN : N % 729 = 694) : affineOrbit N % 729 = 370 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 694).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_102_694
    (N : Nat) (hAmod : affineOrbit N % 729 = 370) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  rw [badChannel_zero_iff, hd2] at hbad2
  simpa using hbad2

theorem commonTwo_of_mod729_sixNineFour (N : Nat) (hN : N % 729 = 694) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_102_694 N (affineOrbit_mod729_eq_370_of_exponent_694 N hN)

theorem physical_happy_of_mod729_sixNineFour
    (N : Nat) (hN : N % 729 = 694) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixNineFour N hN)

theorem four_power_happy_propagates_of_next_mod729_sixNineFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 694) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixNineFour (K+1) hNext

#check commonTwo_of_mod729_sixNineTwo
#check commonTwo_of_mod729_sixNineThree
#check commonTwo_of_mod729_sixNineFour
#check physical_happy_of_mod729_sixNineTwo
#check physical_happy_of_mod729_sixNineThree
#check physical_happy_of_mod729_sixNineFour
#check four_power_happy_propagates_of_next_mod729_sixNineTwo
#check four_power_happy_propagates_of_next_mod729_sixNineThree
#check four_power_happy_propagates_of_next_mod729_sixNineFour
#print axioms commonTwo_of_mod729_sixNineTwo
#print axioms commonTwo_of_mod729_sixNineThree
#print axioms commonTwo_of_mod729_sixNineFour
#print axioms physical_happy_of_mod729_sixNineTwo
#print axioms physical_happy_of_mod729_sixNineThree
#print axioms physical_happy_of_mod729_sixNineFour
#print axioms four_power_happy_propagates_of_next_mod729_sixNineTwo
#print axioms four_power_happy_propagates_of_next_mod729_sixNineThree
#print axioms four_power_happy_propagates_of_next_mod729_sixNineFour

end GSTFourPowerAffineSixthTrit692_694
