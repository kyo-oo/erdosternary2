import GSTFourPowerAffineSixthTrit674_681

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit683_690

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_488_of_exponent_683
    (N : Nat) (hN : N % 729 = 683) : affineOrbit N % 729 = 488 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 683).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_200002_683
    (N : Nat) (hAmod : affineOrbit N % 729 = 488) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_zero_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_zero_iff, hd5] at hbad5
  simpa using hbad5

theorem commonTwo_of_mod729_sixEightThree (N : Nat) (hN : N % 729 = 683) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_200002_683 N (affineOrbit_mod729_eq_488_of_exponent_683 N hN)

theorem physical_happy_of_mod729_sixEightThree
    (N : Nat) (hN : N % 729 = 683) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixEightThree N hN)

theorem four_power_happy_propagates_of_next_mod729_sixEightThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 683) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixEightThree (K+1) hNext

private theorem affineOrbit_mod729_eq_495_of_exponent_684
    (N : Nat) (hN : N % 729 = 684) : affineOrbit N % 729 = 495 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 684).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_001002_684
    (N : Nat) (hAmod : affineOrbit N % 729 = 495) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_zero_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_zero_iff, hd5] at hbad5
  simpa using hbad5

theorem commonTwo_of_mod729_sixEightFour (N : Nat) (hN : N % 729 = 684) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_001002_684 N (affineOrbit_mod729_eq_495_of_exponent_684 N hN)

theorem physical_happy_of_mod729_sixEightFour
    (N : Nat) (hN : N % 729 = 684) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixEightFour N hN)

theorem four_power_happy_propagates_of_next_mod729_sixEightFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 684) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixEightFour (K+1) hNext

private theorem affineOrbit_mod729_eq_523_of_exponent_685
    (N : Nat) (hN : N % 729 = 685) : affineOrbit N % 729 = 523 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 685).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_101102_685
    (N : Nat) (hAmod : affineOrbit N % 729 = 523) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_zero_iff, hd5] at hbad5
  simpa using hbad5

theorem commonTwo_of_mod729_sixEightFive (N : Nat) (hN : N % 729 = 685) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_101102_685 N (affineOrbit_mod729_eq_523_of_exponent_685 N hN)

theorem physical_happy_of_mod729_sixEightFive
    (N : Nat) (hN : N % 729 = 685) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixEightFive N hN)

theorem four_power_happy_propagates_of_next_mod729_sixEightFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 685) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixEightFive (K+1) hNext

private theorem affineOrbit_mod729_eq_688_of_exponent_688
    (N : Nat) (hN : N % 729 = 688) : affineOrbit N % 729 = 688 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 688).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_111122_688
    (N : Nat) (hAmod : affineOrbit N % 729 = 688) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_three_iff, hd5] at hbad5
  simpa using hbad5

theorem commonTwo_of_mod729_sixEightEight (N : Nat) (hN : N % 729 = 688) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_111122_688 N (affineOrbit_mod729_eq_688_of_exponent_688 N hN)

theorem physical_happy_of_mod729_sixEightEight
    (N : Nat) (hN : N % 729 = 688) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixEightEight N hN)

theorem four_power_happy_propagates_of_next_mod729_sixEightEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 688) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixEightEight (K+1) hNext

private theorem affineOrbit_mod729_eq_566_of_exponent_689
    (N : Nat) (hN : N % 729 = 689) : affineOrbit N % 729 = 566 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 689).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_22_689
    (N : Nat) (hAmod : affineOrbit N % 729 = 566) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixEightNine (N : Nat) (hN : N % 729 = 689) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_689 N (affineOrbit_mod729_eq_566_of_exponent_689 N hN)

theorem physical_happy_of_mod729_sixEightNine
    (N : Nat) (hN : N % 729 = 689) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixEightNine N hN)

theorem four_power_happy_propagates_of_next_mod729_sixEightNine
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 689) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixEightNine (K+1) hNext

private theorem affineOrbit_mod729_eq_78_of_exponent_690
    (N : Nat) (hN : N % 729 = 690) : affineOrbit N % 729 = 78 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 690).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_02_690
    (N : Nat) (hAmod : affineOrbit N % 729 = 78) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixNineZero (N : Nat) (hN : N % 729 = 690) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_690 N (affineOrbit_mod729_eq_78_of_exponent_690 N hN)

theorem physical_happy_of_mod729_sixNineZero
    (N : Nat) (hN : N % 729 = 690) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixNineZero N hN)

theorem four_power_happy_propagates_of_next_mod729_sixNineZero
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 690) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixNineZero (K+1) hNext

#check commonTwo_of_mod729_sixEightThree
#check physical_happy_of_mod729_sixEightThree
#check four_power_happy_propagates_of_next_mod729_sixEightThree
#check commonTwo_of_mod729_sixEightFour
#check physical_happy_of_mod729_sixEightFour
#check four_power_happy_propagates_of_next_mod729_sixEightFour
#check commonTwo_of_mod729_sixEightFive
#check physical_happy_of_mod729_sixEightFive
#check four_power_happy_propagates_of_next_mod729_sixEightFive
#check commonTwo_of_mod729_sixEightEight
#check physical_happy_of_mod729_sixEightEight
#check four_power_happy_propagates_of_next_mod729_sixEightEight
#check commonTwo_of_mod729_sixEightNine
#check physical_happy_of_mod729_sixEightNine
#check four_power_happy_propagates_of_next_mod729_sixEightNine
#check commonTwo_of_mod729_sixNineZero
#check physical_happy_of_mod729_sixNineZero
#check four_power_happy_propagates_of_next_mod729_sixNineZero
#print axioms physical_happy_of_mod729_sixEightThree
#print axioms physical_happy_of_mod729_sixEightFour
#print axioms physical_happy_of_mod729_sixEightFive
#print axioms physical_happy_of_mod729_sixEightEight
#print axioms physical_happy_of_mod729_sixEightNine
#print axioms physical_happy_of_mod729_sixNineZero

end GSTFourPowerAffineSixthTrit683_690
