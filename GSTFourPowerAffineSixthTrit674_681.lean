import GSTFourPowerAffineSixthTrit671_673

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit674_681

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_695_of_exponent_674
    (N : Nat) (hN : N % 729 = 674) : affineOrbit N % 729 = 695 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 674).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_202122_674
    (N : Nat) (hAmod : affineOrbit N % 729 = 695) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad3 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_three_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_two_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_three_iff, hd5] at hbad5
  simpa using hbad5

theorem commonTwo_of_mod729_sixSevenFour (N : Nat) (hN : N % 729 = 674) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_202122_674 N (affineOrbit_mod729_eq_695_of_exponent_674 N hN)

theorem physical_happy_of_mod729_sixSevenFour
    (N : Nat) (hN : N % 729 = 674) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixSevenFour N hN)

theorem four_power_happy_propagates_of_next_mod729_sixSevenFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 674) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixSevenFour (K+1) hNext

private theorem affineOrbit_mod729_eq_517_of_exponent_679
    (N : Nat) (hN : N % 729 = 679) : affineOrbit N % 729 = 517 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 679).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_110102_679
    (N : Nat) (hAmod : affineOrbit N % 729 = 517) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_zero_iff, hd5] at hbad5
  simpa using hbad5

theorem commonTwo_of_mod729_sixSevenNine (N : Nat) (hN : N % 729 = 679) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_110102_679 N (affineOrbit_mod729_eq_517_of_exponent_679 N hN)

theorem physical_happy_of_mod729_sixSevenNine
    (N : Nat) (hN : N % 729 = 679) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixSevenNine N hN)

theorem four_power_happy_propagates_of_next_mod729_sixSevenNine
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 679) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixSevenNine (K+1) hNext

private theorem affineOrbit_mod729_eq_611_of_exponent_680
    (N : Nat) (hN : N % 729 = 680) : affineOrbit N % 729 = 611 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 680).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_22_680
    (N : Nat) (hAmod : affineOrbit N % 729 = 611) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixEightZero (N : Nat) (hN : N % 729 = 680) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_680 N (affineOrbit_mod729_eq_611_of_exponent_680 N hN)

theorem physical_happy_of_mod729_sixEightZero
    (N : Nat) (hN : N % 729 = 680) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixEightZero N hN)

theorem four_power_happy_propagates_of_next_mod729_sixEightZero
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 680) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixEightZero (K+1) hNext

private theorem affineOrbit_mod729_eq_258_of_exponent_681
    (N : Nat) (hN : N % 729 = 681) : affineOrbit N % 729 = 258 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 681).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_02_681
    (N : Nat) (hAmod : affineOrbit N % 729 = 258) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixEightOne (N : Nat) (hN : N % 729 = 681) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_681 N (affineOrbit_mod729_eq_258_of_exponent_681 N hN)

theorem physical_happy_of_mod729_sixEightOne
    (N : Nat) (hN : N % 729 = 681) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixEightOne N hN)

theorem four_power_happy_propagates_of_next_mod729_sixEightOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 681) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixEightOne (K+1) hNext

#check commonTwo_of_mod729_sixSevenFour
#check physical_happy_of_mod729_sixSevenFour
#check four_power_happy_propagates_of_next_mod729_sixSevenFour
#check commonTwo_of_mod729_sixSevenNine
#check physical_happy_of_mod729_sixSevenNine
#check four_power_happy_propagates_of_next_mod729_sixSevenNine
#check commonTwo_of_mod729_sixEightZero
#check physical_happy_of_mod729_sixEightZero
#check four_power_happy_propagates_of_next_mod729_sixEightZero
#check commonTwo_of_mod729_sixEightOne
#check physical_happy_of_mod729_sixEightOne
#check four_power_happy_propagates_of_next_mod729_sixEightOne
#print axioms physical_happy_of_mod729_sixSevenFour
#print axioms physical_happy_of_mod729_sixSevenNine
#print axioms physical_happy_of_mod729_sixEightZero
#print axioms physical_happy_of_mod729_sixEightOne

end GSTFourPowerAffineSixthTrit674_681
