import GSTFourPowerAffineSixthTrit660_663

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit665_668

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_416_of_exponent_665
    (N : Nat) (hN : N % 729 = 665) : affineOrbit N % 729 = 416 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 665).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_20102_665
    (N : Nat) (hAmod : affineOrbit N % 729 = 416) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_sixSixFive (N : Nat) (hN : N % 729 = 665) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_20102_665 N (affineOrbit_mod729_eq_416_of_exponent_665 N hN)

theorem physical_happy_of_mod729_sixSixFive
    (N : Nat) (hN : N % 729 = 665) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixSixFive N hN)

theorem four_power_happy_propagates_of_next_mod729_sixSixFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 665) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixSixFive (K+1) hNext

private theorem affineOrbit_mod729_eq_207_of_exponent_666
    (N : Nat) (hN : N % 729 = 666) : affineOrbit N % 729 = 207 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 666).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_002_666
    (N : Nat) (hAmod : affineOrbit N % 729 = 207) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixSixSix (N : Nat) (hN : N % 729 = 666) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_002_666 N (affineOrbit_mod729_eq_207_of_exponent_666 N hN)

theorem physical_happy_of_mod729_sixSixSix
    (N : Nat) (hN : N % 729 = 666) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixSixSix N hN)

theorem four_power_happy_propagates_of_next_mod729_sixSixSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 666) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixSixSix (K+1) hNext

private theorem affineOrbit_mod729_eq_100_of_exponent_667
    (N : Nat) (hN : N % 729 = 667) : affineOrbit N % 729 = 100 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 667).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_102_667
    (N : Nat) (hAmod : affineOrbit N % 729 = 100) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixSixSeven (N : Nat) (hN : N % 729 = 667) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_102_667 N (affineOrbit_mod729_eq_100_of_exponent_667 N hN)

theorem physical_happy_of_mod729_sixSixSeven
    (N : Nat) (hN : N % 729 = 667) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixSixSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_sixSixSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 667) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixSixSeven (K+1) hNext

private theorem affineOrbit_mod729_eq_401_of_exponent_668
    (N : Nat) (hN : N % 729 = 668) : affineOrbit N % 729 = 401 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 668).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_2122_668
    (N : Nat) (hAmod : affineOrbit N % 729 = 401) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 2 (tail3 (tail3 A)) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_two_iff, hd2] at hbad2
    simpa using hbad2
  rw [badChannel_three_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_sixSixEight (N : Nat) (hN : N % 729 = 668) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_2122_668 N (affineOrbit_mod729_eq_401_of_exponent_668 N hN)

theorem physical_happy_of_mod729_sixSixEight
    (N : Nat) (hN : N % 729 = 668) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixSixEight N hN)

theorem four_power_happy_propagates_of_next_mod729_sixSixEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 668) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixSixEight (K+1) hNext

#check commonTwo_of_mod729_sixSixFive
#check physical_happy_of_mod729_sixSixFive
#check four_power_happy_propagates_of_next_mod729_sixSixFive
#check commonTwo_of_mod729_sixSixSix
#check physical_happy_of_mod729_sixSixSix
#check four_power_happy_propagates_of_next_mod729_sixSixSix
#check commonTwo_of_mod729_sixSixSeven
#check physical_happy_of_mod729_sixSixSeven
#check four_power_happy_propagates_of_next_mod729_sixSixSeven
#check commonTwo_of_mod729_sixSixEight
#check physical_happy_of_mod729_sixSixEight
#check four_power_happy_propagates_of_next_mod729_sixSixEight
#print axioms physical_happy_of_mod729_sixSixFive
#print axioms physical_happy_of_mod729_sixSixSix
#print axioms physical_happy_of_mod729_sixSixSeven
#print axioms physical_happy_of_mod729_sixSixEight

end GSTFourPowerAffineSixthTrit665_668
