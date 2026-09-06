import GSTFourPowerAffineSixthTrit714_717

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit720_727

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_342_of_exponent_720
    (N : Nat) (hN : N % 729 = 720) : affineOrbit N % 729 = 342 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 720).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_002_720
    (N : Nat) (hAmod : affineOrbit N % 729 = 342) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sevenTwoZero (N : Nat) (hN : N % 729 = 720) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_002_720 N (affineOrbit_mod729_eq_342_of_exponent_720 N hN)

theorem physical_happy_of_mod729_sevenTwoZero
    (N : Nat) (hN : N % 729 = 720) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenTwoZero N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenTwoZero
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 720) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenTwoZero (K+1) hNext

private theorem affineOrbit_mod729_eq_640_of_exponent_721
    (N : Nat) (hN : N % 729 = 721) : affineOrbit N % 729 = 640 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 721).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_102_721
    (N : Nat) (hAmod : affineOrbit N % 729 = 640) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sevenTwoOne (N : Nat) (hN : N % 729 = 721) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_102_721 N (affineOrbit_mod729_eq_640_of_exponent_721 N hN)

theorem physical_happy_of_mod729_sevenTwoOne
    (N : Nat) (hN : N % 729 = 721) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenTwoOne N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenTwoOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 721) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenTwoOne (K+1) hNext

private theorem affineOrbit_mod729_eq_157_of_exponent_724
    (N : Nat) (hN : N % 729 = 724) : affineOrbit N % 729 = 157 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 724).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_1122_724
    (N : Nat) (hAmod : affineOrbit N % 729 = 157) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  rw [badChannel_three_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_sevenTwoFour (N : Nat) (hN : N % 729 = 724) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_1122_724 N (affineOrbit_mod729_eq_157_of_exponent_724 N hN)

theorem physical_happy_of_mod729_sevenTwoFour
    (N : Nat) (hN : N % 729 = 724) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenTwoFour N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenTwoFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 724) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenTwoFour (K+1) hNext

private theorem affineOrbit_mod729_eq_629_of_exponent_725
    (N : Nat) (hN : N % 729 = 725) : affineOrbit N % 729 = 629 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 725).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_22_725
    (N : Nat) (hAmod : affineOrbit N % 729 = 629) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sevenTwoFive (N : Nat) (hN : N % 729 = 725) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_725 N (affineOrbit_mod729_eq_629_of_exponent_725 N hN)

theorem physical_happy_of_mod729_sevenTwoFive
    (N : Nat) (hN : N % 729 = 725) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenTwoFive N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenTwoFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 725) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenTwoFive (K+1) hNext

private theorem affineOrbit_mod729_eq_330_of_exponent_726
    (N : Nat) (hN : N % 729 = 726) : affineOrbit N % 729 = 330 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 726).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_02_726
    (N : Nat) (hAmod : affineOrbit N % 729 = 330) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sevenTwoSix (N : Nat) (hN : N % 729 = 726) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_726 N (affineOrbit_mod729_eq_330_of_exponent_726 N hN)

theorem physical_happy_of_mod729_sevenTwoSix
    (N : Nat) (hN : N % 729 = 726) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenTwoSix N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenTwoSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 726) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenTwoSix (K+1) hNext

private theorem affineOrbit_mod729_eq_592_of_exponent_727
    (N : Nat) (hN : N % 729 = 727) : affineOrbit N % 729 = 592 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 727).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_122_727
    (N : Nat) (hAmod : affineOrbit N % 729 = 592) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sevenTwoSeven (N : Nat) (hN : N % 729 = 727) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_122_727 N (affineOrbit_mod729_eq_592_of_exponent_727 N hN)

theorem physical_happy_of_mod729_sevenTwoSeven
    (N : Nat) (hN : N % 729 = 727) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenTwoSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenTwoSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 727) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenTwoSeven (K+1) hNext

#check commonTwo_of_mod729_sevenTwoZero
#check physical_happy_of_mod729_sevenTwoZero
#check four_power_happy_propagates_of_next_mod729_sevenTwoZero
#check commonTwo_of_mod729_sevenTwoOne
#check physical_happy_of_mod729_sevenTwoOne
#check four_power_happy_propagates_of_next_mod729_sevenTwoOne
#check commonTwo_of_mod729_sevenTwoFour
#check physical_happy_of_mod729_sevenTwoFour
#check four_power_happy_propagates_of_next_mod729_sevenTwoFour
#check commonTwo_of_mod729_sevenTwoFive
#check physical_happy_of_mod729_sevenTwoFive
#check four_power_happy_propagates_of_next_mod729_sevenTwoFive
#check commonTwo_of_mod729_sevenTwoSix
#check physical_happy_of_mod729_sevenTwoSix
#check four_power_happy_propagates_of_next_mod729_sevenTwoSix
#check commonTwo_of_mod729_sevenTwoSeven
#check physical_happy_of_mod729_sevenTwoSeven
#check four_power_happy_propagates_of_next_mod729_sevenTwoSeven
#print axioms commonTwo_of_mod729_sevenTwoZero
#print axioms physical_happy_of_mod729_sevenTwoZero
#print axioms four_power_happy_propagates_of_next_mod729_sevenTwoZero
#print axioms commonTwo_of_mod729_sevenTwoOne
#print axioms physical_happy_of_mod729_sevenTwoOne
#print axioms four_power_happy_propagates_of_next_mod729_sevenTwoOne
#print axioms commonTwo_of_mod729_sevenTwoFour
#print axioms physical_happy_of_mod729_sevenTwoFour
#print axioms four_power_happy_propagates_of_next_mod729_sevenTwoFour
#print axioms commonTwo_of_mod729_sevenTwoFive
#print axioms physical_happy_of_mod729_sevenTwoFive
#print axioms four_power_happy_propagates_of_next_mod729_sevenTwoFive
#print axioms commonTwo_of_mod729_sevenTwoSix
#print axioms physical_happy_of_mod729_sevenTwoSix
#print axioms four_power_happy_propagates_of_next_mod729_sevenTwoSix
#print axioms commonTwo_of_mod729_sevenTwoSeven
#print axioms physical_happy_of_mod729_sevenTwoSeven
#print axioms four_power_happy_propagates_of_next_mod729_sevenTwoSeven

end GSTFourPowerAffineSixthTrit720_727
