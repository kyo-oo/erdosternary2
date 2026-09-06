import GSTFourPowerAffineSixthTrit701_708

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit714_717

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_300_of_exponent_714
    (N : Nat) (hN : N % 729 = 714) : affineOrbit N % 729 = 300 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 714).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_0102_714
    (N : Nat) (hAmod : affineOrbit N % 729 = 300) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  rw [badChannel_zero_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_sevenOneFour (N : Nat) (hN : N % 729 = 714) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_0102_714 N (affineOrbit_mod729_eq_300_of_exponent_714 N hN)

theorem physical_happy_of_mod729_sevenOneFour
    (N : Nat) (hN : N % 729 = 714) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenOneFour N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenOneFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 714) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenOneFour (K+1) hNext

private theorem affineOrbit_mod729_eq_472_of_exponent_715
    (N : Nat) (hN : N % 729 = 715) : affineOrbit N % 729 = 472 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 715).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_11122_715
    (N : Nat) (hAmod : affineOrbit N % 729 = 472) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_sevenOneFive (N : Nat) (hN : N % 729 = 715) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_11122_715 N (affineOrbit_mod729_eq_472_of_exponent_715 N hN)

theorem physical_happy_of_mod729_sevenOneFive
    (N : Nat) (hN : N % 729 = 715) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenOneFive N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenOneFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 715) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenOneFive (K+1) hNext

private theorem affineOrbit_mod729_eq_431_of_exponent_716
    (N : Nat) (hN : N % 729 = 716) : affineOrbit N % 729 = 431 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 716).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_22_716
    (N : Nat) (hAmod : affineOrbit N % 729 = 431) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sevenOneSix (N : Nat) (hN : N % 729 = 716) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_716 N (affineOrbit_mod729_eq_431_of_exponent_716 N hN)

theorem physical_happy_of_mod729_sevenOneSix
    (N : Nat) (hN : N % 729 = 716) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenOneSix N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenOneSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 716) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenOneSix (K+1) hNext

private theorem affineOrbit_mod729_eq_267_of_exponent_717
    (N : Nat) (hN : N % 729 = 717) : affineOrbit N % 729 = 267 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 717).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_02_717
    (N : Nat) (hAmod : affineOrbit N % 729 = 267) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sevenOneSeven (N : Nat) (hN : N % 729 = 717) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_717 N (affineOrbit_mod729_eq_267_of_exponent_717 N hN)

theorem physical_happy_of_mod729_sevenOneSeven
    (N : Nat) (hN : N % 729 = 717) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenOneSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenOneSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 717) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenOneSeven (K+1) hNext

#check commonTwo_of_mod729_sevenOneFour
#check physical_happy_of_mod729_sevenOneFour
#check four_power_happy_propagates_of_next_mod729_sevenOneFour
#check commonTwo_of_mod729_sevenOneFive
#check physical_happy_of_mod729_sevenOneFive
#check four_power_happy_propagates_of_next_mod729_sevenOneFive
#check commonTwo_of_mod729_sevenOneSix
#check physical_happy_of_mod729_sevenOneSix
#check four_power_happy_propagates_of_next_mod729_sevenOneSix
#check commonTwo_of_mod729_sevenOneSeven
#check physical_happy_of_mod729_sevenOneSeven
#check four_power_happy_propagates_of_next_mod729_sevenOneSeven
#print axioms commonTwo_of_mod729_sevenOneFour
#print axioms physical_happy_of_mod729_sevenOneFour
#print axioms four_power_happy_propagates_of_next_mod729_sevenOneFour
#print axioms commonTwo_of_mod729_sevenOneFive
#print axioms physical_happy_of_mod729_sevenOneFive
#print axioms four_power_happy_propagates_of_next_mod729_sevenOneFive
#print axioms commonTwo_of_mod729_sevenOneSix
#print axioms physical_happy_of_mod729_sevenOneSix
#print axioms four_power_happy_propagates_of_next_mod729_sevenOneSix
#print axioms commonTwo_of_mod729_sevenOneSeven
#print axioms physical_happy_of_mod729_sevenOneSeven
#print axioms four_power_happy_propagates_of_next_mod729_sevenOneSeven

end GSTFourPowerAffineSixthTrit714_717
