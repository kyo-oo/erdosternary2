import GSTFourPowerAffineEighthTritContinuation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineNinthTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod19683_eq_13312_of_exponent_14527
    (N : Nat) (hN : N % 19683 = 14527) : affineOrbit N % 19683 = 13312 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 9 N 14527).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod19683_pattern_100120002_14527
    (N : Nat) (hAmod : affineOrbit N % 19683 = 13312) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_three_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) := by
    rw [badChannel_one_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) := by
    rw [badChannel_zero_iff, hd7] at hbad7
    simpa using hbad7
  rw [badChannel_zero_iff, hd8] at hbad8
  simpa using hbad8

theorem commonTwo_of_mod19683_14527
    (N : Nat) (hN : N % 19683 = 14527) : CommonTwo N := by
  exact commonTwo_of_mod19683_pattern_100120002_14527 N
    (affineOrbit_mod19683_eq_13312_of_exponent_14527 N hN)

theorem physical_happy_of_mod19683_14527
    (N : Nat) (hN : N % 19683 = 14527) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod19683_14527 N hN)

theorem four_power_happy_propagates_of_next_mod19683_14527
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 19683 = 14527) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod19683_14527 (K+1) hNext

private theorem affineOrbit_mod19683_eq_13426_of_exponent_2869
    (N : Nat) (hN : N % 19683 = 2869) : affineOrbit N % 19683 = 13426 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 9 N 2869).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod19683_pattern_120201002_2869
    (N : Nat) (hAmod : affineOrbit N % 19683 = 13426) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_three_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_three_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_one_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) := by
    rw [badChannel_one_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) := by
    rw [badChannel_zero_iff, hd7] at hbad7
    simpa using hbad7
  rw [badChannel_zero_iff, hd8] at hbad8
  simpa using hbad8

theorem commonTwo_of_mod19683_2869
    (N : Nat) (hN : N % 19683 = 2869) : CommonTwo N := by
  exact commonTwo_of_mod19683_pattern_120201002_2869 N
    (affineOrbit_mod19683_eq_13426_of_exponent_2869 N hN)

theorem physical_happy_of_mod19683_2869
    (N : Nat) (hN : N % 19683 = 2869) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod19683_2869 N hN)

theorem four_power_happy_propagates_of_next_mod19683_2869
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 19683 = 2869) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod19683_2869 (K+1) hNext

#check physical_happy_of_mod19683_14527
#check physical_happy_of_mod19683_2869
#print axioms physical_happy_of_mod19683_14527
#print axioms physical_happy_of_mod19683_2869

end GSTFourPowerAffineNinthTritNext
