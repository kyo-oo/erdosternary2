import GSTFourPowerAffineTwelfthTritNext

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineThirteenthTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod1594323_eq_1497235_of_exponent_31
    (N : Nat) (hN : N % 1594323 = 31) : affineOrbit N % 1594323 = 1497235 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 13 N 31).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod1594323_pattern_1101121001122_31
    (N : Nat) (hAmod : affineOrbit N % 1594323 = 1497235) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd11 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd12 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad5 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_one_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) := by
    rw [badChannel_three_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) := by
    rw [badChannel_two_iff, hd7] at hbad7
    simpa using hbad7
  have hbad9 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) := by
    rw [badChannel_zero_iff, hd8] at hbad8
    simpa using hbad8
  have hbad10 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) := by
    rw [badChannel_zero_iff, hd9] at hbad9
    simpa using hbad9
  have hbad11 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))))) := by
    rw [badChannel_one_iff, hd10] at hbad10
    simpa using hbad10
  have hbad12 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))))) := by
    rw [badChannel_one_iff, hd11] at hbad11
    simpa using hbad11
  rw [badChannel_three_iff, hd12] at hbad12
  simpa using hbad12

theorem commonTwo_of_mod1594323_31
    (N : Nat) (hN : N % 1594323 = 31) : CommonTwo N := by
  exact commonTwo_of_mod1594323_pattern_1101121001122_31 N
    (affineOrbit_mod1594323_eq_1497235_of_exponent_31 N hN)

theorem physical_happy_of_mod1594323_31
    (N : Nat) (hN : N % 1594323 = 31) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod1594323_31 N hN)

theorem four_power_happy_propagates_of_next_mod1594323_31
    (K p : Nat) (hK : 12 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 1594323 = 31) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod1594323_31 (K+1) hNext

private theorem affineOrbit_mod1594323_eq_1132328_of_exponent_62
    (N : Nat) (hN : N % 1594323 = 62) : affineOrbit N % 1594323 = 1132328 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 13 N 62).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod1594323_pattern_2001202110102_62
    (N : Nat) (hAmod : affineOrbit N % 1594323 = 1132328) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd11 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd12 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_three_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) := by
    rw [badChannel_one_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) := by
    rw [badChannel_three_iff, hd7] at hbad7
    simpa using hbad7
  have hbad9 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) := by
    rw [badChannel_two_iff, hd8] at hbad8
    simpa using hbad8
  have hbad10 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) := by
    rw [badChannel_two_iff, hd9] at hbad9
    simpa using hbad9
  have hbad11 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))))) := by
    rw [badChannel_zero_iff, hd10] at hbad10
    simpa using hbad10
  have hbad12 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))))) := by
    rw [badChannel_one_iff, hd11] at hbad11
    simpa using hbad11
  rw [badChannel_zero_iff, hd12] at hbad12
  simpa using hbad12

theorem commonTwo_of_mod1594323_62
    (N : Nat) (hN : N % 1594323 = 62) : CommonTwo N := by
  exact commonTwo_of_mod1594323_pattern_2001202110102_62 N
    (affineOrbit_mod1594323_eq_1132328_of_exponent_62 N hN)

theorem physical_happy_of_mod1594323_62
    (N : Nat) (hN : N % 1594323 = 62) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod1594323_62 N hN)

theorem four_power_happy_propagates_of_next_mod1594323_62
    (K p : Nat) (hK : 12 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 1594323 = 62) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod1594323_62 (K+1) hNext

end GSTFourPowerAffineThirteenthTritNext
