import GSTFourPowerAffineThirteenthTritNext

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineFourteenthTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod4782969_eq_3237745_of_exponent_13
    (N : Nat) (hN : N % 4782969 = 13) : affineOrbit N % 4782969 = 3237745 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 14 N 13).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod4782969_pattern_11100111120002_13
    (N : Nat) (hAmod : affineOrbit N % 4782969 = 3237745) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd11 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd12 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd13 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))) := by
    rw [badChannel_zero_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))) := by
    rw [badChannel_zero_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))) := by
    rw [badChannel_one_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))) := by
    rw [badChannel_one_iff, hd7] at hbad7
    simpa using hbad7
  have hbad9 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))) := by
    rw [badChannel_one_iff, hd8] at hbad8
    simpa using hbad8
  have hbad10 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))) := by
    rw [badChannel_one_iff, hd9] at hbad9
    simpa using hbad9
  have hbad11 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))) := by
    rw [badChannel_three_iff, hd10] at hbad10
    simpa using hbad10
  have hbad12 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))))) := by
    rw [badChannel_one_iff, hd11] at hbad11
    simpa using hbad11
  have hbad13 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))))) := by
    rw [badChannel_zero_iff, hd12] at hbad12
    simpa using hbad12
  rw [badChannel_zero_iff, hd13] at hbad13
  simpa using hbad13

theorem commonTwo_of_mod4782969_13
    (N : Nat) (hN : N % 4782969 = 13) : CommonTwo N := by
  exact commonTwo_of_mod4782969_pattern_11100111120002_13 N
    (affineOrbit_mod4782969_eq_3237745_of_exponent_13 N hN)

theorem physical_happy_of_mod4782969_13
    (N : Nat) (hN : N % 4782969 = 13) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod4782969_13 N hN)

theorem four_power_happy_propagates_of_next_mod4782969_13
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 4782969 = 13) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod4782969_13 (K+1) hNext

private theorem affineOrbit_mod4782969_eq_3461495_of_exponent_92
    (N : Nat) (hN : N % 4782969 = 92) : affineOrbit N % 4782969 = 3461495 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 14 N 92).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod4782969_pattern_21112021211102_92
    (N : Nat) (hAmod : affineOrbit N % 4782969 = 3461495) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd11 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd12 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd13 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 2 (tail3 (tail3 (A))) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 2 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_two_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))) := by
    rw [badChannel_two_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))) := by
    rw [badChannel_three_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))) := by
    rw [badChannel_one_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))) := by
    rw [badChannel_three_iff, hd7] at hbad7
    simpa using hbad7
  have hbad9 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))) := by
    rw [badChannel_two_iff, hd8] at hbad8
    simpa using hbad8
  have hbad10 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))) := by
    rw [badChannel_three_iff, hd9] at hbad9
    simpa using hbad9
  have hbad11 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))) := by
    rw [badChannel_two_iff, hd10] at hbad10
    simpa using hbad10
  have hbad12 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))))) := by
    rw [badChannel_two_iff, hd11] at hbad11
    simpa using hbad11
  have hbad13 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))))) := by
    rw [badChannel_two_iff, hd12] at hbad12
    simpa using hbad12
  rw [badChannel_zero_iff, hd13] at hbad13
  simpa using hbad13

theorem commonTwo_of_mod4782969_92
    (N : Nat) (hN : N % 4782969 = 92) : CommonTwo N := by
  exact commonTwo_of_mod4782969_pattern_21112021211102_92 N
    (affineOrbit_mod4782969_eq_3461495_of_exponent_92 N hN)

theorem physical_happy_of_mod4782969_92
    (N : Nat) (hN : N % 4782969 = 92) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod4782969_92 N hN)

theorem four_power_happy_propagates_of_next_mod4782969_92
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 4782969 = 92) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod4782969_92 (K+1) hNext

private theorem affineOrbit_mod4782969_eq_3250453_of_exponent_490
    (N : Nat) (hN : N % 4782969 = 490) : affineOrbit N % 4782969 = 3250453 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 14 N 490).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod4782969_pattern_11001201001002_490
    (N : Nat) (hAmod : affineOrbit N % 4782969 = 3250453) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd11 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd12 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd13 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))) := by
    rw [badChannel_zero_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))) := by
    rw [badChannel_one_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))) := by
    rw [badChannel_three_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))) := by
    rw [badChannel_one_iff, hd7] at hbad7
    simpa using hbad7
  have hbad9 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))) := by
    rw [badChannel_one_iff, hd8] at hbad8
    simpa using hbad8
  have hbad10 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))) := by
    rw [badChannel_zero_iff, hd9] at hbad9
    simpa using hbad9
  have hbad11 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))) := by
    rw [badChannel_zero_iff, hd10] at hbad10
    simpa using hbad10
  have hbad12 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))))) := by
    rw [badChannel_one_iff, hd11] at hbad11
    simpa using hbad11
  have hbad13 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))))) := by
    rw [badChannel_zero_iff, hd12] at hbad12
    simpa using hbad12
  rw [badChannel_zero_iff, hd13] at hbad13
  simpa using hbad13

theorem commonTwo_of_mod4782969_490
    (N : Nat) (hN : N % 4782969 = 490) : CommonTwo N := by
  exact commonTwo_of_mod4782969_pattern_11001201001002_490 N
    (affineOrbit_mod4782969_eq_3250453_of_exponent_490 N hN)

theorem physical_happy_of_mod4782969_490
    (N : Nat) (hN : N % 4782969 = 490) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod4782969_490 N hN)

theorem four_power_happy_propagates_of_next_mod4782969_490
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 4782969 = 490) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod4782969_490 (K+1) hNext

private theorem affineOrbit_mod4782969_eq_4444437_of_exponent_516
    (N : Nat) (hN : N % 4782969 = 516) : affineOrbit N % 4782969 = 4444437 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 14 N 516).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod4782969_pattern_01212101200122_516
    (N : Nat) (hAmod : affineOrbit N % 4782969 = 4444437) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd11 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd12 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd13 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 3 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_three_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))) := by
    rw [badChannel_two_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))) := by
    rw [badChannel_three_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))) := by
    rw [badChannel_two_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))) := by
    rw [badChannel_zero_iff, hd7] at hbad7
    simpa using hbad7
  have hbad9 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))) := by
    rw [badChannel_one_iff, hd8] at hbad8
    simpa using hbad8
  have hbad10 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))) := by
    rw [badChannel_three_iff, hd9] at hbad9
    simpa using hbad9
  have hbad11 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))) := by
    rw [badChannel_one_iff, hd10] at hbad10
    simpa using hbad10
  have hbad12 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A))))))))))))) := by
    rw [badChannel_zero_iff, hd11] at hbad11
    simpa using hbad11
  have hbad13 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (A)))))))))))))) := by
    rw [badChannel_one_iff, hd12] at hbad12
    simpa using hbad12
  rw [badChannel_three_iff, hd13] at hbad13
  simpa using hbad13

theorem commonTwo_of_mod4782969_516
    (N : Nat) (hN : N % 4782969 = 516) : CommonTwo N := by
  exact commonTwo_of_mod4782969_pattern_01212101200122_516 N
    (affineOrbit_mod4782969_eq_4444437_of_exponent_516 N hN)

theorem physical_happy_of_mod4782969_516
    (N : Nat) (hN : N % 4782969 = 516) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod4782969_516 N hN)

theorem four_power_happy_propagates_of_next_mod4782969_516
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 4782969 = 516) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod4782969_516 (K+1) hNext

#check physical_happy_of_mod4782969_13
#check physical_happy_of_mod4782969_92
#check physical_happy_of_mod4782969_490
#check physical_happy_of_mod4782969_516

#print axioms physical_happy_of_mod4782969_13
#print axioms physical_happy_of_mod4782969_92
#print axioms physical_happy_of_mod4782969_490
#print axioms physical_happy_of_mod4782969_516

end GSTFourPowerAffineFourteenthTritNext
