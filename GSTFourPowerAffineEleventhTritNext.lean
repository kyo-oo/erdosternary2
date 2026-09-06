import GSTFourPowerAffineTenthTritNext

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineEleventhTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod177147_eq_169139_of_exponent_17
    (N : Nat) (hN : N % 177147 = 17) : affineOrbit N % 177147 = 169139 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 11 N 17).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod177147_pattern_20100012122_17
    (N : Nat) (hAmod : affineOrbit N % 177147 = 169139) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_zero_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_zero_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) := by
    rw [badChannel_zero_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) := by
    rw [badChannel_one_iff, hd7] at hbad7
    simpa using hbad7
  have hbad9 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) := by
    rw [badChannel_three_iff, hd8] at hbad8
    simpa using hbad8
  have hbad10 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) := by
    rw [badChannel_two_iff, hd9] at hbad9
    simpa using hbad9
  rw [badChannel_three_iff, hd10] at hbad10
  simpa using hbad10

theorem commonTwo_of_mod177147_17
    (N : Nat) (hN : N % 177147 = 17) : CommonTwo N := by
  exact commonTwo_of_mod177147_pattern_20100012122_17 N
    (affineOrbit_mod177147_eq_169139_of_exponent_17 N hN)

theorem physical_happy_of_mod177147_17
    (N : Nat) (hN : N % 177147 = 17) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod177147_17 N hN)

theorem four_power_happy_propagates_of_next_mod177147_17
    (K p : Nat) (hK : 10 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 177147 = 17) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod177147_17 (K+1) hNext

private theorem affineOrbit_mod177147_eq_120717_of_exponent_27
    (N : Nat) (hN : N % 177147 = 27) : affineOrbit N % 177147 = 120717 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 11 N 27).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod177147_pattern_00012101002_27
    (N : Nat) (hAmod : affineOrbit N % 177147 = 120717) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
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
  have hbad6 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_three_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) := by
    rw [badChannel_two_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) := by
    rw [badChannel_zero_iff, hd7] at hbad7
    simpa using hbad7
  have hbad9 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) := by
    rw [badChannel_one_iff, hd8] at hbad8
    simpa using hbad8
  have hbad10 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) := by
    rw [badChannel_zero_iff, hd9] at hbad9
    simpa using hbad9
  rw [badChannel_zero_iff, hd10] at hbad10
  simpa using hbad10

theorem commonTwo_of_mod177147_27
    (N : Nat) (hN : N % 177147 = 27) : CommonTwo N := by
  exact commonTwo_of_mod177147_pattern_00012101002_27 N
    (affineOrbit_mod177147_eq_120717_of_exponent_27 N hN)

theorem physical_happy_of_mod177147_27
    (N : Nat) (hN : N % 177147 = 27) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod177147_27 N hN)

theorem four_power_happy_propagates_of_next_mod177147_27
    (K p : Nat) (hK : 10 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 177147 = 27) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod177147_27 (K+1) hNext

private theorem affineOrbit_mod177147_eq_128575_of_exponent_28
    (N : Nat) (hN : N % 177147 = 28) : affineOrbit N % 177147 = 128575 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 11 N 28).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod177147_pattern_10010121102_28
    (N : Nat) (hAmod : affineOrbit N % 177147 = 128575) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_zero_iff, hd5] at hbad5
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
  rw [badChannel_zero_iff, hd10] at hbad10
  simpa using hbad10

theorem commonTwo_of_mod177147_28
    (N : Nat) (hN : N % 177147 = 28) : CommonTwo N := by
  exact commonTwo_of_mod177147_pattern_10010121102_28 N
    (affineOrbit_mod177147_eq_128575_of_exponent_28 N hN)

theorem physical_happy_of_mod177147_28
    (N : Nat) (hN : N % 177147 = 28) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod177147_28 N hN)

theorem four_power_happy_propagates_of_next_mod177147_28
    (K p : Nat) (hK : 10 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 177147 = 28) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod177147_28 (K+1) hNext

private theorem affineOrbit_mod177147_eq_123284_of_exponent_35
    (N : Nat) (hN : N % 177147 = 35) : affineOrbit N % 177147 = 123284 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 11 N 35).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod177147_pattern_20001012002_35
    (N : Nat) (hAmod : affineOrbit N % 177147 = 123284) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd7 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd8 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd9 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd10 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad5 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_zero_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_one_iff, hd5] at hbad5
    simpa using hbad5
  have hbad7 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))) := by
    rw [badChannel_zero_iff, hd6] at hbad6
    simpa using hbad6
  have hbad8 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))) := by
    rw [badChannel_one_iff, hd7] at hbad7
    simpa using hbad7
  have hbad9 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))))))) := by
    rw [badChannel_three_iff, hd8] at hbad8
    simpa using hbad8
  have hbad10 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))))))) := by
    rw [badChannel_one_iff, hd9] at hbad9
    simpa using hbad9
  rw [badChannel_zero_iff, hd10] at hbad10
  simpa using hbad10

theorem commonTwo_of_mod177147_35
    (N : Nat) (hN : N % 177147 = 35) : CommonTwo N := by
  exact commonTwo_of_mod177147_pattern_20001012002_35 N
    (affineOrbit_mod177147_eq_123284_of_exponent_35 N hN)

theorem physical_happy_of_mod177147_35
    (N : Nat) (hN : N % 177147 = 35) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod177147_35 N hN)

theorem four_power_happy_propagates_of_next_mod177147_35
    (K p : Nat) (hK : 10 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 177147 = 35) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod177147_35 (K+1) hNext

end GSTFourPowerAffineEleventhTritNext
