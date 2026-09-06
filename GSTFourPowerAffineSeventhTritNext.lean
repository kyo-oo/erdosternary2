import GSTFourPowerAffineSeventhTrit719_723

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSeventhTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod2187_eq_2052_of_exponent_675
    (N : Nat) (hN : N % 2187 = 675) : affineOrbit N % 2187 = 2052 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 7 N 675).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod2187_pattern_0001122_675
    (N : Nat) (hAmod : affineOrbit N % 2187 = 2052) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad5 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_one_iff, hd5] at hbad5
    simpa using hbad5
  rw [badChannel_three_iff, hd6] at hbad6
  simpa using hbad6

theorem commonTwo_of_mod2187_675
    (N : Nat) (hN : N % 2187 = 675) : CommonTwo N := by
  exact commonTwo_of_mod2187_pattern_0001122_675 N
    (affineOrbit_mod2187_eq_2052_of_exponent_675 N hN)

theorem physical_happy_of_mod2187_675
    (N : Nat) (hN : N % 2187 = 675) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod2187_675 N hN)

theorem four_power_happy_propagates_of_next_mod2187_675
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 2187 = 675) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod2187_675 (K+1) hNext

private theorem affineOrbit_mod2187_eq_1490_of_exponent_2135
    (N : Nat) (hN : N % 2187 = 2135) : affineOrbit N % 2187 = 1490 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 7 N 2135).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod2187_pattern_2101002_2135
    (N : Nat) (hAmod : affineOrbit N % 2187 = 1490) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 2 (tail3 (tail3 A)) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_two_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_zero_iff, hd5] at hbad5
    simpa using hbad5
  rw [badChannel_zero_iff, hd6] at hbad6
  simpa using hbad6

theorem commonTwo_of_mod2187_2135
    (N : Nat) (hN : N % 2187 = 2135) : CommonTwo N := by
  exact commonTwo_of_mod2187_pattern_2101002_2135 N
    (affineOrbit_mod2187_eq_1490_of_exponent_2135 N hN)

theorem physical_happy_of_mod2187_2135
    (N : Nat) (hN : N % 2187 = 2135) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod2187_2135 N hN)

theorem four_power_happy_propagates_of_next_mod2187_2135
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 2187 = 2135) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod2187_2135 (K+1) hNext

private theorem affineOrbit_mod2187_eq_1587_of_exponent_2136
    (N : Nat) (hN : N % 2187 = 2136) : affineOrbit N % 2187 = 1587 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 7 N 2136).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod2187_pattern_0121102_2136
    (N : Nat) (hAmod : affineOrbit N % 2187 = 1587) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_three_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_two_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_two_iff, hd5] at hbad5
    simpa using hbad5
  rw [badChannel_zero_iff, hd6] at hbad6
  simpa using hbad6

theorem commonTwo_of_mod2187_2136
    (N : Nat) (hN : N % 2187 = 2136) : CommonTwo N := by
  exact commonTwo_of_mod2187_pattern_0121102_2136 N
    (affineOrbit_mod2187_eq_1587_of_exponent_2136 N hN)

theorem physical_happy_of_mod2187_2136
    (N : Nat) (hN : N % 2187 = 2136) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod2187_2136 N hN)

theorem four_power_happy_propagates_of_next_mod2187_2136
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 2187 = 2136) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod2187_2136 (K+1) hNext

private theorem affineOrbit_mod2187_eq_2093_of_exponent_1415
    (N : Nat) (hN : N % 2187 = 1415) : affineOrbit N % 2187 = 2093 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 7 N 1415).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod2187_pattern_2112122_1415
    (N : Nat) (hAmod : affineOrbit N % 2187 = 2093) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 2 (tail3 (tail3 A)) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 2 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_two_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_three_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_two_iff, hd5] at hbad5
    simpa using hbad5
  rw [badChannel_three_iff, hd6] at hbad6
  simpa using hbad6

theorem commonTwo_of_mod2187_1415
    (N : Nat) (hN : N % 2187 = 1415) : CommonTwo N := by
  exact commonTwo_of_mod2187_pattern_2112122_1415 N
    (affineOrbit_mod2187_eq_2093_of_exponent_1415 N hN)

theorem physical_happy_of_mod2187_1415
    (N : Nat) (hN : N % 2187 = 1415) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod2187_1415 N hN)

theorem four_power_happy_propagates_of_next_mod2187_1415
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 2187 = 1415) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod2187_1415 (K+1) hNext

private theorem affineOrbit_mod2187_eq_1481_of_exponent_1424
    (N : Nat) (hN : N % 2187 = 1424) : affineOrbit N % 2187 = 1481 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 7 N 1424).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod2187_pattern_2120002_1424
    (N : Nat) (hAmod : affineOrbit N % 2187 = 1481) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_three_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_zero_iff, hd5] at hbad5
    simpa using hbad5
  rw [badChannel_zero_iff, hd6] at hbad6
  simpa using hbad6

theorem commonTwo_of_mod2187_1424
    (N : Nat) (hN : N % 2187 = 1424) : CommonTwo N := by
  exact commonTwo_of_mod2187_pattern_2120002_1424 N
    (affineOrbit_mod2187_eq_1481_of_exponent_1424 N hN)

theorem physical_happy_of_mod2187_1424
    (N : Nat) (hN : N % 2187 = 1424) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod2187_1424 N hN)

theorem four_power_happy_propagates_of_next_mod2187_1424
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 2187 = 1424) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod2187_1424 (K+1) hNext

private theorem affineOrbit_mod2187_eq_1551_of_exponent_1425
    (N : Nat) (hN : N % 2187 = 1425) : affineOrbit N % 2187 = 1551 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 7 N 1425).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod2187_pattern_0110102_1425
    (N : Nat) (hAmod : affineOrbit N % 2187 = 1551) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_zero_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_one_iff, hd5] at hbad5
    simpa using hbad5
  rw [badChannel_zero_iff, hd6] at hbad6
  simpa using hbad6

theorem commonTwo_of_mod2187_1425
    (N : Nat) (hN : N % 2187 = 1425) : CommonTwo N := by
  exact commonTwo_of_mod2187_pattern_0110102_1425 N
    (affineOrbit_mod2187_eq_1551_of_exponent_1425 N hN)

theorem physical_happy_of_mod2187_1425
    (N : Nat) (hN : N % 2187 = 1425) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod2187_1425 N hN)

theorem four_power_happy_propagates_of_next_mod2187_1425
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 2187 = 1425) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod2187_1425 (K+1) hNext

private theorem affineOrbit_mod2187_eq_2054_of_exponent_710
    (N : Nat) (hN : N % 2187 = 710) : affineOrbit N % 2187 = 2054 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 7 N 710).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod2187_pattern_2001122_710
    (N : Nat) (hAmod : affineOrbit N % 2187 = 2054) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad5 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_one_iff, hd5] at hbad5
    simpa using hbad5
  rw [badChannel_three_iff, hd6] at hbad6
  simpa using hbad6

theorem commonTwo_of_mod2187_710
    (N : Nat) (hN : N % 2187 = 710) : CommonTwo N := by
  exact commonTwo_of_mod2187_pattern_2001122_710 N
    (affineOrbit_mod2187_eq_2054_of_exponent_710 N hN)

theorem physical_happy_of_mod2187_710
    (N : Nat) (hN : N % 2187 = 710) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod2187_710 N hN)

theorem four_power_happy_propagates_of_next_mod2187_710
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 2187 = 710) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod2187_710 (K+1) hNext

private theorem affineOrbit_mod2187_eq_1522_of_exponent_2170
    (N : Nat) (hN : N % 2187 = 2170) : affineOrbit N % 2187 = 1522 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 7 N 2170).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod2187_pattern_1012002_2170
    (N : Nat) (hAmod : affineOrbit N % 2187 = 1522) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd6 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_three_iff, hd4] at hbad4
    simpa using hbad4
  have hbad6 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 (tail3 A)))))) := by
    rw [badChannel_one_iff, hd5] at hbad5
    simpa using hbad5
  rw [badChannel_zero_iff, hd6] at hbad6
  simpa using hbad6

theorem commonTwo_of_mod2187_2170
    (N : Nat) (hN : N % 2187 = 2170) : CommonTwo N := by
  exact commonTwo_of_mod2187_pattern_1012002_2170 N
    (affineOrbit_mod2187_eq_1522_of_exponent_2170 N hN)

theorem physical_happy_of_mod2187_2170
    (N : Nat) (hN : N % 2187 = 2170) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod2187_2170 N hN)

theorem four_power_happy_propagates_of_next_mod2187_2170
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 2187 = 2170) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod2187_2170 (K+1) hNext

end GSTFourPowerAffineSeventhTritNext
