import GSTFourPowerAffineSixthTrit575_578

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit581_587

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_377_of_exponent_581
    (N : Nat) (hN : N % 729 = 581) :
    affineOrbit N % 729 = 377 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 581).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_22_581
    (N : Nat) (hAmod : affineOrbit N % 729 = 377) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveEightOne
    (N : Nat) (hN : N % 729 = 581) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_581 N
    (affineOrbit_mod729_eq_377_of_exponent_581 N hN)

theorem physical_happy_of_mod729_fiveEightOne
    (N : Nat) (hN : N % 729 = 581) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveEightOne N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveEightOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 581) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveEightOne (K+1) hNext

private theorem affineOrbit_mod729_eq_51_of_exponent_582
    (N : Nat) (hN : N % 729 = 582) :
    affineOrbit N % 729 = 51 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 582).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_02_582
    (N : Nat) (hAmod : affineOrbit N % 729 = 51) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveEightTwo
    (N : Nat) (hN : N % 729 = 582) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_582 N
    (affineOrbit_mod729_eq_51_of_exponent_582 N hN)

theorem physical_happy_of_mod729_fiveEightTwo
    (N : Nat) (hN : N % 729 = 582) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveEightTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveEightTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 582) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveEightTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_369_of_exponent_585
    (N : Nat) (hN : N % 729 = 585) :
    affineOrbit N % 729 = 369 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 585).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_002_585
    (N : Nat) (hAmod : affineOrbit N % 729 = 369) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveEightFive
    (N : Nat) (hN : N % 729 = 585) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_002_585 N
    (affineOrbit_mod729_eq_369_of_exponent_585 N hN)

theorem physical_happy_of_mod729_fiveEightFive
    (N : Nat) (hN : N % 729 = 585) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveEightFive N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveEightFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 585) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveEightFive (K+1) hNext

private theorem affineOrbit_mod729_eq_19_of_exponent_586
    (N : Nat) (hN : N % 729 = 586) :
    affineOrbit N % 729 = 19 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 586).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_102_586
    (N : Nat) (hAmod : affineOrbit N % 729 = 19) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveEightSix
    (N : Nat) (hN : N % 729 = 586) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_102_586 N
    (affineOrbit_mod729_eq_19_of_exponent_586 N hN)

theorem physical_happy_of_mod729_fiveEightSix
    (N : Nat) (hN : N % 729 = 586) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveEightSix N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveEightSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 586) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveEightSix (K+1) hNext

private theorem affineOrbit_mod729_eq_77_of_exponent_587
    (N : Nat) (hN : N % 729 = 587) :
    affineOrbit N % 729 = 77 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 587).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_2122_587
    (N : Nat) (hAmod : affineOrbit N % 729 = 77) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
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

theorem commonTwo_of_mod729_fiveEightSeven
    (N : Nat) (hN : N % 729 = 587) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_2122_587 N
    (affineOrbit_mod729_eq_77_of_exponent_587 N hN)

theorem physical_happy_of_mod729_fiveEightSeven
    (N : Nat) (hN : N % 729 = 587) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveEightSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveEightSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 587) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveEightSeven (K+1) hNext

end GSTFourPowerAffineSixthTrit581_587
