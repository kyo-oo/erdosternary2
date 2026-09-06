import GSTFourPowerAffineSixthTrit698_700

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit701_708

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_74_of_exponent_701
    (N : Nat) (hN : N % 729 = 701) : affineOrbit N % 729 = 74 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 701).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_2022_701
    (N : Nat) (hAmod : affineOrbit N % 729 = 74) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  rw [badChannel_three_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_sevenZeroOne (N : Nat) (hN : N % 729 = 701) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_2022_701 N (affineOrbit_mod729_eq_74_of_exponent_701 N hN)

theorem physical_happy_of_mod729_sevenZeroOne
    (N : Nat) (hN : N % 729 = 701) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenZeroOne N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenZeroOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 701) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenZeroOne (K+1) hNext

private theorem affineOrbit_mod729_eq_297_of_exponent_702
    (N : Nat) (hN : N % 729 = 702) : affineOrbit N % 729 = 297 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 702).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_0002_702
    (N : Nat) (hAmod : affineOrbit N % 729 = 297) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  rw [badChannel_zero_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_sevenZeroTwo (N : Nat) (hN : N % 729 = 702) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_0002_702 N (affineOrbit_mod729_eq_297_of_exponent_702 N hN)

theorem physical_happy_of_mod729_sevenZeroTwo
    (N : Nat) (hN : N % 729 = 702) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenZeroTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenZeroTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 702) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenZeroTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_460_of_exponent_703
    (N : Nat) (hN : N % 729 = 703) : affineOrbit N % 729 = 460 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 703).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_1002_703
    (N : Nat) (hAmod : affineOrbit N % 729 = 460) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  rw [badChannel_zero_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_sevenZeroThree (N : Nat) (hN : N % 729 = 703) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_1002_703 N (affineOrbit_mod729_eq_460_of_exponent_703 N hN)

theorem physical_happy_of_mod729_sevenZeroThree
    (N : Nat) (hN : N % 729 = 703) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenZeroThree N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenZeroThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 703) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenZeroThree (K+1) hNext

private theorem affineOrbit_mod729_eq_383_of_exponent_704
    (N : Nat) (hN : N % 729 = 704) : affineOrbit N % 729 = 383 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 704).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_2102_704
    (N : Nat) (hAmod : affineOrbit N % 729 = 383) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_two_iff, hd2] at hbad2
    simpa using hbad2
  rw [badChannel_zero_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_sevenZeroFour (N : Nat) (hN : N % 729 = 704) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_2102_704 N (affineOrbit_mod729_eq_383_of_exponent_704 N hN)

theorem physical_happy_of_mod729_sevenZeroFour
    (N : Nat) (hN : N % 729 = 704) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenZeroFour N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenZeroFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 704) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenZeroFour (K+1) hNext

private theorem affineOrbit_mod729_eq_75_of_exponent_705
    (N : Nat) (hN : N % 729 = 705) : affineOrbit N % 729 = 75 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 705).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_0122_705
    (N : Nat) (hAmod : affineOrbit N % 729 = 75) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad3 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  rw [badChannel_three_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_sevenZeroFive (N : Nat) (hN : N % 729 = 705) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_0122_705 N (affineOrbit_mod729_eq_75_of_exponent_705 N hN)

theorem physical_happy_of_mod729_sevenZeroFive
    (N : Nat) (hN : N % 729 = 705) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenZeroFive N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenZeroFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 705) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenZeroFive (K+1) hNext

private theorem affineOrbit_mod729_eq_301_of_exponent_706
    (N : Nat) (hN : N % 729 = 706) : affineOrbit N % 729 = 301 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 706).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_1102_706
    (N : Nat) (hAmod : affineOrbit N % 729 = 301) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  rw [badChannel_zero_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_sevenZeroSix (N : Nat) (hN : N % 729 = 706) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_1102_706 N (affineOrbit_mod729_eq_301_of_exponent_706 N hN)

theorem physical_happy_of_mod729_sevenZeroSix
    (N : Nat) (hN : N % 729 = 706) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenZeroSix N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenZeroSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 706) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenZeroSix (K+1) hNext

private theorem affineOrbit_mod729_eq_476_of_exponent_707
    (N : Nat) (hN : N % 729 = 707) : affineOrbit N % 729 = 476 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 707).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_22_707
    (N : Nat) (hAmod : affineOrbit N % 729 = 476) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  rw [badChannel_three_iff, hd1] at hbad1
  simpa using hbad1

theorem commonTwo_of_mod729_sevenZeroSeven (N : Nat) (hN : N % 729 = 707) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_707 N (affineOrbit_mod729_eq_476_of_exponent_707 N hN)

theorem physical_happy_of_mod729_sevenZeroSeven
    (N : Nat) (hN : N % 729 = 707) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenZeroSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenZeroSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 707) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenZeroSeven (K+1) hNext

private theorem affineOrbit_mod729_eq_447_of_exponent_708
    (N : Nat) (hN : N % 729 = 708) : affineOrbit N % 729 = 447 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 708).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_02_708
    (N : Nat) (hAmod : affineOrbit N % 729 = 447) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  rw [badChannel_zero_iff, hd1] at hbad1
  simpa using hbad1

theorem commonTwo_of_mod729_sevenZeroEight (N : Nat) (hN : N % 729 = 708) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_708 N (affineOrbit_mod729_eq_447_of_exponent_708 N hN)

theorem physical_happy_of_mod729_sevenZeroEight
    (N : Nat) (hN : N % 729 = 708) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sevenZeroEight N hN)

theorem four_power_happy_propagates_of_next_mod729_sevenZeroEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 708) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sevenZeroEight (K+1) hNext

#check commonTwo_of_mod729_sevenZeroOne
#check physical_happy_of_mod729_sevenZeroOne
#check four_power_happy_propagates_of_next_mod729_sevenZeroOne
#check commonTwo_of_mod729_sevenZeroTwo
#check physical_happy_of_mod729_sevenZeroTwo
#check four_power_happy_propagates_of_next_mod729_sevenZeroTwo
#check commonTwo_of_mod729_sevenZeroThree
#check physical_happy_of_mod729_sevenZeroThree
#check four_power_happy_propagates_of_next_mod729_sevenZeroThree
#check commonTwo_of_mod729_sevenZeroFour
#check physical_happy_of_mod729_sevenZeroFour
#check four_power_happy_propagates_of_next_mod729_sevenZeroFour
#check commonTwo_of_mod729_sevenZeroFive
#check physical_happy_of_mod729_sevenZeroFive
#check four_power_happy_propagates_of_next_mod729_sevenZeroFive
#check commonTwo_of_mod729_sevenZeroSix
#check physical_happy_of_mod729_sevenZeroSix
#check four_power_happy_propagates_of_next_mod729_sevenZeroSix
#check commonTwo_of_mod729_sevenZeroSeven
#check physical_happy_of_mod729_sevenZeroSeven
#check four_power_happy_propagates_of_next_mod729_sevenZeroSeven
#check commonTwo_of_mod729_sevenZeroEight
#check physical_happy_of_mod729_sevenZeroEight
#check four_power_happy_propagates_of_next_mod729_sevenZeroEight
#print axioms commonTwo_of_mod729_sevenZeroOne
#print axioms physical_happy_of_mod729_sevenZeroOne
#print axioms four_power_happy_propagates_of_next_mod729_sevenZeroOne
#print axioms commonTwo_of_mod729_sevenZeroTwo
#print axioms physical_happy_of_mod729_sevenZeroTwo
#print axioms four_power_happy_propagates_of_next_mod729_sevenZeroTwo
#print axioms commonTwo_of_mod729_sevenZeroThree
#print axioms physical_happy_of_mod729_sevenZeroThree
#print axioms four_power_happy_propagates_of_next_mod729_sevenZeroThree
#print axioms commonTwo_of_mod729_sevenZeroFour
#print axioms physical_happy_of_mod729_sevenZeroFour
#print axioms four_power_happy_propagates_of_next_mod729_sevenZeroFour
#print axioms commonTwo_of_mod729_sevenZeroFive
#print axioms physical_happy_of_mod729_sevenZeroFive
#print axioms four_power_happy_propagates_of_next_mod729_sevenZeroFive
#print axioms commonTwo_of_mod729_sevenZeroSix
#print axioms physical_happy_of_mod729_sevenZeroSix
#print axioms four_power_happy_propagates_of_next_mod729_sevenZeroSix
#print axioms commonTwo_of_mod729_sevenZeroSeven
#print axioms physical_happy_of_mod729_sevenZeroSeven
#print axioms four_power_happy_propagates_of_next_mod729_sevenZeroSeven
#print axioms commonTwo_of_mod729_sevenZeroEight
#print axioms physical_happy_of_mod729_sevenZeroEight
#print axioms four_power_happy_propagates_of_next_mod729_sevenZeroEight

end GSTFourPowerAffineSixthTrit701_708
