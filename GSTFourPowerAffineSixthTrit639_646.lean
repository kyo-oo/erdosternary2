import GSTFourPowerAffineSixthTrit631_636

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit639_646

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_504_of_exponent_639
    (N : Nat) (hN : N % 729 = 639) : affineOrbit N % 729 = 504 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 639).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_002_639
    (N : Nat) (hAmod : affineOrbit N % 729 = 504) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixThreeNine (N : Nat) (hN : N % 729 = 639) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_002_639 N (affineOrbit_mod729_eq_504_of_exponent_639 N hN)

theorem physical_happy_of_mod729_sixThreeNine
    (N : Nat) (hN : N % 729 = 639) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixThreeNine N hN)

theorem four_power_happy_propagates_of_next_mod729_sixThreeNine
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 639) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixThreeNine (K+1) hNext

private theorem affineOrbit_mod729_eq_559_of_exponent_640
    (N : Nat) (hN : N % 729 = 640) : affineOrbit N % 729 = 559 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 640).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_102_640
    (N : Nat) (hAmod : affineOrbit N % 729 = 559) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixFourZero (N : Nat) (hN : N % 729 = 640) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_102_640 N (affineOrbit_mod729_eq_559_of_exponent_640 N hN)

theorem physical_happy_of_mod729_sixFourZero
    (N : Nat) (hN : N % 729 = 640) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixFourZero N hN)

theorem four_power_happy_propagates_of_next_mod729_sixFourZero
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 640) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixFourZero (K+1) hNext

private theorem affineOrbit_mod729_eq_76_of_exponent_643
    (N : Nat) (hN : N % 729 = 643) : affineOrbit N % 729 = 76 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 643).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_1122_643
    (N : Nat) (hAmod : affineOrbit N % 729 = 76) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixFourThree (N : Nat) (hN : N % 729 = 643) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_1122_643 N (affineOrbit_mod729_eq_76_of_exponent_643 N hN)

theorem physical_happy_of_mod729_sixFourThree
    (N : Nat) (hN : N % 729 = 643) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixFourThree N hN)

theorem four_power_happy_propagates_of_next_mod729_sixFourThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 643) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixFourThree (K+1) hNext

private theorem affineOrbit_mod729_eq_305_of_exponent_644
    (N : Nat) (hN : N % 729 = 644) : affineOrbit N % 729 = 305 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 644).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_22_644
    (N : Nat) (hAmod : affineOrbit N % 729 = 305) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixFourFour (N : Nat) (hN : N % 729 = 644) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_644 N (affineOrbit_mod729_eq_305_of_exponent_644 N hN)

theorem physical_happy_of_mod729_sixFourFour
    (N : Nat) (hN : N % 729 = 644) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixFourFour N hN)

theorem four_power_happy_propagates_of_next_mod729_sixFourFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 644) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixFourFour (K+1) hNext

private theorem affineOrbit_mod729_eq_492_of_exponent_645
    (N : Nat) (hN : N % 729 = 645) : affineOrbit N % 729 = 492 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 645).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_02_645
    (N : Nat) (hAmod : affineOrbit N % 729 = 492) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixFourFive (N : Nat) (hN : N % 729 = 645) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_645 N (affineOrbit_mod729_eq_492_of_exponent_645 N hN)

theorem physical_happy_of_mod729_sixFourFive
    (N : Nat) (hN : N % 729 = 645) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixFourFive N hN)

theorem four_power_happy_propagates_of_next_mod729_sixFourFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 645) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixFourFive (K+1) hNext

private theorem affineOrbit_mod729_eq_511_of_exponent_646
    (N : Nat) (hN : N % 729 = 646) : affineOrbit N % 729 = 511 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 646).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_122_646
    (N : Nat) (hAmod : affineOrbit N % 729 = 511) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixFourSix (N : Nat) (hN : N % 729 = 646) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_122_646 N (affineOrbit_mod729_eq_511_of_exponent_646 N hN)

theorem physical_happy_of_mod729_sixFourSix
    (N : Nat) (hN : N % 729 = 646) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixFourSix N hN)

theorem four_power_happy_propagates_of_next_mod729_sixFourSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 646) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixFourSix (K+1) hNext

end GSTFourPowerAffineSixthTrit639_646
