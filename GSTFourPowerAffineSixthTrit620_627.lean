import GSTFourPowerAffineSixthTrit617_619

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit620_627

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_479_of_exponent_620
    (N : Nat) (hN : N % 729 = 620) : affineOrbit N % 729 = 479 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 620).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `2022` forces `1 -> 3 -> 1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_2022_620
    (N : Nat) (hAmod : affineOrbit N % 729 = 479) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
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

theorem commonTwo_of_mod729_sixTwoZero (N : Nat) (hN : N % 729 = 620) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_2022_620 N (affineOrbit_mod729_eq_479_of_exponent_620 N hN)

theorem physical_happy_of_mod729_sixTwoZero
    (N : Nat) (hN : N % 729 = 620) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixTwoZero N hN)

theorem four_power_happy_propagates_of_next_mod729_sixTwoZero
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 620) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixTwoZero (K+1) hNext

private theorem affineOrbit_mod729_eq_459_of_exponent_621
    (N : Nat) (hN : N % 729 = 621) : affineOrbit N % 729 = 459 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 621).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `0002` forces `1 -> 0 -> 0 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_0002_621
    (N : Nat) (hAmod : affineOrbit N % 729 = 459) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
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

theorem commonTwo_of_mod729_sixTwoOne (N : Nat) (hN : N % 729 = 621) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_0002_621 N (affineOrbit_mod729_eq_459_of_exponent_621 N hN)

theorem physical_happy_of_mod729_sixTwoOne
    (N : Nat) (hN : N % 729 = 621) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixTwoOne N hN)

theorem four_power_happy_propagates_of_next_mod729_sixTwoOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 621) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixTwoOne (K+1) hNext

private theorem affineOrbit_mod729_eq_379_of_exponent_622
    (N : Nat) (hN : N % 729 = 622) : affineOrbit N % 729 = 379 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 622).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `1002` forces `1 -> 1 -> 0 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_1002_622
    (N : Nat) (hAmod : affineOrbit N % 729 = 379) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
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

theorem commonTwo_of_mod729_sixTwoTwo (N : Nat) (hN : N % 729 = 622) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_1002_622 N (affineOrbit_mod729_eq_379_of_exponent_622 N hN)

theorem physical_happy_of_mod729_sixTwoTwo
    (N : Nat) (hN : N % 729 = 622) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixTwoTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_sixTwoTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 622) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixTwoTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_59_of_exponent_623
    (N : Nat) (hN : N % 729 = 623) : affineOrbit N % 729 = 59 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 623).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `2102` forces `1 -> 3 -> 2 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_2102_623
    (N : Nat) (hAmod : affineOrbit N % 729 = 59) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
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

theorem commonTwo_of_mod729_sixTwoThree (N : Nat) (hN : N % 729 = 623) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_2102_623 N (affineOrbit_mod729_eq_59_of_exponent_623 N hN)

theorem physical_happy_of_mod729_sixTwoThree
    (N : Nat) (hN : N % 729 = 623) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixTwoThree N hN)

theorem four_power_happy_propagates_of_next_mod729_sixTwoThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 623) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixTwoThree (K+1) hNext

private theorem affineOrbit_mod729_eq_237_of_exponent_624
    (N : Nat) (hN : N % 729 = 624) : affineOrbit N % 729 = 237 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 624).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `0122` forces `1 -> 0 -> 1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_0122_624
    (N : Nat) (hAmod : affineOrbit N % 729 = 237) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
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

theorem commonTwo_of_mod729_sixTwoFour (N : Nat) (hN : N % 729 = 624) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_0122_624 N (affineOrbit_mod729_eq_237_of_exponent_624 N hN)

theorem physical_happy_of_mod729_sixTwoFour
    (N : Nat) (hN : N % 729 = 624) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixTwoFour N hN)

theorem four_power_happy_propagates_of_next_mod729_sixTwoFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 624) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixTwoFour (K+1) hNext

private theorem affineOrbit_mod729_eq_220_of_exponent_625
    (N : Nat) (hN : N % 729 = 625) : affineOrbit N % 729 = 220 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 625).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `1102` forces `1 -> 1 -> 1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_1102_625
    (N : Nat) (hAmod : affineOrbit N % 729 = 220) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
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

theorem commonTwo_of_mod729_sixTwoFive (N : Nat) (hN : N % 729 = 625) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_1102_625 N (affineOrbit_mod729_eq_220_of_exponent_625 N hN)

theorem physical_happy_of_mod729_sixTwoFive
    (N : Nat) (hN : N % 729 = 625) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixTwoFive N hN)

theorem four_power_happy_propagates_of_next_mod729_sixTwoFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 625) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixTwoFive (K+1) hNext

private theorem affineOrbit_mod729_eq_152_of_exponent_626
    (N : Nat) (hN : N % 729 = 626) : affineOrbit N % 729 = 152 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 626).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` forces `1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_22_626
    (N : Nat) (hAmod : affineOrbit N % 729 = 152) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixTwoSix (N : Nat) (hN : N % 729 = 626) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_626 N (affineOrbit_mod729_eq_152_of_exponent_626 N hN)

theorem physical_happy_of_mod729_sixTwoSix
    (N : Nat) (hN : N % 729 = 626) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixTwoSix N hN)

theorem four_power_happy_propagates_of_next_mod729_sixTwoSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 626) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixTwoSix (K+1) hNext

private theorem affineOrbit_mod729_eq_609_of_exponent_627
    (N : Nat) (hN : N % 729 = 627) : affineOrbit N % 729 = 609 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 627).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` forces `1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_02_627
    (N : Nat) (hAmod : affineOrbit N % 729 = 609) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixTwoSeven (N : Nat) (hN : N % 729 = 627) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_627 N (affineOrbit_mod729_eq_609_of_exponent_627 N hN)

theorem physical_happy_of_mod729_sixTwoSeven
    (N : Nat) (hN : N % 729 = 627) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixTwoSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_sixTwoSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 627) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixTwoSeven (K+1) hNext

end GSTFourPowerAffineSixthTrit620_627
