import GSTFourPowerAffineSixthTrit620_627

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit631_636

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_712_of_exponent_631
    (N : Nat) (hN : N % 729 = 631) : affineOrbit N % 729 = 712 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 631).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `10122` forces `1 -> 1 -> 0 -> 1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_10122_631
    (N : Nat) (hAmod : affineOrbit N % 729 = 712) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_sixThreeOne (N : Nat) (hN : N % 729 = 631) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_10122_631 N (affineOrbit_mod729_eq_712_of_exponent_631 N hN)

theorem physical_happy_of_mod729_sixThreeOne
    (N : Nat) (hN : N % 729 = 631) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixThreeOne N hN)

theorem four_power_happy_propagates_of_next_mod729_sixThreeOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 631) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixThreeOne (K+1) hNext

private theorem affineOrbit_mod729_eq_662_of_exponent_632
    (N : Nat) (hN : N % 729 = 632) : affineOrbit N % 729 = 662 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 632).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `21102` forces `1 -> 3 -> 2 -> 2 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_21102_632
    (N : Nat) (hAmod : affineOrbit N % 729 = 662) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_sixThreeTwo (N : Nat) (hN : N % 729 = 632) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_21102_632 N (affineOrbit_mod729_eq_662_of_exponent_632 N hN)

theorem physical_happy_of_mod729_sixThreeTwo
    (N : Nat) (hN : N % 729 = 632) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixThreeTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_sixThreeTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 632) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixThreeTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_462_of_exponent_633
    (N : Nat) (hN : N % 729 = 633) : affineOrbit N % 729 = 462 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 633).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `0102` forces `1 -> 0 -> 1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_0102_633
    (N : Nat) (hAmod : affineOrbit N % 729 = 462) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixThreeThree (N : Nat) (hN : N % 729 = 633) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_0102_633 N (affineOrbit_mod729_eq_462_of_exponent_633 N hN)

theorem physical_happy_of_mod729_sixThreeThree
    (N : Nat) (hN : N % 729 = 633) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixThreeThree N hN)

theorem four_power_happy_propagates_of_next_mod729_sixThreeThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 633) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixThreeThree (K+1) hNext

private theorem affineOrbit_mod729_eq_107_of_exponent_635
    (N : Nat) (hN : N % 729 = 635) : affineOrbit N % 729 = 107 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 635).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` forces `1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_22_635
    (N : Nat) (hAmod : affineOrbit N % 729 = 107) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixThreeFive (N : Nat) (hN : N % 729 = 635) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_635 N (affineOrbit_mod729_eq_107_of_exponent_635 N hN)

theorem physical_happy_of_mod729_sixThreeFive
    (N : Nat) (hN : N % 729 = 635) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixThreeFive N hN)

theorem four_power_happy_propagates_of_next_mod729_sixThreeFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 635) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixThreeFive (K+1) hNext

private theorem affineOrbit_mod729_eq_429_of_exponent_636
    (N : Nat) (hN : N % 729 = 636) : affineOrbit N % 729 = 429 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 636).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` forces `1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_02_636
    (N : Nat) (hAmod : affineOrbit N % 729 = 429) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixThreeSix (N : Nat) (hN : N % 729 = 636) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_636 N (affineOrbit_mod729_eq_429_of_exponent_636 N hN)

theorem physical_happy_of_mod729_sixThreeSix
    (N : Nat) (hN : N % 729 = 636) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixThreeSix N hN)

theorem four_power_happy_propagates_of_next_mod729_sixThreeSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 636) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixThreeSix (K+1) hNext

end GSTFourPowerAffineSixthTrit631_636
