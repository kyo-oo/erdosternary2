import GSTFourPowerAffineSixthTrit556_559

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit562_565

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_724_of_exponent_562
    (N : Nat) (hN : N % 729 = 562) :
    affineOrbit N % 729 = 724 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 562).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `1122` (least-significant trit first) forces
`1 -> 1 -> 1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_1122_562
    (N : Nat) (hAmod : affineOrbit N % 729 = 724) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveSixTwo
    (N : Nat) (hN : N % 729 = 562) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_1122_562 N
    (affineOrbit_mod729_eq_724_of_exponent_562 N hN)

theorem physical_happy_of_mod729_fiveSixTwo
    (N : Nat) (hN : N % 729 = 562) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSixTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSixTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 562) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSixTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_710_of_exponent_563
    (N : Nat) (hN : N % 729 = 563) :
    affineOrbit N % 729 = 710 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 563).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` forces `1 -> 3`, then the second trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_22_563
    (N : Nat) (hAmod : affineOrbit N % 729 = 710) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveSixThree
    (N : Nat) (hN : N % 729 = 563) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_563 N
    (affineOrbit_mod729_eq_710_of_exponent_563 N hN)

theorem physical_happy_of_mod729_fiveSixThree
    (N : Nat) (hN : N % 729 = 563) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSixThree N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSixThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 563) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSixThree (K+1) hNext

private theorem affineOrbit_mod729_eq_654_of_exponent_564
    (N : Nat) (hN : N % 729 = 564) :
    affineOrbit N % 729 = 654 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 564).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` forces `1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_02_564
    (N : Nat) (hAmod : affineOrbit N % 729 = 654) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveSixFour
    (N : Nat) (hN : N % 729 = 564) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_564 N
    (affineOrbit_mod729_eq_654_of_exponent_564 N hN)

theorem physical_happy_of_mod729_fiveSixFour
    (N : Nat) (hN : N % 729 = 564) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSixFour N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSixFour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 564) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSixFour (K+1) hNext

private theorem affineOrbit_mod729_eq_430_of_exponent_565
    (N : Nat) (hN : N % 729 = 565) :
    affineOrbit N % 729 = 430 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 565).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `122` forces `1 -> 1 -> 3`, then the final trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_122_565
    (N : Nat) (hAmod : affineOrbit N % 729 = 430) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveSixFive
    (N : Nat) (hN : N % 729 = 565) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_122_565 N
    (affineOrbit_mod729_eq_430_of_exponent_565 N hN)

theorem physical_happy_of_mod729_fiveSixFive
    (N : Nat) (hN : N % 729 = 565) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSixFive N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSixFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 565) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSixFive (K+1) hNext

#check commonTwo_of_mod729_fiveSixTwo
#check physical_happy_of_mod729_fiveSixTwo
#check four_power_happy_propagates_of_next_mod729_fiveSixTwo
#check commonTwo_of_mod729_fiveSixThree
#check physical_happy_of_mod729_fiveSixThree
#check four_power_happy_propagates_of_next_mod729_fiveSixThree
#check commonTwo_of_mod729_fiveSixFour
#check physical_happy_of_mod729_fiveSixFour
#check four_power_happy_propagates_of_next_mod729_fiveSixFour
#check commonTwo_of_mod729_fiveSixFive
#check physical_happy_of_mod729_fiveSixFive
#check four_power_happy_propagates_of_next_mod729_fiveSixFive
#print axioms commonTwo_of_mod729_fiveSixTwo
#print axioms physical_happy_of_mod729_fiveSixTwo
#print axioms four_power_happy_propagates_of_next_mod729_fiveSixTwo
#print axioms commonTwo_of_mod729_fiveSixThree
#print axioms physical_happy_of_mod729_fiveSixThree
#print axioms four_power_happy_propagates_of_next_mod729_fiveSixThree
#print axioms commonTwo_of_mod729_fiveSixFour
#print axioms physical_happy_of_mod729_fiveSixFour
#print axioms four_power_happy_propagates_of_next_mod729_fiveSixFour
#print axioms commonTwo_of_mod729_fiveSixFive
#print axioms physical_happy_of_mod729_fiveSixFive
#print axioms four_power_happy_propagates_of_next_mod729_fiveSixFive

end GSTFourPowerAffineSixthTrit562_565
