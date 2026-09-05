import GSTFourPowerAffineSixthTrit571_573

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit575_578

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_56_of_exponent_575
    (N : Nat) (hN : N % 729 = 575) :
    affineOrbit N % 729 = 56 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 575).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `2002` (least-significant trit first) forces
`1 -> 3 -> 1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_2002_575
    (N : Nat) (hAmod : affineOrbit N % 729 = 56) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
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
  rw [badChannel_zero_iff, hd3] at hbad3
  simpa using hbad3

theorem commonTwo_of_mod729_fiveSevenFive
    (N : Nat) (hN : N % 729 = 575) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_2002_575 N
    (affineOrbit_mod729_eq_56_of_exponent_575 N hN)

theorem physical_happy_of_mod729_fiveSevenFive
    (N : Nat) (hN : N % 729 = 575) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSevenFive N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSevenFive
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 575) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSevenFive (K+1) hNext

private theorem affineOrbit_mod729_eq_225_of_exponent_576
    (N : Nat) (hN : N % 729 = 576) :
    affineOrbit N % 729 = 225 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 576).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `00122` forces `1 -> 0 -> 0 -> 1 -> 3`,
then the final trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_00122_576
    (N : Nat) (hAmod : affineOrbit N % 729 = 225) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_fiveSevenSix
    (N : Nat) (hN : N % 729 = 576) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_00122_576 N
    (affineOrbit_mod729_eq_225_of_exponent_576 N hN)

theorem physical_happy_of_mod729_fiveSevenSix
    (N : Nat) (hN : N % 729 = 576) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSevenSix N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSevenSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 576) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSevenSix (K+1) hNext

private theorem affineOrbit_mod729_eq_172_of_exponent_577
    (N : Nat) (hN : N % 729 = 577) :
    affineOrbit N % 729 = 172 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 577).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `10102` forces `1 -> 1 -> 0 -> 1 -> 0`,
then the final trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_10102_577
    (N : Nat) (hAmod : affineOrbit N % 729 = 172) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_fiveSevenSeven
    (N : Nat) (hN : N % 729 = 577) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_10102_577 N
    (affineOrbit_mod729_eq_172_of_exponent_577 N hN)

theorem physical_happy_of_mod729_fiveSevenSeven
    (N : Nat) (hN : N % 729 = 577) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSevenSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSevenSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 577) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSevenSeven (K+1) hNext

private theorem affineOrbit_mod729_eq_689_of_exponent_578
    (N : Nat) (hN : N % 729 = 578) :
    affineOrbit N % 729 = 689 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 578).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `211122` forces `1 -> 3 -> 2 -> 2 -> 2 -> 3`,
then the sixth trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_211122_578
    (N : Nat) (hAmod : affineOrbit N % 729 = 689) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by
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
  have hbad3 : BadChannel 2 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_two_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_two_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_three_iff, hd5] at hbad5
  simpa using hbad5

theorem commonTwo_of_mod729_fiveSevenEight
    (N : Nat) (hN : N % 729 = 578) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_211122_578 N
    (affineOrbit_mod729_eq_689_of_exponent_578 N hN)

theorem physical_happy_of_mod729_fiveSevenEight
    (N : Nat) (hN : N % 729 = 578) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSevenEight N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSevenEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 578) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSevenEight (K+1) hNext

#check commonTwo_of_mod729_fiveSevenFive
#check physical_happy_of_mod729_fiveSevenFive
#check four_power_happy_propagates_of_next_mod729_fiveSevenFive
#check commonTwo_of_mod729_fiveSevenSix
#check physical_happy_of_mod729_fiveSevenSix
#check four_power_happy_propagates_of_next_mod729_fiveSevenSix
#check commonTwo_of_mod729_fiveSevenSeven
#check physical_happy_of_mod729_fiveSevenSeven
#check four_power_happy_propagates_of_next_mod729_fiveSevenSeven
#check commonTwo_of_mod729_fiveSevenEight
#check physical_happy_of_mod729_fiveSevenEight
#check four_power_happy_propagates_of_next_mod729_fiveSevenEight
#print axioms commonTwo_of_mod729_fiveSevenFive
#print axioms physical_happy_of_mod729_fiveSevenFive
#print axioms four_power_happy_propagates_of_next_mod729_fiveSevenFive
#print axioms commonTwo_of_mod729_fiveSevenSix
#print axioms physical_happy_of_mod729_fiveSevenSix
#print axioms four_power_happy_propagates_of_next_mod729_fiveSevenSix
#print axioms commonTwo_of_mod729_fiveSevenSeven
#print axioms physical_happy_of_mod729_fiveSevenSeven
#print axioms four_power_happy_propagates_of_next_mod729_fiveSevenSeven
#print axioms commonTwo_of_mod729_fiveSevenEight
#print axioms physical_happy_of_mod729_fiveSevenEight
#print axioms four_power_happy_propagates_of_next_mod729_fiveSevenEight

end GSTFourPowerAffineSixthTrit575_578
