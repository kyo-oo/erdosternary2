import GSTFourPowerAffineSixthTrit554_555

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit556_559

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_178_of_exponent_556
    (N : Nat) (hN : N % 729 = 556) :
    affineOrbit N % 729 = 178 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 556).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `12102` (least-significant trit first) forces
`1 -> 1 -> 3 -> 2 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_12102_556
    (N : Nat) (hAmod : affineOrbit N % 729 = 178) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 2 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_three_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_fiveFiveSix
    (N : Nat) (hN : N % 729 = 556) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_12102_556 N
    (affineOrbit_mod729_eq_178_of_exponent_556 N hN)

theorem physical_happy_of_mod729_fiveFiveSix
    (N : Nat) (hN : N % 729 = 556) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveFiveSix N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveFiveSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 556) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFiveSix (K+1) hNext

private theorem affineOrbit_mod729_eq_713_of_exponent_557
    (N : Nat) (hN : N % 729 = 557) :
    affineOrbit N % 729 = 713 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 557).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `20122` forces `1 -> 3 -> 1 -> 1 -> 3`, then the final trit `2`
kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_20122_557
    (N : Nat) (hAmod : affineOrbit N % 729 = 713) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_fiveFiveSeven
    (N : Nat) (hN : N % 729 = 557) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_20122_557 N
    (affineOrbit_mod729_eq_713_of_exponent_557 N hN)

theorem physical_happy_of_mod729_fiveFiveSeven
    (N : Nat) (hN : N % 729 = 557) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveFiveSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveFiveSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 557) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFiveSeven (K+1) hNext

private theorem affineOrbit_mod729_eq_666_of_exponent_558
    (N : Nat) (hN : N % 729 = 558) :
    affineOrbit N % 729 = 666 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 558).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `002` forces `1 -> 0 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_002_558
    (N : Nat) (hAmod : affineOrbit N % 729 = 666) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveFiveEight
    (N : Nat) (hN : N % 729 = 558) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_002_558 N
    (affineOrbit_mod729_eq_666_of_exponent_558 N hN)

theorem physical_happy_of_mod729_fiveFiveEight
    (N : Nat) (hN : N % 729 = 558) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveFiveEight N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveFiveEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 558) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFiveEight (K+1) hNext

private theorem affineOrbit_mod729_eq_478_of_exponent_559
    (N : Nat) (hN : N % 729 = 559) :
    affineOrbit N % 729 = 478 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 559).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `102` forces `1 -> 1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_102_559
    (N : Nat) (hAmod : affineOrbit N % 729 = 478) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveFiveNine
    (N : Nat) (hN : N % 729 = 559) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_102_559 N
    (affineOrbit_mod729_eq_478_of_exponent_559 N hN)

theorem physical_happy_of_mod729_fiveFiveNine
    (N : Nat) (hN : N % 729 = 559) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveFiveNine N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveFiveNine
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 559) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveFiveNine (K+1) hNext

#check commonTwo_of_mod729_fiveFiveSix
#check physical_happy_of_mod729_fiveFiveSix
#check four_power_happy_propagates_of_next_mod729_fiveFiveSix
#check commonTwo_of_mod729_fiveFiveSeven
#check physical_happy_of_mod729_fiveFiveSeven
#check four_power_happy_propagates_of_next_mod729_fiveFiveSeven
#check commonTwo_of_mod729_fiveFiveEight
#check physical_happy_of_mod729_fiveFiveEight
#check four_power_happy_propagates_of_next_mod729_fiveFiveEight
#check commonTwo_of_mod729_fiveFiveNine
#check physical_happy_of_mod729_fiveFiveNine
#check four_power_happy_propagates_of_next_mod729_fiveFiveNine
#print axioms commonTwo_of_mod729_fiveFiveSix
#print axioms physical_happy_of_mod729_fiveFiveSix
#print axioms four_power_happy_propagates_of_next_mod729_fiveFiveSix
#print axioms commonTwo_of_mod729_fiveFiveSeven
#print axioms physical_happy_of_mod729_fiveFiveSeven
#print axioms four_power_happy_propagates_of_next_mod729_fiveFiveSeven
#print axioms commonTwo_of_mod729_fiveFiveEight
#print axioms physical_happy_of_mod729_fiveFiveEight
#print axioms four_power_happy_propagates_of_next_mod729_fiveFiveEight
#print axioms commonTwo_of_mod729_fiveFiveNine
#print axioms physical_happy_of_mod729_fiveFiveNine
#print axioms four_power_happy_propagates_of_next_mod729_fiveFiveNine

end GSTFourPowerAffineSixthTrit556_559
