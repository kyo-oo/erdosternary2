import GSTFourPowerAffineSixthTrit531_532

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit536_538

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_116_of_exponent_536
    (N : Nat) (hN : N % 729 = 536) :
    affineOrbit N % 729 = 116 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 536).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` (least-significant trit first) kills a hypothetical bad
channel: `1 -> 3`, then trit `2` is impossible from state `3`. -/
private theorem commonTwo_of_mod729_pattern_22
    (N : Nat) (hAmod : affineOrbit N % 729 = 116) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveThreeSix
    (N : Nat) (hN : N % 729 = 536) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22 N
    (affineOrbit_mod729_eq_116_of_exponent_536 N hN)

theorem physical_happy_of_mod729_fiveThreeSix
    (N : Nat) (hN : N % 729 = 536) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveThreeSix N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveThreeSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 536) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveThreeSix (K+1) hNext

private theorem affineOrbit_mod729_eq_465_of_exponent_537
    (N : Nat) (hN : N % 729 = 537) :
    affineOrbit N % 729 = 465 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 537).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` kills a hypothetical bad channel: `1 -> 0`, then trit `2`
is impossible from state `0`. -/
private theorem commonTwo_of_mod729_pattern_02
    (N : Nat) (hAmod : affineOrbit N % 729 = 465) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveThreeSeven
    (N : Nat) (hN : N % 729 = 537) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02 N
    (affineOrbit_mod729_eq_465_of_exponent_537 N hN)

theorem physical_happy_of_mod729_fiveThreeSeven
    (N : Nat) (hN : N % 729 = 537) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveThreeSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveThreeSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 537) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveThreeSeven (K+1) hNext

private theorem affineOrbit_mod729_eq_403_of_exponent_538
    (N : Nat) (hN : N % 729 = 538) :
    affineOrbit N % 729 = 403 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 538).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `122` kills a hypothetical bad channel: `1 -> 1 -> 3`, then trit
`2` is impossible from state `3`. -/
private theorem commonTwo_of_mod729_pattern_122
    (N : Nat) (hAmod : affineOrbit N % 729 = 403) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveThreeEight
    (N : Nat) (hN : N % 729 = 538) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_122 N
    (affineOrbit_mod729_eq_403_of_exponent_538 N hN)

theorem physical_happy_of_mod729_fiveThreeEight
    (N : Nat) (hN : N % 729 = 538) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveThreeEight N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveThreeEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 538) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveThreeEight (K+1) hNext

#check commonTwo_of_mod729_fiveThreeSix
#check physical_happy_of_mod729_fiveThreeSix
#check four_power_happy_propagates_of_next_mod729_fiveThreeSix
#check commonTwo_of_mod729_fiveThreeSeven
#check physical_happy_of_mod729_fiveThreeSeven
#check four_power_happy_propagates_of_next_mod729_fiveThreeSeven
#check commonTwo_of_mod729_fiveThreeEight
#check physical_happy_of_mod729_fiveThreeEight
#check four_power_happy_propagates_of_next_mod729_fiveThreeEight
#print axioms commonTwo_of_mod729_fiveThreeSix
#print axioms physical_happy_of_mod729_fiveThreeSix
#print axioms four_power_happy_propagates_of_next_mod729_fiveThreeSix
#print axioms commonTwo_of_mod729_fiveThreeSeven
#print axioms physical_happy_of_mod729_fiveThreeSeven
#print axioms four_power_happy_propagates_of_next_mod729_fiveThreeSeven
#print axioms commonTwo_of_mod729_fiveThreeEight
#print axioms physical_happy_of_mod729_fiveThreeEight
#print axioms four_power_happy_propagates_of_next_mod729_fiveThreeEight

end GSTFourPowerAffineSixthTrit536_538
