import GSTFourPowerAffineSixthTrit525

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit526_528

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_526_of_exponent_526
    (N : Nat) (hN : N % 729 = 526) :
    affineOrbit N % 729 = 526 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 526).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Sixth-trit kill pattern `111102` (least-significant trit first).
A hypothetical bad channel follows `1 -> 1 -> 1 -> 1 -> 1 -> 0`,
then the terminal trit `2` is impossible from state `0`. -/
private theorem commonTwo_of_mod729_pattern_111102
    (N : Nat) (hAmod : affineOrbit N % 729 = 526) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_zero_iff, hd5] at hbad5
  simpa using hbad5

theorem commonTwo_of_mod729_fiveTwoSix
    (N : Nat) (hN : N % 729 = 526) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_111102 N
    (affineOrbit_mod729_eq_526_of_exponent_526 N hN)

theorem physical_happy_of_mod729_fiveTwoSix
    (N : Nat) (hN : N % 729 = 526) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveTwoSix N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveTwoSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 526) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveTwoSix (K+1) hNext

private theorem affineOrbit_mod729_eq_647_of_exponent_527
    (N : Nat) (hN : N % 729 = 527) :
    affineOrbit N % 729 = 647 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 527).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` already kills a hypothetical bad channel: state `1` on trit `2`
moves to state `3`, where the next trit `2` is immediate success. -/
private theorem commonTwo_of_mod729_pattern_22
    (N : Nat) (hAmod : affineOrbit N % 729 = 647) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveTwoSeven
    (N : Nat) (hN : N % 729 = 527) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22 N
    (affineOrbit_mod729_eq_647_of_exponent_527 N hN)

theorem physical_happy_of_mod729_fiveTwoSeven
    (N : Nat) (hN : N % 729 = 527) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveTwoSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveTwoSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 527) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveTwoSeven (K+1) hNext

private theorem affineOrbit_mod729_eq_402_of_exponent_528
    (N : Nat) (hN : N % 729 = 528) :
    affineOrbit N % 729 = 402 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 528).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` kills the bad channel: state `1` on trit `0` moves to state `0`,
where trit `2` is immediate success. -/
private theorem commonTwo_of_mod729_pattern_02
    (N : Nat) (hAmod : affineOrbit N % 729 = 402) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveTwoEight
    (N : Nat) (hN : N % 729 = 528) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02 N
    (affineOrbit_mod729_eq_402_of_exponent_528 N hN)

theorem physical_happy_of_mod729_fiveTwoEight
    (N : Nat) (hN : N % 729 = 528) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveTwoEight N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveTwoEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 528) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveTwoEight (K+1) hNext

#check commonTwo_of_mod729_fiveTwoSix
#check physical_happy_of_mod729_fiveTwoSix
#check four_power_happy_propagates_of_next_mod729_fiveTwoSix
#check commonTwo_of_mod729_fiveTwoSeven
#check physical_happy_of_mod729_fiveTwoSeven
#check four_power_happy_propagates_of_next_mod729_fiveTwoSeven
#check commonTwo_of_mod729_fiveTwoEight
#check physical_happy_of_mod729_fiveTwoEight
#check four_power_happy_propagates_of_next_mod729_fiveTwoEight
#print axioms commonTwo_of_mod729_fiveTwoSix
#print axioms physical_happy_of_mod729_fiveTwoSix
#print axioms four_power_happy_propagates_of_next_mod729_fiveTwoSix
#print axioms commonTwo_of_mod729_fiveTwoSeven
#print axioms physical_happy_of_mod729_fiveTwoSeven
#print axioms four_power_happy_propagates_of_next_mod729_fiveTwoSeven
#print axioms commonTwo_of_mod729_fiveTwoEight
#print axioms physical_happy_of_mod729_fiveTwoEight
#print axioms four_power_happy_propagates_of_next_mod729_fiveTwoEight

end GSTFourPowerAffineSixthTrit526_528
