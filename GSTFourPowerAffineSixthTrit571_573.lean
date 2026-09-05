import GSTFourPowerAffineSixthTrit562_565

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit571_573

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_652_of_exponent_571
    (N : Nat) (hN : N % 729 = 571) :
    affineOrbit N % 729 = 652 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 571).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `11002` (least-significant trit first) forces
`1 -> 1 -> 1 -> 0 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_11002_571
    (N : Nat) (hAmod : affineOrbit N % 729 = 652) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
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
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_fiveSevenOne
    (N : Nat) (hN : N % 729 = 571) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_11002_571 N
    (affineOrbit_mod729_eq_652_of_exponent_571 N hN)

theorem physical_happy_of_mod729_fiveSevenOne
    (N : Nat) (hN : N % 729 = 571) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSevenOne N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSevenOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 571) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSevenOne (K+1) hNext

private theorem affineOrbit_mod729_eq_422_of_exponent_572
    (N : Nat) (hN : N % 729 = 572) :
    affineOrbit N % 729 = 422 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 572).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` forces `1 -> 3`, then the second trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_22_572
    (N : Nat) (hAmod : affineOrbit N % 729 = 422) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveSevenTwo
    (N : Nat) (hN : N % 729 = 572) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_572 N
    (affineOrbit_mod729_eq_422_of_exponent_572 N hN)

theorem physical_happy_of_mod729_fiveSevenTwo
    (N : Nat) (hN : N % 729 = 572) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSevenTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSevenTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 572) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSevenTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_231_of_exponent_573
    (N : Nat) (hN : N % 729 = 573) :
    affineOrbit N % 729 = 231 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 573).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` forces `1 -> 0`, then the second trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_02_573
    (N : Nat) (hAmod : affineOrbit N % 729 = 231) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveSevenThree
    (N : Nat) (hN : N % 729 = 573) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_573 N
    (affineOrbit_mod729_eq_231_of_exponent_573 N hN)

theorem physical_happy_of_mod729_fiveSevenThree
    (N : Nat) (hN : N % 729 = 573) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveSevenThree N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveSevenThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 573) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveSevenThree (K+1) hNext

#check commonTwo_of_mod729_fiveSevenOne
#check physical_happy_of_mod729_fiveSevenOne
#check four_power_happy_propagates_of_next_mod729_fiveSevenOne
#check commonTwo_of_mod729_fiveSevenTwo
#check physical_happy_of_mod729_fiveSevenTwo
#check four_power_happy_propagates_of_next_mod729_fiveSevenTwo
#check commonTwo_of_mod729_fiveSevenThree
#check physical_happy_of_mod729_fiveSevenThree
#check four_power_happy_propagates_of_next_mod729_fiveSevenThree
#print axioms commonTwo_of_mod729_fiveSevenOne
#print axioms physical_happy_of_mod729_fiveSevenOne
#print axioms four_power_happy_propagates_of_next_mod729_fiveSevenOne
#print axioms commonTwo_of_mod729_fiveSevenTwo
#print axioms physical_happy_of_mod729_fiveSevenTwo
#print axioms four_power_happy_propagates_of_next_mod729_fiveSevenTwo
#print axioms commonTwo_of_mod729_fiveSevenThree
#print axioms physical_happy_of_mod729_fiveSevenThree
#print axioms four_power_happy_propagates_of_next_mod729_fiveSevenThree

end GSTFourPowerAffineSixthTrit571_573
