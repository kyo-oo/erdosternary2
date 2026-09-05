import GSTFourPowerAffineSixthTrit665_668

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit671_673

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_170_of_exponent_671
    (N : Nat) (hN : N % 729 = 671) : affineOrbit N % 729 = 170 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 671).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_22_671
    (N : Nat) (hAmod : affineOrbit N % 729 = 170) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixSevenOne (N : Nat) (hN : N % 729 = 671) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_671 N (affineOrbit_mod729_eq_170_of_exponent_671 N hN)

theorem physical_happy_of_mod729_sixSevenOne
    (N : Nat) (hN : N % 729 = 671) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixSevenOne N hN)

theorem four_power_happy_propagates_of_next_mod729_sixSevenOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 671) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixSevenOne (K+1) hNext

private theorem affineOrbit_mod729_eq_681_of_exponent_672
    (N : Nat) (hN : N % 729 = 672) : affineOrbit N % 729 = 681 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 672).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_02_672
    (N : Nat) (hAmod : affineOrbit N % 729 = 681) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixSevenTwo (N : Nat) (hN : N % 729 = 672) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_672 N (affineOrbit_mod729_eq_681_of_exponent_672 N hN)

theorem physical_happy_of_mod729_sixSevenTwo
    (N : Nat) (hN : N % 729 = 672) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixSevenTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_sixSevenTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 672) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixSevenTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_538_of_exponent_673
    (N : Nat) (hN : N % 729 = 673) : affineOrbit N % 729 = 538 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 673).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod729_pattern_122_673
    (N : Nat) (hAmod : affineOrbit N % 729 = 538) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixSevenThree (N : Nat) (hN : N % 729 = 673) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_122_673 N (affineOrbit_mod729_eq_538_of_exponent_673 N hN)

theorem physical_happy_of_mod729_sixSevenThree
    (N : Nat) (hN : N % 729 = 673) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod729_sixSevenThree N hN)

theorem four_power_happy_propagates_of_next_mod729_sixSevenThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 673) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixSevenThree (K+1) hNext

#check commonTwo_of_mod729_sixSevenOne
#check physical_happy_of_mod729_sixSevenOne
#check four_power_happy_propagates_of_next_mod729_sixSevenOne
#check commonTwo_of_mod729_sixSevenTwo
#check physical_happy_of_mod729_sixSevenTwo
#check four_power_happy_propagates_of_next_mod729_sixSevenTwo
#check commonTwo_of_mod729_sixSevenThree
#check physical_happy_of_mod729_sixSevenThree
#check four_power_happy_propagates_of_next_mod729_sixSevenThree
#print axioms physical_happy_of_mod729_sixSevenOne
#print axioms physical_happy_of_mod729_sixSevenTwo
#print axioms physical_happy_of_mod729_sixSevenThree

end GSTFourPowerAffineSixthTrit671_673
