import GSTFourPowerAffineSixthTrit526_528

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit531_532

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_234_of_exponent_531
    (N : Nat) (hN : N % 729 = 531) :
    affineOrbit N % 729 = 234 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 531).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `002` (least-significant trit first) kills a hypothetical bad
channel: `1 -> 0 -> 0`, then trit `2` is impossible from state `0`. -/
private theorem commonTwo_of_mod729_pattern_002
    (N : Nat) (hAmod : affineOrbit N % 729 = 234) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveThreeOne
    (N : Nat) (hN : N % 729 = 531) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_002 N
    (affineOrbit_mod729_eq_234_of_exponent_531 N hN)

theorem physical_happy_of_mod729_fiveThreeOne
    (N : Nat) (hN : N % 729 = 531) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveThreeOne N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveThreeOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 531) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveThreeOne (K+1) hNext

private theorem affineOrbit_mod729_eq_208_of_exponent_532
    (N : Nat) (hN : N % 729 = 532) :
    affineOrbit N % 729 = 208 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 532).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `102` kills a hypothetical bad channel: `1 -> 1 -> 0`, then trit
`2` is impossible from state `0`. -/
private theorem commonTwo_of_mod729_pattern_102
    (N : Nat) (hAmod : affineOrbit N % 729 = 208) : CommonTwo N := by
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

theorem commonTwo_of_mod729_fiveThreeTwo
    (N : Nat) (hN : N % 729 = 532) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_102 N
    (affineOrbit_mod729_eq_208_of_exponent_532 N hN)

theorem physical_happy_of_mod729_fiveThreeTwo
    (N : Nat) (hN : N % 729 = 532) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveThreeTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveThreeTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 532) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveThreeTwo (K+1) hNext

#check commonTwo_of_mod729_fiveThreeOne
#check physical_happy_of_mod729_fiveThreeOne
#check four_power_happy_propagates_of_next_mod729_fiveThreeOne
#check commonTwo_of_mod729_fiveThreeTwo
#check physical_happy_of_mod729_fiveThreeTwo
#check four_power_happy_propagates_of_next_mod729_fiveThreeTwo
#print axioms commonTwo_of_mod729_fiveThreeOne
#print axioms physical_happy_of_mod729_fiveThreeOne
#print axioms four_power_happy_propagates_of_next_mod729_fiveThreeOne
#print axioms commonTwo_of_mod729_fiveThreeTwo
#print axioms physical_happy_of_mod729_fiveThreeTwo
#print axioms four_power_happy_propagates_of_next_mod729_fiveThreeTwo

end GSTFourPowerAffineSixthTrit531_532
