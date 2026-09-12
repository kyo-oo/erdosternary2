import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectNinetyThirdRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row93_reference :
    digit3 (4 ^ 94) 93 = 2 ∧ digit3 (4 ^ 95) 93 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod235655016338368235499067731945871638181119123_94
    (N : Nat) (hN : N % 235655016338368235499067731945871638181119123 = 94) : CommonTwo N := by
  have hPow : 3 ^ 93 = 235655016338368235499067731945871638181119123 := by norm_num
  have hExp : N % 3 ^ 93 = 94 % 3 ^ 93 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (93 + 1) = 4 ^ 94 % 3 ^ (93 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 93 N 94).2 hExp
  have hd0 : digit3 (4 ^ N) 93 = 2 := by
    calc
      digit3 (4 ^ N) 93 = digit3 (4 ^ 94) 93 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row93_reference.1
  have hExp1 : (N + 1) % 3 ^ 93 = 95 % 3 ^ 93 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (93 + 1) = 4 ^ 95 % 3 ^ (93 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 93 (N + 1) 95).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 93 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 93 = digit3 (4 ^ 95) 93 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row93_reference.2
  exact ⟨93, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod235655016338368235499067731945871638181119123_94
    (N : Nat) (hN : N % 235655016338368235499067731945871638181119123 = 94) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod235655016338368235499067731945871638181119123_94 N hN)

theorem four_power_happy_propagates_of_next_mod235655016338368235499067731945871638181119123_94
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 235655016338368235499067731945871638181119123 = 94) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod235655016338368235499067731945871638181119123_94 (K + 1) hNext

#check commonTwo_of_mod235655016338368235499067731945871638181119123_94
#check physical_happy_of_mod235655016338368235499067731945871638181119123_94
#check four_power_happy_propagates_of_next_mod235655016338368235499067731945871638181119123_94

end GSTFourPowerDirectNinetyThirdRow
