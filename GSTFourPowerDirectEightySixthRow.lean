import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectEightySixthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row86_reference :
    digit3 (4 ^ 87) 86 = 2 ∧ digit3 (4 ^ 88) 86 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod107752636643058178097424660240453423951129_87
    (N : Nat) (hN : N % 107752636643058178097424660240453423951129 = 87) : CommonTwo N := by
  have hPow : 3 ^ 86 = 107752636643058178097424660240453423951129 := by norm_num
  have hExp : N % 3 ^ 86 = 87 % 3 ^ 86 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (86 + 1) = 4 ^ 87 % 3 ^ (86 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 86 N 87).2 hExp
  have hd0 : digit3 (4 ^ N) 86 = 2 := by
    calc
      digit3 (4 ^ N) 86 = digit3 (4 ^ 87) 86 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row86_reference.1
  have hExp1 : (N + 1) % 3 ^ 86 = 88 % 3 ^ 86 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (86 + 1) = 4 ^ 88 % 3 ^ (86 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 86 (N + 1) 88).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 86 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 86 = digit3 (4 ^ 88) 86 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row86_reference.2
  exact ⟨86, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod107752636643058178097424660240453423951129_87
    (N : Nat) (hN : N % 107752636643058178097424660240453423951129 = 87) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod107752636643058178097424660240453423951129_87 N hN)

theorem four_power_happy_propagates_of_next_mod107752636643058178097424660240453423951129_87
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 107752636643058178097424660240453423951129 = 87) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod107752636643058178097424660240453423951129_87 (K + 1) hNext

#check commonTwo_of_mod107752636643058178097424660240453423951129_87
#check physical_happy_of_mod107752636643058178097424660240453423951129_87
#check four_power_happy_propagates_of_next_mod107752636643058178097424660240453423951129_87

end GSTFourPowerDirectEightySixthRow
