import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectTwoHundredNineteenthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row219_reference :
    digit3 (4 ^ 220) 219 = 2 ∧ digit3 (4 ^ 221) 219 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467_220
    (N : Nat) (hN : N % 308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467 = 220) : CommonTwo N := by
  have hPow : 3 ^ 219 = 308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467 := by norm_num
  have hExp : N % 3 ^ 219 = 220 % 3 ^ 219 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (219 + 1) = 4 ^ 220 % 3 ^ (219 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 219 N 220).2 hExp
  have hd0 : digit3 (4 ^ N) 219 = 2 := by
    calc
      digit3 (4 ^ N) 219 = digit3 (4 ^ 220) 219 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row219_reference.1
  have hExp1 : (N + 1) % 3 ^ 219 = 221 % 3 ^ 219 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (219 + 1) = 4 ^ 221 % 3 ^ (219 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 219 (N + 1) 221).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 219 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 219 = digit3 (4 ^ 221) 219 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row219_reference.2
  exact ⟨219, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467_220
    (N : Nat) (hN : N % 308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467 = 220) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467_220 N hN)

theorem four_power_happy_propagates_of_next_mod308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467_220
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467 = 220) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467_220 (K + 1) hNext

#check commonTwo_of_mod308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467_220
#check physical_happy_of_mod308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467_220
#check four_power_happy_propagates_of_next_mod308712904366595890319978599341504655567257431166409329421135089732346509723631627417356013073234099809467_220

end GSTFourPowerDirectTwoHundredNineteenthRow
