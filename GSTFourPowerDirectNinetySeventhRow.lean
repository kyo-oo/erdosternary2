import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectNinetySeventhRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row97_reference :
    digit3 (4 ^ 98) 97 = 2 ∧ digit3 (4 ^ 99) 97 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod19088056323407827075424486287615602692670648963_98
    (N : Nat) (hN : N % 19088056323407827075424486287615602692670648963 = 98) : CommonTwo N := by
  have hPow : 3 ^ 97 = 19088056323407827075424486287615602692670648963 := by norm_num
  have hExp : N % 3 ^ 97 = 98 % 3 ^ 97 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (97 + 1) = 4 ^ 98 % 3 ^ (97 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 97 N 98).2 hExp
  have hd0 : digit3 (4 ^ N) 97 = 2 := by
    calc
      digit3 (4 ^ N) 97 = digit3 (4 ^ 98) 97 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row97_reference.1
  have hExp1 : (N + 1) % 3 ^ 97 = 99 % 3 ^ 97 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (97 + 1) = 4 ^ 99 % 3 ^ (97 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 97 (N + 1) 99).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 97 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 97 = digit3 (4 ^ 99) 97 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row97_reference.2
  exact ⟨97, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod19088056323407827075424486287615602692670648963_98
    (N : Nat) (hN : N % 19088056323407827075424486287615602692670648963 = 98) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod19088056323407827075424486287615602692670648963_98 N hN)

theorem four_power_happy_propagates_of_next_mod19088056323407827075424486287615602692670648963_98
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 19088056323407827075424486287615602692670648963 = 98) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod19088056323407827075424486287615602692670648963_98 (K + 1) hNext

#check commonTwo_of_mod19088056323407827075424486287615602692670648963_98
#check physical_happy_of_mod19088056323407827075424486287615602692670648963_98
#check four_power_happy_propagates_of_next_mod19088056323407827075424486287615602692670648963_98

end GSTFourPowerDirectNinetySeventhRow
