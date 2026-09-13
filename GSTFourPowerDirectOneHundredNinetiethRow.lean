import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredNinetiethRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row190_reference :
    digit3 (4 ^ 191) 190 = 2 ∧ digit3 (4 ^ 192) 190 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449_191
    (N : Nat) (hN : N % 4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449 = 191) : CommonTwo N := by
  have hPow : 3 ^ 190 = 4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449 := by norm_num
  have hExp : N % 3 ^ 190 = 191 % 3 ^ 190 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (190 + 1) = 4 ^ 191 % 3 ^ (190 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 190 N 191).2 hExp
  have hd0 : digit3 (4 ^ N) 190 = 2 := by
    calc
      digit3 (4 ^ N) 190 = digit3 (4 ^ 191) 190 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row190_reference.1
  have hExp1 : (N + 1) % 3 ^ 190 = 192 % 3 ^ 190 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (190 + 1) = 4 ^ 192 % 3 ^ (190 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 190 (N + 1) 192).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 190 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 190 = digit3 (4 ^ 192) 190 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row190_reference.2
  exact ⟨190, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449_191
    (N : Nat) (hN : N % 4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449 = 191) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449_191 N hN)

theorem four_power_happy_propagates_of_next_mod4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449_191
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449 = 191) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449_191 (K + 1) hNext

#check commonTwo_of_mod4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449_191
#check physical_happy_of_mod4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449_191
#check four_power_happy_propagates_of_next_mod4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449_191

end GSTFourPowerDirectOneHundredNinetiethRow
