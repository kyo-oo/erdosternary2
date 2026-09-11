import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSixtyEighthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row68_reference :
    digit3 (4 ^ 69) 68 = 2 ∧ digit3 (4 ^ 70) 68 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod278128389443693511257285776231761_69
    (N : Nat) (hN : N % 278128389443693511257285776231761 = 69) : CommonTwo N := by
  have hPow : 3 ^ 68 = 278128389443693511257285776231761 := by norm_num
  have hExp : N % 3 ^ 68 = 69 % 3 ^ 68 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (68 + 1) = 4 ^ 69 % 3 ^ (68 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 68 N 69).2 hExp
  have hd0 : digit3 (4 ^ N) 68 = 2 := by
    calc
      digit3 (4 ^ N) 68 = digit3 (4 ^ 69) 68 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row68_reference.1
  have hExp1 : (N + 1) % 3 ^ 68 = 70 % 3 ^ 68 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (68 + 1) = 4 ^ 70 % 3 ^ (68 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 68 (N + 1) 70).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 68 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 68 = digit3 (4 ^ 70) 68 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row68_reference.2
  exact ⟨68, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod278128389443693511257285776231761_69
    (N : Nat) (hN : N % 278128389443693511257285776231761 = 69) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod278128389443693511257285776231761_69 N hN)

theorem four_power_happy_propagates_of_next_mod278128389443693511257285776231761_69
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 278128389443693511257285776231761 = 69) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod278128389443693511257285776231761_69 (K + 1) hNext

#check commonTwo_of_mod278128389443693511257285776231761_69
#check physical_happy_of_mod278128389443693511257285776231761_69
#check four_power_happy_propagates_of_next_mod278128389443693511257285776231761_69

end GSTFourPowerDirectSixtyEighthRow
