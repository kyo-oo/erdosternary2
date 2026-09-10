import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectFiftyNinthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row59_reference :
    digit3 (4 ^ 58) 59 = 2 ∧ digit3 (4 ^ 59) 59 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod14130386091738734504764811067_58
    (N : Nat) (hN : N % 14130386091738734504764811067 = 58) : CommonTwo N := by
  have hPow : 3 ^ 59 = 14130386091738734504764811067 := by norm_num
  have hExp : N % 3 ^ 59 = 58 % 3 ^ 59 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (59 + 1) = 4 ^ 58 % 3 ^ (59 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 59 N 58).2 hExp
  have hd0 : digit3 (4 ^ N) 59 = 2 := by
    calc
      digit3 (4 ^ N) 59 = digit3 (4 ^ 58) 59 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row59_reference.1
  have hExp1 : (N + 1) % 3 ^ 59 = 59 % 3 ^ 59 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (59 + 1) = 4 ^ 59 % 3 ^ (59 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 59 (N + 1) 59).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 59 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 59 = digit3 (4 ^ 59) 59 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row59_reference.2
  exact ⟨59, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod14130386091738734504764811067_58
    (N : Nat) (hN : N % 14130386091738734504764811067 = 58) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod14130386091738734504764811067_58 N hN)

theorem four_power_happy_propagates_of_next_mod14130386091738734504764811067_58
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 14130386091738734504764811067 = 58) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod14130386091738734504764811067_58 (K + 1) hNext

#check commonTwo_of_mod14130386091738734504764811067_58
#check physical_happy_of_mod14130386091738734504764811067_58
#check four_power_happy_propagates_of_next_mod14130386091738734504764811067_58

end GSTFourPowerDirectFiftyNinthRow
