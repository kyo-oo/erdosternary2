import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSeventyFourthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row74_reference :
    digit3 (4 ^ 61) 74 = 2 ∧ digit3 (4 ^ 62) 74 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod202755595904452569706561330872953769_61
    (N : Nat) (hN : N % 202755595904452569706561330872953769 = 61) : CommonTwo N := by
  have hPow : 3 ^ 74 = 202755595904452569706561330872953769 := by norm_num
  have hExp : N % 3 ^ 74 = 61 % 3 ^ 74 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (74 + 1) = 4 ^ 61 % 3 ^ (74 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 74 N 61).2 hExp
  have hd0 : digit3 (4 ^ N) 74 = 2 := by
    calc
      digit3 (4 ^ N) 74 = digit3 (4 ^ 61) 74 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row74_reference.1
  have hExp1 : (N + 1) % 3 ^ 74 = 62 % 3 ^ 74 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (74 + 1) = 4 ^ 62 % 3 ^ (74 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 74 (N + 1) 62).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 74 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 74 = digit3 (4 ^ 62) 74 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row74_reference.2
  exact ⟨74, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod202755595904452569706561330872953769_61
    (N : Nat) (hN : N % 202755595904452569706561330872953769 = 61) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod202755595904452569706561330872953769_61 N hN)

theorem four_power_happy_propagates_of_next_mod202755595904452569706561330872953769_61
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 202755595904452569706561330872953769 = 61) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod202755595904452569706561330872953769_61 (K + 1) hNext

#check commonTwo_of_mod202755595904452569706561330872953769_61
#check physical_happy_of_mod202755595904452569706561330872953769_61
#check four_power_happy_propagates_of_next_mod202755595904452569706561330872953769_61

end GSTFourPowerDirectSeventyFourthRow
