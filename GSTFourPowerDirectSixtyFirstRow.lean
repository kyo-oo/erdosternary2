import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSixtyFirstRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row61_reference :
    digit3 (4 ^ 57) 61 = 2 ∧ digit3 (4 ^ 58) 61 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod127173474825648610542883299603_57
    (N : Nat) (hN : N % 127173474825648610542883299603 = 57) : CommonTwo N := by
  have hPow : 3 ^ 61 = 127173474825648610542883299603 := by norm_num
  have hExp : N % 3 ^ 61 = 57 % 3 ^ 61 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (61 + 1) = 4 ^ 57 % 3 ^ (61 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 61 N 57).2 hExp
  have hd0 : digit3 (4 ^ N) 61 = 2 := by
    calc
      digit3 (4 ^ N) 61 = digit3 (4 ^ 57) 61 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row61_reference.1
  have hExp1 : (N + 1) % 3 ^ 61 = 58 % 3 ^ 61 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (61 + 1) = 4 ^ 58 % 3 ^ (61 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 61 (N + 1) 58).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 61 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 61 = digit3 (4 ^ 58) 61 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row61_reference.2
  exact ⟨61, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod127173474825648610542883299603_57
    (N : Nat) (hN : N % 127173474825648610542883299603 = 57) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod127173474825648610542883299603_57 N hN)

theorem four_power_happy_propagates_of_next_mod127173474825648610542883299603_57
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 127173474825648610542883299603 = 57) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod127173474825648610542883299603_57 (K + 1) hNext

#check commonTwo_of_mod127173474825648610542883299603_57
#check physical_happy_of_mod127173474825648610542883299603_57
#check four_power_happy_propagates_of_next_mod127173474825648610542883299603_57

end GSTFourPowerDirectSixtyFirstRow
