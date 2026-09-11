import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSeventyThirdRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row73_reference :
    digit3 (4 ^ 76) 73 = 2 ∧ digit3 (4 ^ 77) 73 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod67585198634817523235520443624317923_76
    (N : Nat) (hN : N % 67585198634817523235520443624317923 = 76) : CommonTwo N := by
  have hPow : 3 ^ 73 = 67585198634817523235520443624317923 := by norm_num
  have hExp : N % 3 ^ 73 = 76 % 3 ^ 73 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (73 + 1) = 4 ^ 76 % 3 ^ (73 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 73 N 76).2 hExp
  have hd0 : digit3 (4 ^ N) 73 = 2 := by
    calc
      digit3 (4 ^ N) 73 = digit3 (4 ^ 76) 73 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row73_reference.1
  have hExp1 : (N + 1) % 3 ^ 73 = 77 % 3 ^ 73 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (73 + 1) = 4 ^ 77 % 3 ^ (73 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 73 (N + 1) 77).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 73 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 73 = digit3 (4 ^ 77) 73 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row73_reference.2
  exact ⟨73, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod67585198634817523235520443624317923_76
    (N : Nat) (hN : N % 67585198634817523235520443624317923 = 76) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod67585198634817523235520443624317923_76 N hN)

theorem four_power_happy_propagates_of_next_mod67585198634817523235520443624317923_76
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 67585198634817523235520443624317923 = 76) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod67585198634817523235520443624317923_76 (K + 1) hNext

#check commonTwo_of_mod67585198634817523235520443624317923_76
#check physical_happy_of_mod67585198634817523235520443624317923_76
#check four_power_happy_propagates_of_next_mod67585198634817523235520443624317923_76

end GSTFourPowerDirectSeventyThirdRow
