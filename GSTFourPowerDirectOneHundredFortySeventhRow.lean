import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredFortySeventhRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row147_reference :
    digit3 (4 ^ 148) 147 = 2 ∧ digit3 (4 ^ 149) 147 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod13703277223523221219433362313025801636536040755174924956117940937101787_148
    (N : Nat) (hN : N % 13703277223523221219433362313025801636536040755174924956117940937101787 = 148) : CommonTwo N := by
  have hPow : 3 ^ 147 = 13703277223523221219433362313025801636536040755174924956117940937101787 := by norm_num
  have hExp : N % 3 ^ 147 = 148 % 3 ^ 147 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (147 + 1) = 4 ^ 148 % 3 ^ (147 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 147 N 148).2 hExp
  have hd0 : digit3 (4 ^ N) 147 = 2 := by
    calc
      digit3 (4 ^ N) 147 = digit3 (4 ^ 148) 147 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row147_reference.1
  have hExp1 : (N + 1) % 3 ^ 147 = 149 % 3 ^ 147 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (147 + 1) = 4 ^ 149 % 3 ^ (147 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 147 (N + 1) 149).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 147 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 147 = digit3 (4 ^ 149) 147 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row147_reference.2
  exact ⟨147, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod13703277223523221219433362313025801636536040755174924956117940937101787_148
    (N : Nat) (hN : N % 13703277223523221219433362313025801636536040755174924956117940937101787 = 148) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod13703277223523221219433362313025801636536040755174924956117940937101787_148 N hN)

theorem four_power_happy_propagates_of_next_mod13703277223523221219433362313025801636536040755174924956117940937101787_148
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 13703277223523221219433362313025801636536040755174924956117940937101787 = 148) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod13703277223523221219433362313025801636536040755174924956117940937101787_148 (K + 1) hNext

#check commonTwo_of_mod13703277223523221219433362313025801636536040755174924956117940937101787_148
#check physical_happy_of_mod13703277223523221219433362313025801636536040755174924956117940937101787_148
#check four_power_happy_propagates_of_next_mod13703277223523221219433362313025801636536040755174924956117940937101787_148

end GSTFourPowerDirectOneHundredFortySeventhRow
